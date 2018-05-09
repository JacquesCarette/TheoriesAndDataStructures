\section{Structures.Multiset-Bleeding}

New experimental variation on |Structures.Multiset-Bleeding| but using sets rather than setoids.

%{{{ Precisé

\begin{enumerate}

\item |IsCtrEquivalence 𝒞| is a proof that data-type constructor |𝒞| endows types with equivalence relations. We show how lists with bag equality are such an instance: |Bag-isCtrEquivalence|.

\item |CommutativeContainer| is a essentially a tuple |(𝒞, ø, _⊕_)| consisting of a container equivalence |𝒞|
      along with an “empty container” |ø| and a “container union” |_⊕_| operation such that the type
      transformer |𝒞| endows types with a commutative monoid structure.

      We relise that bags, implemented as lists with usual catenation, are such an instance:
      |Bag-CommutativeContainer|.

\item |Multiset| is a type transformer furnishing a (setoid) carrier type with a commutative container
      transformer |𝒞|, a way to embed the carrier into into its associated container (|singleton|),
      a polymoprhic operation, “fold”, that reifies commutative container values (terms)
      as values in any given commutative monoid such that the “one point rule” holds:
      The |fold| of a |singleton| is just the carrier element being injected into the carrier.

      That the one point rule holds ensures that the |singleton| embedding is in-fact injective
      ---provided our carrier type admits a commutative monoid structure at all; this is also
      a technical proviso for the one point rule.

\item |MultisetHom| consist of a method of |lift|ing functions between types to be between multisets
      which are compatible with the |singleton| and |fold| operations.

      ( Later we show, in |ListCMHom|, that lists with their usual
        map operation result in such a structure --with bag equality. )
      
      The expected Functorialty conditions are, for now, in their own record: |FunctorialMSH|.

\item |BuildLeftAdjoint|: Provided we have implementations of the multiset transformers we can
      produce a |Free| functor from category of setoids to the category of commutative monoids.

\item |ImplementationViaList|: An implementation of |Multiset| using lists with Bag equality
\end{enumerate}

%}}}

%{{{ Imports
\begin{code}
module Structures.Multiset-Bleeding-SET where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
    --
    -- Could not utilise this variant since _++_ is not a congruence wrt _≡_.
    --
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function using (id ; _∘_)
-- open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
-- open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)

open import Data.List     using ([]; [_]; _++_; _∷_; foldr; monoid)  renaming (map to mapL ; List to Bag)
open import Data.List.Properties using (map-++-commute; map-id; map-compose)

open import DataProperties hiding (⟨_,_⟩)
open import SetoidEquiv
open import ParComp
open import EqualityCombinators

-- open import Structures.CommMonoid-SET renaming (Hom to CMArrow)
open import Structures.CommMonoid renaming (Hom to CMArrow)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)

open import Algebra   using (Monoid ; CommutativeMonoid)
open import Data.List using (monoid)

open CommMonoid using (eq-in ; isCommMonoid)

open import Data.List.Any ; open Membership-≡
import Data.List.Any.BagAndSetEquality as BagEq

-- multiset type

BagSetoid : {ℓ : Level} → Set ℓ → Setoid ℓ ℓ
BagSetoid {ℓ} A = record { CommutativeMonoid (BagEq.commutativeMonoid bag A) }

-- Bag₀ : {ℓ : Level} → Set ℓ → Set ℓ
-- Bag₀ A = record { CommutativeMonoid (BagEq.commutativeMonoid bag A) }
-- 
bag-eq : {ℓ : Level} (X : Set ℓ) → Bag X → Bag X → Set ℓ
bag-eq X = let open Relation.Binary using (Setoid)
           in Setoid._≈_ (BagSetoid X)

infix -666 bag-eq
syntax bag-eq X s t  =  s ≈ₘ t ∶ X   -- ghost colon

open import Function.Inverse using (_↔_)

private 
  remark : {ℓ : Level} {X : Set ℓ} {xs ys : Bag X}
         → (xs ≈ₘ ys ∶ X) ≡ (∀ {z : X} →  (z ∈ xs) ↔ (z ∈ ys) )
  remark = ≡.refl
\end{code}
%}}}

%{{{ CtrSetoid
\subsection{CtrSetoid}

As will be explained below, the kind of ``container'' ---|ctr|--- used for
building a |Multiset| needs to support a |Setoid|-polymorphic
equivalence relation.
\begin{code}
record IsCtrEquivalence {ℓ : Level} (Ctr : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    equiv        : (X : Set ℓ) → Rel (Ctr X) ℓ
    equivIsEquiv : (X : Set ℓ) → IsEquivalence (equiv X)
    
  -- handy dandy syntactic sugar for |k|ontainer equality.
  infix -666 equiv
  syntax equiv X s t  =  s ≈ₖ t ∶ X   -- ghost colon
\end{code}

We have a type transformer |ctr| that furnishes setoids with an equivalence relation |equiv|.

\edcomm{MA}{Since there are no `coherencey' constraints, we might as well say that this
|IsCtrEquivalence| is nothing more than a setoid transformer: The object component of an endofunctor
on the category of setoids. Indeed:}

\begin{code}
  ctrSetoid : (X : Set ℓ) → Setoid ℓ ℓ
  ctrSetoid X = record
    { Carrier        =  Ctr X
    ; _≈_            =  equiv X
    ; isEquivalence  =  equivIsEquiv X
    }

Bag-isCtrEquivalence : (ℓ : Level) → IsCtrEquivalence Bag
Bag-isCtrEquivalence ℓ = record
  { equiv        = λ X → bag-eq X
  ; equivIsEquiv = λ X → Setoid.isEquivalence {ℓ} {ℓ} ([ bag ]-Equality X)
  }
\end{code}
%}}}

%{{{ CommutativeContainer

In the same vein as before, we consider a setoid-polymorphic equivalence relation that
also furnishes a raw type with a commutative monoid structure. That is, we now have
the object-component of a functor from the category of setoids to the category of
commutative monoids.

\begin{code}
record CommutativeContainer (ℓ : Level) : Set (lsuc ℓ) where
  open IsCtrEquivalence using (equiv)
  field
    𝒞                    : Set ℓ → Set ℓ
    isCtrEquivalence     :  IsCtrEquivalence 𝒞
    ∅                    :  {X : Set ℓ} → 𝒞 X
    _⊕_                  :  {X : Set ℓ} → 𝒞 X → 𝒞 X → 𝒞 X
    isCommutativeMonoid  :  {X : Set ℓ} → IsCommutativeMonoid (equiv isCtrEquivalence X) _⊕_ ∅

  open IsCtrEquivalence isCtrEquivalence             public

  commMonoid : (X : Set ℓ) → CommMonoid (ctrSetoid X)
  commMonoid X = record
    { e              =   ∅
    ; _*_            =   _⊕_
    ; isCommMonoid   =   isCommutativeMonoid
    }

Bag-CommutativeContainer : (ℓ : Level) → CommutativeContainer ℓ
Bag-CommutativeContainer ℓ = record
  { 𝒞 = Bag
  ; isCtrEquivalence = Bag-isCtrEquivalence ℓ
  ; ∅   = []
  ; _⊕_ = _++_
  ; isCommutativeMonoid = λ {X} →
      let open CommutativeMonoid (BagEq.commutativeMonoid bag X) in record
      -- let open Monoid (monoid X) in record
      { left-unit   =   identityˡ
      ; right-unit  =   proj₂ identity
      ; assoc       =   assoc
      ; comm        =   comm
      ; _⟨∙⟩_       =   ∙-cong      
      }
  -- |record { CommMonoid (asCommMonoid {ℓ} {ℓ} (BagEq.commutativeMonoid bag (Setoid.Carrier X))) }|
  -- wont work for some reason; it yields yellow.
  }
\end{code}

%}}}

%{{{ Multiset
\subsection{Multiset}
A “multiset on type X” is a structure on which one can define
\begin{itemize}
\item a \emph{commutative monoid} structure,
\item implement the concept of ``wrapping an element up as a \emph{singleton} container''
\item implement the concept of \emph{fold}; note that the name
is inspired by its implementation in the main model.  Its signature
would have suggested ``extract'', but this would have been
quite misleading.

  That is to say, we wish to have an operation |fold : ⦃x₁, …, xₙ⦄ ↦ x₁ ⊕ ⋯ ⊕ xₙ|
  where |⦃⋯⦄| are multi-set brackets and so order is irrelevant, but multiplicity matters.

  Really, we are asking for a way to ``form finite sums'' on the multiset.    
\end{itemize}

\begin{code}
𝑪𝑴 : {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
𝑪𝑴 X = CommMonoid (≡.setoid X)

record Multiset {ℓ : Level} (X : Set ℓ) : Set (lsuc ℓ) where  
  field
    commutativeContainer : CommutativeContainer ℓ

  open CommutativeContainer commutativeContainer public

  field
    singleton       :  X → Setoid.Carrier (ctrSetoid X)
    fold            :  {Y : Set ℓ} (CMY : 𝑪𝑴 Y) → CMArrow (commMonoid Y) CMY
    fold-singleton  :  {CMX : 𝑪𝑴 X} {x : X} → x ≡ fold CMX ⟨$⟩ singleton x

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|, and |𝒮| for referring to a multiset's singleton embedding operation.

  -- |𝓜 : CommMonoid (ctrSetoid X)|
  -- |𝓜 = commMonoid X|

  𝒮 : X → 𝒞 X
  𝒮 x = singleton x 

  singleton-injective : (CM : CommMonoid (≡.setoid X)) {x y : X}
                      → 𝒮 x ≈ 𝒮 y ∶ commMonoid X →  x ≡ y
  singleton-injective CM {x} {y} 𝒮x≈𝒮y = begin⟨ ≡.setoid X ⟩
      x
    ≈⟨ fold-singleton ⟩    
      fold CM  ⟨$⟩  𝒮 x
    ≈⟨ CMArrow.cong (fold CM) 𝒮x≈𝒮y ⟩
      fold CM  ⟨$⟩  𝒮 y
    ≈˘⟨ fold-singleton ⟩
      y
    ■
    where open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_; begin⟨_⟩_) renaming (_∎ to _■)

-- MA: Define and discuss,
  -- |_⊕₀_ : X₀ → X₀ → 𝒞 X₀|
  -- |x ⊕₀ y = fold {!commMonoid ?!} ⟨$⟩ ( (singleton ⟨$⟩₀ x) ⊕ (singleton ⟨$⟩₀ y) )|
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

In the classical contexts of sets and set-functions, the constraints take the form:
|{ f x } ≈ lift f { x }| and |fold (lift f s) ≈ f (fold s)|. In particular, the |lift| operation
mimics the behaviour of the morphism, or “map”, portion of a functor.

\begin{code}
record MultisetHom {ℓ : Level} {X Y : Set ℓ} (X* : Multiset X) (Y* : Multiset Y) : Set (lsuc ℓ) where

  open Multiset {ℓ}

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|.
  private
    𝓜 = λ {Z : Set ℓ} (CMZ : Multiset {ℓ} Z) → commMonoid CMZ Z

  field
    lift : (X → Y) → CMArrow (𝓜 X*) (𝓜 Y*)

    -- This ensures that |singleton| is sufficiently polymorphic; i.e., a natural transformation.
    -- See the Adjunction below.
    singleton-commute : (F : X → Y) {x : X} → 𝒮 Y* (F x) ≈ lift F ⟨$⟩ (𝒮 X* x)  ∶  𝓜 Y*
    
    fold-commute : {CMX : CommMonoid (≡.setoid X)} {CMY : CommMonoid (≡.setoid Y)}
                 → (F : CMArrow CMX CMY)
                 → {s : 𝒞 X* X}
                 → fold Y* CMY ⟨$⟩ (lift (F ⟨$⟩_ ) ⟨$⟩ s) ≡ F ⟨$⟩ (fold X* CMX ⟨$⟩ s)
                 -- MA: This is ``precisely'' the condition that |F| is a homomorphism!
                 -- Instead of requesting `F (x ⊕ y) ≈ F x ⊕ F y ∧ F ε ≈ ε`, we ask for
                 -- `F (x₁ ⊕ ⋯ ⊕ xₙ) ≈ F x₁ ⊕ ⋯ ⊕ F xₙ` for any `n : ℕ`.
\end{code}

\edcomm{MA}{

From Bird's theory of lists we know that every list homomorphism is the composition of a fold
after a map. Now a fold usually serves to realise an algebra as being initial and so ``least'' in some
sense. As such, perhaps it'd be beneficial to request every |CMArrow (commMonoid Y) CMY|
be expressible as a |fold|?

}%edcomm

And now something somewhat different: To express that we have the right
functoriality properties (and ``zap''), we need to assume that we have
\emph{constructors} of |Multiset| and |MultisetHom|.  With these in hand,
we can then phrase what extra properties must hold.  Because these properties
hold at ``different types'' than the ones for the underlying ones, these
cannot go into the above.
\begin{code}
record FunctorialMSH {ℓ : Level} (MS : (X : Set ℓ) → Multiset X)
    (MSH : {X Y : Set ℓ} → MultisetHom {ℓ} {X} {Y} (MS X) (MS Y))
    : Set (lsuc ℓ) where

  open Multiset
  open MultisetHom
  open Setoid   using (Carrier)
  open IsCtrEquivalence hiding (ctrSetoid)

  private 
    Obj = Set ℓ
    𝒞ₘ = λ X → 𝒞 (MS X) X
    𝓜 = λ X → commMonoid (MS X) X

    -- 𝑳ift and apply onto the ₘultiset.
    𝑳ₘ  = λ {X Y : Obj}  (F   : X → Y) (x : 𝒞ₘ X) → lift MSH F ⟨$⟩ x

    infix 0 _≋_
    _≋_ = λ {X : Obj} (l r : 𝒞ₘ X) → l ≈ r ∶ 𝓜 X

  field
    -- Lifting the identity yields an identity morphism.
    id-pres : {X : Obj} → {x : 𝒞ₘ X} → 𝑳ₘ id x  ≋  x

    -- Lifting preserves composition.
    ∘-pres : {X Y Z : Obj} {F : X → Y} {G : Y → Z}
           → {x : 𝒞ₘ X} → 𝑳ₘ (G ∘ F) x  ≋  𝑳ₘ G (𝑳ₘ F x)

    -- Lifting preserves extensional equality.
    resp-≈ : {X Y : Obj} {F G : X → Y}
          → (F≈G : {x : X} → F x ≡ G x)
          → {x : 𝒞ₘ X} → 𝑳ₘ F x  ≋  𝑳ₘ G x

    -- Lifting the singleton mapping then folding yields the orginal result.
    -- In particular, the singleton construction is injective --as we'd like.
--     fold-lift-singleton : {X : Obj} (let ms = MS X ; _≈_ = equiv (isCtrEquivalence ms) X)
--       → {s : 𝒞ₘ X} → s ≈ (fold (MS X) (commMonoid {!!} {!!}) ⟨$⟩ {!!})
--       -- (fold (MS (ctrSetoid ms X)) (𝓜 X) ⟨$⟩ (𝑳ₘ (singleton ms) s))
\end{code}    
%}}}

%{{{ BuildLeftAdjoint
Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module BuildLeftAdjoint
  (MS   : {ℓ : Level} (X : Set ℓ) → Multiset X)
  (MSH  : {ℓ : Level} {X Y : Set ℓ} → MultisetHom {ℓ} (MS X) (MS Y))
  (Func : {ℓ : Level} → FunctorialMSH {ℓ} MS MSH )
  where

  module _ {ℓ} {X : Set ℓ} where open Multiset (MS X) public
  module _ {ℓ} {X Y : Set ℓ} where open MultisetHom (MSH {ℓ} {X} {Y}) public
  module _ {ℓ} where open FunctorialMSH {ℓ} Func public

  open import Function.Equality using (Π)  

  -- completely ignore the setoid structure ...
  Free : (ℓ c : Level) → Functor (Setoids ℓ c) (CommMonoidCat ℓ ℓ)
  Free _ _ = record
    { F₀             =  λ 𝑺 → let S = Setoid.Carrier 𝑺 in ctrSetoid S , commMonoid {_} {S} S
    ; F₁             =  λ 𝑭 → let F = Π._⟨$⟩_ 𝑭 in record { CMArrow (lift F) }
    ; identity       = id-pres
    ; homomorphism   = ∘-pres
    ; F-resp-≡      =  {!resp-≈!}
    }
\end{code}
\begin{spec}
  LeftAdjoint : {ℓ c : Level} → Adjunction (Free ℓ ℓ) (Forget ℓ ℓ)
  LeftAdjoint = record
    { unit = record
      { η = λ _ → singleton
      ; commute = singleton-commute
      }
    ; counit = record
      { η        =  λ { (_ , cm) → record { CMArrow (fold cm) } }
      ; commute  =  fold-commute
      }
    ; zig = ? -- fold-lift-singleton
    ; zag = λ { {X , _} → fold-singleton {X = X} }
    }
\end{spec}
%}}}

%{{{ An implementation of |Multiset| using lists with Bag equality
\subsection{An implementation of |Multiset| using lists with Bag equality}
\begin{code}
open import Relation.Binary.SetoidReasoning renaming (_∎ to _■₀)

open import Function.Inverse using (_↔_)
open import Data.List.Any.Properties hiding (map-id)
open import Function using (_$_)
open import Function.Related hiding (_∼[_]_) ; open EquationalReasoning renaming (_∎ to _■) hiding (sym)
module ↔ = EquationalReasoning
open import Function.Inverse public using () renaming  (id to  ↔-refl)

postulate

  singleton-cong-lemma : {ℓ : Level} (X : Setoid ℓ ℓ) (x y : Setoid.Carrier X) → Setoid._≈_ X x y
                       → {z : Setoid.Carrier X} → (z ≡ x  ⊎  z ∈ [])  ↔  (z ≡ y  ⊎  z ∈ [])

-- Ought to be |module CMUtils {ℓ c : Level} {X : Setoid ℓ (ℓ ⊍ c)} (CMX : CommMonoid X) where|.
module CMUtils {ℓ : Level} {X : Setoid ℓ ℓ} (CMX : CommMonoid X) where

  open CommMonoid CMX
  open Setoid X using (_≈_)
  open import Data.List as List using (List; []; _∷_; _++_)

  fold₀ : List (Setoid.Carrier X) → Setoid.Carrier X
  fold₀ = List.foldr _*_ e
  --
  -- c.f., -- https://github.com/bch29/agda-stdlib/blob/106a4fbd6f3feb12e99704589ef93b637fbe96ea/src/Algebra/Operations/CommutativeMonoid.agda

  -- https://github.com/bch29/agda-stdlib/blob/106a4fbd6f3feb12e99704589ef93b637fbe96ea/src/Data/List/Any/Properties/CommutativeMonoid.agda
  --
  -- In a commutative monoid, if you add up everything in two lists that contain
  -- the same elements, you get the same result.  
  postulate
    sum-bag : ∀ {xs ys} → xs ∼[ bag ] ys → fold₀ xs ≈ fold₀ ys

module ImplementationViaList {ℓ : Level} (X : Set ℓ) where
  open Setoid  
  -- open ElemOfSing X

  ListMS : Multiset {ℓ} X -- \edcomm{MA}{This homogenity of levels is unsettling. }
  ListMS = record
    { commutativeContainer   =   Bag-CommutativeContainer ℓ
    ; singleton              =  _∷ []
    ; fold  =   λ {Y} CMY → let open CMUtils CMY in record
      { mor      =   record { _⟨$⟩_ = fold₀ ; cong = sum-bag }
      ; pres-e   =   ≡.refl
      ; pres-*   =   fold-CM-over-++ CMY
      }
    ; fold-singleton         =   λ {CMX} {x} → ≡.sym (CommMonoid.right-unit CMX x)
    }
    where

      open IsCommutativeMonoid using (left-unit ; right-unit ; assoc) renaming (_⟨∙⟩_ to cong)      
       
      fold-CM-over-++ : {Z : Setoid ℓ ℓ} (cm : CommMonoid Z) {s t : Bag (Carrier Z)}
                      →  let open CommMonoid cm ; F = foldr _*_ e in
                          F (s ++ t) ≈⌊ Z ⌋ (F s * F t)
      fold-CM-over-++ {Z} (MkCommMon e _*_ isCommMon) {[]} {t} = sym Z (left-unit isCommMon _)
      fold-CM-over-++ {Z} CMZ@(MkCommMon e _*_ isCommMon) {x ∷ s} {t} = begin⟨ Z ⟩
        let F = foldr _*_ e in
        x * F (s ++ t)   ≈⟨ cong isCommMon (refl Z) (fold-CM-over-++ CMZ ) ⟩
        x * (F s * F t)  ≈⟨ sym Z (assoc isCommMon _ _ _)                  ⟩
        (x * F s) * F t  ■₀

open ImplementationViaList
\end{code}

\begin{code}
∈-↔-reflexive : {ℓ : Level} {X : Set ℓ} {xs ys : Bag X}
            → xs ≡ ys  →  {z : X}  →  z ∈ xs  ↔  z ∈ ys
∈-↔-reflexive ≡.refl = ↔-refl

ListCMHom : {ℓ : Level} {X Y : Set ℓ} → MultisetHom (ListMS X) (ListMS Y)
ListCMHom {ℓ} {X} {Y} = record
  { lift                =   λ f → let mapf =  mapL f  in record
    { mor      =    record { _⟨$⟩_ = mapf ; cong = λ {xs} {ys} xs≈ys {z} →  
          z ∈ mapf xs
       ↔⟨⟩
          Any (z ≡_) (mapL f xs)
       ↔⟨ ↔.sym map↔ ⟩
          Any (λ e → z ≡ f e) xs
       ↔⟨ Any-cong (λ x → ≡⇒ ≡.refl) xs≈ys ⟩
          Any (λ e → z ≡ f e) ys
       ↔⟨ map↔ ⟩
          z ∈ mapf ys
       ■  } 
    ; pres-e   =   ↔-refl
    ; pres-*   =   λ {xs ys} → ∈-↔-reflexive (map-++-commute f xs ys)
                 -- Equivalently, |≡⇒ (≡.cong (z ∈_) (map-++-commute (f ⟨$⟩₀_) xs ys))|
    }
  ; singleton-commute   =   λ f {x} → ↔-refl
  ; fold-commute        =   it
  }
  where

    -- Proving |foldr _*₂_ e₂ (mapL (F ⟨$⟩_) xs)  ≈ F ⟨$⟩ foldr _*₁_ e₁ xs|.
    it : {ℓ : Level} {X Y : Setoid ℓ ℓ} {CMX : CommMonoid X} {CMY : CommMonoid Y}
         (F : CMArrow CMX CMY) {xs : Bag (Setoid.Carrier X)} (open CMUtils)
         → fold₀ CMY (mapL (F ⟨$⟩_) xs)  ≈⌊ Y ⌋  F ⟨$⟩ fold₀ CMX xs
    it {ℓ₁} {X} {Y} F {[]} = Setoid.sym Y (pres-e F)
    it {ℓ₁} {X} {Y} {CMX@(MkCommMon _ _*₁_ _)} {CMY@(MkCommMon _ _*₂_ isCM₂)} F {x ∷ xs} =
        begin⟨ Y ⟩
           (F ⟨$⟩ x)  *₂  fold₀ CMY (mapL (F ⟨$⟩_) xs)
        ≈⟨ refl ⟨∙⟩ it F ⟩
           (F ⟨$⟩ x)  *₂  (F ⟨$⟩ fold₀ CMX xs)
        ≈˘⟨ pres-* F ⟩
           F ⟨$⟩ (x *₁ fold₀ CMX xs)
        ■₀
        where open IsCommutativeMonoid isCM₂ using (_⟨∙⟩_)
              open CMUtils ; open Setoid Y
\end{code}

\begin{code}
-- \edcomm{MA}{Should be moved into a List-like library. Maybe moved to the standard library.}
-- Transforming a list into singletons then catenating is the same as “doing nothing.”
concat-singleton : {ℓ : Level} {X : Set ℓ} (xs : Bag X)
                 → xs ≡ foldr _++_ [] (mapL [_] xs)
concat-singleton []         =   ≡.refl
concat-singleton (x ∷ xs)   =   ≡.cong (x ∷_) (concat-singleton xs)

-- \edcomm{MA}{Should be moved into a Any-like library. Maybe moved to the standard library.}
resp-helper : {ℓ : Level} {B : Set ℓ} {l r : B}
            → l ≡ r → {z : B}
            → (z ≡ l) ↔ (z ≡ r)
resp-helper {ℓ} {B} {l} {.l} _≡_.refl {z} = ↔-refl

module BuildProperties where
  open ImplementationViaList
  functoriality : {ℓ : Level} → FunctorialMSH {ℓ} ListMS ListCMHom
  functoriality {ℓ} = record
    { id-pres               =   λ {X} {xs} → ∈-↔-reflexive (map-id xs)
    ; ∘-pres                =   λ {_} {_} {Z} {F} {G} {xs} → ∈-↔-reflexive (map-compose xs)
    ; resp-≈                =   λ {A} {B} {f} {g} F≈G {xs} → λ {z} →  
          z  ∈  mapL f xs
       ↔⟨⟩ 
          Any (z ≡_) (mapL f xs)
       ↔⟨ ↔.sym map↔ ⟩
          Any (λ e → z ≡ f e) xs
       ↔⟨ Any-cong (λ x → resp-helper {_} {B} {f x} {g x} F≈G {z}) (≡⇒ ≡.refl) ⟩
          Any (λ e → z ≡ g e) xs
       ↔⟨ map↔ ⟩
          z  ∈  mapL g xs
       ■ 
    -- ; fold-lift-singleton   =   λ {X} {xs} → ∈-↔-reflexive (concat-singleton xs)
    }
    where
\end{code}                  

Last but not least, build the left adjoint:

\begin{code}
module FreeCommMonoid = BuildLeftAdjoint ImplementationViaList.ListMS ListCMHom
  BuildProperties.functoriality
\end{code}
%}}}

% Quick Folding Instructions:
% C-c C-s :: show/unfold region
% C-c C-h :: hide/fold region
% C-c C-w :: whole file fold
% C-c C-o :: whole file unfold
%
% Local Variables:
% folded-file: t
% eval: (fold-set-marks "%{{{ " "%}}}")
% eval: (fold-whole-buffer)
% fold-internal-margins: 0
% end:
