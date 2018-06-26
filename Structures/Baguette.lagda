\section{Structures.Baguette}

\iffalse
New experimental variation on |Structures.Multiset| using Brad Hardy's work.

A “baguette” is a long and narrow loaf of French bread.
The same modifiers are used to describe the final piece of this project.

Alternatively, a “baguette” is a form of gem, as is this the project's remaining hole.

On a completely unrelated matter, we're running out of names since
we already have files named “multiset” and “bag” in the experimental directory.
\fi

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
module Structures.Baguette where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)

open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open Π                        using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open import Algebra           using (Monoid ; CommutativeMonoid ; CommutativeSemiring)
open import Relation.Binary   using (Setoid; Rel; IsEquivalence)
open Setoid                   using (Carrier)

open import Data.List  using ([]; [_]; _++_; _∷_)  renaming (map to mapL)
open import Data.List.Properties using (map-++-commute; map-id; map-compose)
import Data.List as List
open import Data.Fin.Permutation using (Permutation) renaming (id to idp)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
import Data.Fin as Fin

open import Data.Sum using ([_,_]′)

open import Structures.CommMonoid renaming (Hom to CMArrow)

open import Helpers.DataProperties hiding (⟨_,_⟩ ; ⊎-cong; _‼_)
open import Helpers.EqualityCombinators
open import Helpers.FinEquivPlusTimes using (module Plus)
open Plus using (+≃⊎)

open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
open CommMonoid using (eq-in ; isCommMonoid)

open import Relation.Binary.SetoidReasoning renaming (_∎ to _■₀)

open import Function.Inverse using (_↔_; module Inverse)
open import Data.List.Any.Properties hiding (map-id)
open import Function using (_$_)

-- multiset type
open import Structures.SequencesAsBags as Seq
  using (table ; table˘ ; BagSetoid; len; sequence) renaming (Seq to Bag)

bag-eq : {ℓ c : Level} (X : Setoid ℓ c) (f g : Bag (Setoid.Carrier X)) → Set c
bag-eq X = Setoid._≈_ (BagSetoid X)

infix -666 bag-eq
syntax bag-eq X s t  =  s ≈ₘ t ∶ X   -- ghost colon
\end{code}
%}}}

%{{{ CtrSetoid
\subsection{CtrSetoid}

As will be explained below, the kind of ``container'' ---|ctr|--- used for
building a |Multiset| needs to support a |Setoid|-polymorphic
equivalence relation.
\begin{code}
record IsCtrEquivalence {ℓ : Level} (o : Level) (Ctr : Set ℓ → Set ℓ)
  : Set (lsuc ℓ ⊍ lsuc o) where
  field
    equiv        : (X : Setoid ℓ o) → Rel (Ctr (Setoid.Carrier X)) o
    equivIsEquiv : (X : Setoid ℓ o) → IsEquivalence (equiv X)

  -- handy dandy syntactic sugar for |k|ontainer equality.
  infix -666 equiv
  syntax equiv X s t  =  s ≈ₖ t ∶ X   -- ghost colon
\end{code}

We have a type transformer |ctr| that furnishes setoids with an equivalence relation |equiv|.

\edcomm{MA}{Since there are no `coherencey' constraints, we might as well say that this
|IsCtrEquivalence| is nothing more than a setoid transformer: The object component of an endofunctor
on the category of setoids. Indeed:}

\begin{code}
  ctrSetoid : (X : Setoid ℓ o) → Setoid ℓ o
  ctrSetoid X = record
    { Carrier        =  Ctr (Setoid.Carrier X)
    ; _≈_            =  equiv X
    ; isEquivalence  =  equivIsEquiv X
    }

Bag-isCtrEquivalence : (ℓ c : Level) → IsCtrEquivalence {ℓ} c Bag
Bag-isCtrEquivalence ℓ c = record
  { equiv        = λ X → Setoid._≈_ (BagSetoid X)
  ; equivIsEquiv = λ X → Setoid.isEquivalence (BagSetoid X)
  }
\end{code}
%}}}

%{{{ CommutativeContainer

In the same vein as before, we consider a setoid-polymorphic equivalence relation that
also furnishes a raw type with a commutative monoid structure. That is, we now have
the object-component of a functor from the category of setoids to the category of
commutative monoids.

\begin{code}
record CommutativeContainer (ℓ c : Level) : Set (lsuc ℓ ⊍ lsuc c) where
  open IsCtrEquivalence using (equiv)
  field
    𝒞                    : Set ℓ → Set ℓ
    isCtrEquivalence     :  IsCtrEquivalence c 𝒞
    ∅                    :  {X : Set ℓ} → 𝒞 X
    _⊕_                  :  {X : Set ℓ} → 𝒞 X → 𝒞 X → 𝒞 X
    isCommutativeMonoid  :  {X : Setoid ℓ c} → IsCommutativeMonoid (equiv isCtrEquivalence X) _⊕_ ∅

  open IsCtrEquivalence isCtrEquivalence             public

  commMonoid : (X : Setoid ℓ c) → CommMonoid (ctrSetoid X)
  commMonoid X = record
    { e              =   ∅
    ; _*_            =   _⊕_
    ; isCommMonoid   =   isCommutativeMonoid
    }

Bag-CommutativeContainer : (ℓ c : Level) → CommutativeContainer ℓ c
Bag-CommutativeContainer ℓ c = record
  { 𝒞 = Bag
  ; isCtrEquivalence = Bag-isCtrEquivalence ℓ c
  ; ∅   = λ {X} → Seq.∅
  ; _⊕_ = λ {X} → Seq._⊕_
  ; isCommutativeMonoid = λ {X} →
      let open CommutativeMonoid (Seq.commutativeMonoid X) in record
      { left-unit   =  identityˡ
      ; right-unit  =  proj₂ identity
      ; assoc       =  assoc
      ; comm        =  comm
      ; _⟨∙⟩_       =  ∙-cong
      }
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
record Multiset {ℓ c : Level} (X : Setoid ℓ c) : Set (lsuc ℓ ⊍ lsuc c) where
  field
    commutativeContainer : CommutativeContainer ℓ c

  open CommutativeContainer commutativeContainer     public
  open Setoid X using (_≈_) renaming (Carrier to X₀)

  field
    singleton       :  X ⟶ ctrSetoid X             -- A setoid map
    fold            :  {Y : Setoid ℓ c} (CMY : CommMonoid Y) → CMArrow (commMonoid Y) CMY
    fold-singleton  :  {CM : CommMonoid X} {x : X₀} → x ≈ fold CM ⟨$⟩ (singleton ⟨$⟩₀ x)

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|, and |𝒮| for referring to a multiset's singleton embedding operation.

  -- |𝓜 : CommMonoid (ctrSetoid X)|
  -- |𝓜 = commMonoid X|

  𝒮 : X₀ → 𝒞 X₀
  𝒮 x = singleton ⟨$⟩₀ x

  singleton-injective : (CM : CommMonoid X) {x y : X₀}
                      → 𝒮 x ≈ 𝒮 y ∶ commMonoid X  →  x ≈ y
  singleton-injective CM {x} {y} 𝒮x≈𝒮y = begin⟨ X ⟩
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
record MultisetHom {ℓ c : Level} {X Y : Setoid ℓ c} (X* : Multiset X) (Y* : Multiset Y)
  : Set (lsuc ℓ ⊍ lsuc c) where
  open Multiset {ℓ} {c}
  X₀ = Setoid.Carrier X
  open Setoid Y using (_≈_)

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|.
  private
    𝓜 = λ {Z : Setoid ℓ c} (CMZ : Multiset Z) → commMonoid CMZ Z

  field
    lift : (X ⟶ Y) → CMArrow (𝓜 X*) (𝓜 Y*)

    -- This ensures that |singleton| is sufficiently polymorphic; i.e., a natural transformation.
    -- See the Adjunction below.
    singleton-commute : (F : X ⟶ Y) {x : X₀} → 𝒮 Y* (F ⟨$⟩₀ x) ≈ lift F ⟨$⟩ (𝒮 X* x)  ∶  𝓜 Y*

    fold-commute : {CMX : CommMonoid X} {CMY : CommMonoid Y} (F : CMArrow CMX CMY)
                 → {s : 𝒞 X* X₀}
                 → fold Y* CMY ⟨$⟩ (lift (mor F) ⟨$⟩ s)  ≈  F ⟨$⟩ (fold X* CMX ⟨$⟩ s)
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
record FunctorialMSH {ℓ c : Level} (MS : (X : Setoid ℓ c) → Multiset X)
    (MSH : {X Y : Setoid ℓ c} → MultisetHom {ℓ} {c} {X} {Y} (MS X) (MS Y))
    : Set (lsuc ℓ ⊍ lsuc c) where
  open Multiset
  open MultisetHom
  open Setoid   using (Carrier)
  open IsCtrEquivalence hiding (ctrSetoid)
  private
    Obj = Setoid ℓ c
    𝒞ₘ = λ X → 𝒞 (MS X) (Carrier X)
    𝓜 = λ X → commMonoid (MS X) X

    -- 𝑳ift and apply onto the ₘultiset.
    𝑳ₘ  = λ {X Y : Obj}  (F   : X ⟶ Y) (x : 𝒞ₘ X) → lift MSH F ⟨$⟩ x

    infix 0 _≋_
    _≋_ = λ {X : Obj} (l r : 𝒞ₘ X) → l ≈ r ∶ 𝓜 X

  field
    -- Lifting the identity yields an identity morphism.
    id-pres : {X : Obj} → {x : 𝒞ₘ X} → 𝑳ₘ id x  ≋  x

    -- Lifting preserves composition.
    ∘-pres : {X Y Z : Obj} {F : X ⟶ Y} {G : Y ⟶ Z}
           → {x : 𝒞ₘ X} → 𝑳ₘ (G ∘ F) x  ≋  𝑳ₘ G (𝑳ₘ F x)

    -- Lifting preserves extensional equality.
    resp-≈ : {X Y : Obj} {F G : X ⟶ Y} (let open Setoid Y renaming (_≈_ to _≈₀_))
          → (F≈G : {x : Carrier X} → F ⟨$⟩₀ x ≈₀ G ⟨$⟩₀ x)
          → {x : 𝒞ₘ X} → 𝑳ₘ F x  ≋  𝑳ₘ G x

    -- Lifting the singleton mapping then folding yields the orginal result.
    -- In particular, the singleton construction is injective --as we'd like.
    fold-lift-singleton : {X : Obj} (let ms = MS X ; _≈_ = equiv (isCtrEquivalence ms) X)
      → {s : 𝒞ₘ X} → s ≈ (fold (MS (ctrSetoid ms X)) (𝓜 X) ⟨$⟩ (𝑳ₘ (singleton ms) s))
\end{code}
%}}}

%{{{ BuildLeftAdjoint
Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module BuildLeftAdjoint
  (MS   : {ℓ c : Level} (X : Setoid ℓ c) → Multiset X)
  (MSH  : {ℓ c : Level} {X Y : Setoid ℓ c} → MultisetHom {ℓ} {c} (MS X) (MS {c = c} Y))
  (Func : {ℓ c : Level} → FunctorialMSH {ℓ} {c} MS MSH )
  where

  module _ {ℓ c} {X : Setoid ℓ c} where open Multiset {ℓ} {c} (MS X) public
  module _ {ℓ c} {X Y : Setoid ℓ c} where open MultisetHom (MSH {ℓ} {c} {X} {Y}) public
  module _ {ℓ c} where open FunctorialMSH {ℓ} {c} Func public

  Free : (ℓ c : Level) → Functor (Setoids ℓ c) (CommMonoidCat ℓ c)
  Free ℓ c = record
    { F₀             =   λ S → ctrSetoid {ℓ} {c} S , commMonoid S
    ; F₁             =   λ F → record { CMArrow (lift F) }
    ; identity       =   id-pres
    ; homomorphism   =   ∘-pres
    ; F-resp-≡      =   resp-≈
    }

  LeftAdjoint : {ℓ c : Level} → Adjunction (Free ℓ c) (Forget ℓ c)
  LeftAdjoint = record
    { unit = record
      { η = λ _ → singleton
      ; commute = singleton-commute
      }
    ; counit = record
      { η        =  λ { (_ , cm) → record { CMArrow (fold cm) } }
      ; commute  =  fold-commute
      }
    ; zig = fold-lift-singleton
    ; zag = λ { {X , _} → fold-singleton {X = X} }
    }
\end{code}
%}}}

%{{{ An implementation of |Multiset| using lists with Bag equality
\subsection{An implementation of |Multiset| using lists with Bag equality}
\begin{code}
module CMUtils {ℓ c : Level} {S : Setoid ℓ c} (CMS : CommMonoid S) where
  open Setoid S using (_≈_) renaming (Carrier to S₀)
  open CommMonoid CMS renaming (_*_ to _+_)
  open import Data.Table.Base
  open import Algebra.Operations.CommutativeMonoid (asCommutativeMonoid CMS)
  -- open import Algebra.Properties.CommutativeMonoid (asCommutativeMonoid CMS)
  open import Helpers.Hardy
  open HardyCommutativeMonoid (asCommutativeMonoid CMS)

  sumₛ : Bag S₀ → S₀
  sumₛ = λ f → sumₜ (table f)

  -- In a commutative monoid, if you add up everything in two sequences that contain
  -- the same elements, you get the same result.
  sumₛ-cong : {f g : Bag S₀} → f ≈ₘ g ∶ S → sumₛ f ≈ sumₛ g
  sumₛ-cong {f} {g} (s Seq.⟨π⟩ f≈sg) = let open Setoid S in begin⟨ S ⟩
      sumₛ f
    ≈⟨ refl ⟩
      sumₜ (table f)
    ≈⟨ sumₜ-cong {Seq.len f} {table f} {table (s Seq.◈ g)} f≈sg ⟩
      sumₜ (table (s Seq.◈ g))
    ≈⟨ sym (sumₜ-permute′ {Seq.len f} {Seq.len g} (table g) s)   ⟩
      sumₜ (table g)
    ≈⟨ refl ⟩
      sumₛ g
    ■₀

  -- The |sumₛ| operator distributes over addition.
  sumₛ-homo : {f g : Bag S₀} → sumₛ (f Seq.⊕ g) ≈ sumₛ f + sumₛ g
  sumₛ-homo {f} = Seq.sumₜ-homo CMS (len f)

ListMS : {ℓ c : Level} (X : Setoid ℓ c) → Multiset {ℓ} {c} X
ListMS {ℓ} {c} X = record
    { commutativeContainer   =   Bag-CommutativeContainer ℓ c
    ; singleton              =   record { _⟨$⟩_ = Seq.singleton X ; cong = Seq.singleton-cong X }
    ; fold  =   λ {Y} CMY → let open CMUtils CMY in record
      { mor      =   record { _⟨$⟩_ = sumₛ ; cong = sumₛ-cong }
      ; pres-e   =   Setoid.refl Y
      ; pres-*   =   λ {f} {g} → sumₛ-homo {f} {g}
      }
    ; fold-singleton         =   λ {CMX} {x} → Setoid.sym X (CommMonoid.right-unit CMX x)
    }
\end{code}

\begin{code}
open import Data.Table.Base

apply-map : {ℓ ℓ′ c : Level} {X Y : Setoid ℓ c} {Z W : Set ℓ′} {g : Z → Carrier X} {h : W → Carrier X} →
  (f : X ⟶ Y) → (c : Z ⊎ W) → Setoid._≈_ Y (f ⟨$⟩₀ ([ g , h ]′ c)) ([ (λ x → f ⟨$⟩₀ (g x)), (λ x → f ⟨$⟩₀ (h x)) ]′ c)
apply-map {Y = Y} f (inj₁ x) = Setoid.refl Y
apply-map {Y = Y} f (inj₂ y) = Setoid.refl Y

ListCMHom : {ℓ c : Level} {X Y : Setoid ℓ c} → MultisetHom (ListMS {ℓ} {c} X) (ListMS {ℓ} {c} Y)
ListCMHom {ℓ} {c} {X} {Y} = record
  { lift =   λ f → let mapf = λ x → table˘ (map (f ⟨$⟩₀_) (table x)) in record
    { mor      =   record
      { _⟨$⟩_ = mapf
      ; cong  = λ i≈ₛj → Seq._≈ₛ_.shuffle i≈ₛj Seq.⟨π⟩ (λ a → Π.cong f (Seq._≈ₛ_.eq i≈ₛj a))
      }
    ; pres-e   =   Function.Inverse.id Seq.⟨π⟩ λ ()
    ; pres-*   =   λ {xs ys} → Function.Inverse.id Seq.⟨π⟩ λ i → apply-map {ℓ} {_} {c} {g = Bag._‼_ xs} f (proj₁ +≃⊎ i)
    }
  ; singleton-commute   =   λ F → Seq.≈ₛ-refl Y
  ; fold-commute        =   λ {CMX} {CMY} F {s} → it {CMX = CMX} {CMY} F {Seq.len s}
  }
  where
    -- Proving |foldr _*₂_ e₂ (mapL (F ⟨$⟩_) xs)  ≈ F ⟨$⟩ foldr _*₁_ e₁ xs|.
    it : {ℓ c : Level} {X Y : Setoid ℓ c} {CMX : CommMonoid X} {CMY : CommMonoid Y}
         (F : CMArrow CMX CMY) {n : ℕ} {s : Fin.Fin n → Carrier X}
         → foldr (CommMonoid._*_ CMY) (CommMonoid.e CMY) (tabulate (λ x → mor F ⟨$⟩₀ (s x)))  ≈⌊ Y ⌋
           mor F ⟨$⟩₀ foldr (CommMonoid._*_ CMX) (CommMonoid.e CMX) (tabulate s)
    it {ℓ} {c} {X} {Y} {MkCommMon e₁ _*₁_ _} {MkCommMon e₂ _*₂_ isCM₂} F {zero} {_} = Setoid.sym Y (pres-e F)
    it {ℓ} {c} {X} {Y} {MkCommMon e₁ _*₁_ _} {MkCommMon e₂ _*₂_ isCM₂} F {suc len} {tb} =
       let G = mor F ⟨$⟩₀_ in begin⟨ Y ⟩
       G (tb Fin.zero) *₂ (foldr _*₂_ e₂ (tabulate (λ x → G (tb (Fin.suc x)))))  ≈⟨ Setoid.refl Y ⟨∙⟩ it F {len} ⟩
       G (tb Fin.zero) *₂ (G (foldr _*₁_ e₁ (tabulate λ x → tb (Fin.suc x))))    ≈⟨ Setoid.sym Y (pres-* F) ⟩
       G (foldr _*₁_ e₁ (tabulate tb)) ■₀
        where open IsCommutativeMonoid isCM₂ using (_⟨∙⟩_)
              open CMUtils
\end{code}

\begin{code}
module BuildProperties where  
  functoriality : {ℓ c : Level} → FunctorialMSH {ℓ} (ListMS {ℓ} {c}) ListCMHom
  functoriality {ℓ} {c} = record
    { id-pres               =   λ {X} {xs} → idp Seq.⟨π⟩ λ _ → Setoid.refl X
    ; ∘-pres                =   λ {_} {_} {Z} {F} {G} {xs} → Seq.≈ₛ-refl Z
    ; resp-≈                =   λ {X} {Y} {f} {g} F≈G {xs} → idp Seq.⟨π⟩ λ i → F≈G {xs Bag.‼ i}
    ; fold-lift-singleton   =   λ {X} {xs} →
      fold-perm {X} (Bag.len xs) (Bag._‼_ xs) Seq.⟨π⟩ λ i → fold-perm-adequate {X} (Bag.len xs) (Bag._‼_ xs) i
    }
    where
    open Multiset            using   (𝒞; commMonoid; ctrSetoid; fold; singleton)
    open MultisetHom         using   (lift)
    open import Data.Table   using   (permute)
    
    module _ {X : Setoid ℓ c} where
      LMS = ListMS {ℓ} {c} X
      L = ListMS {ℓ} {c} (ctrSetoid LMS X)
      C = commMonoid LMS X
      
      same-size : (n : ℕ) (bg : Fin.Fin n → Carrier X) →
        let xs = Bag.sequence n bg in
        n ≡ (Bag.len (fold LMS C ⟨$⟩ (lift ListCMHom (singleton LMS) ⟨$⟩ xs)))
      same-size zero bg = ≡.refl
      same-size (suc n) bg = ≡.cong suc (same-size n _)
      
      fold-perm : (n : ℕ) (bg : Fin.Fin n → Carrier X) →
        let xs = Bag.sequence n bg in
        Permutation n (Bag.len (fold LMS C ⟨$⟩ (lift ListCMHom (singleton LMS) ⟨$⟩ xs)))
      fold-perm zero bg = idp
      fold-perm (suc n) bg = record
        { to = record
          { _⟨$⟩_ = λ { Fin.zero → Fin.zero ; (Fin.suc x) → Fin.suc (Function.Inverse.Inverse.to (fold-perm n (λ i → bg (Fin.suc i))) ⟨$⟩₀ x)}
          ; cong = λ { ≡.refl → ≡.refl} }
        ; from = record
          { _⟨$⟩_ = λ { Fin.zero → Fin.zero ; (Fin.suc x) → Fin.suc (Function.Inverse.Inverse.from (fold-perm n (λ i → bg (Fin.suc i))) ⟨$⟩₀ x)}
          ; cong = λ { ≡.refl → ≡.refl} }
        ; inverse-of = record
          { left-inverse-of = λ { Fin.zero → ≡.refl ; (Fin.suc x) → ≡.cong Fin.suc (Function.Inverse.Inverse.left-inverse-of (fold-perm n _) x)}
          ; right-inverse-of = λ { Fin.zero → ≡.refl ; (Fin.suc x) → ≡.cong Fin.suc (Function.Inverse.Inverse.right-inverse-of (fold-perm n _) x)} }
        }

      fold-perm-id : (n : ℕ) (bg : Fin.Fin n → Carrier X) (i : Fin.Fin n) → Fin.toℕ (Inverse.to (fold-perm n bg) ⟨$⟩₀ i) ≡ Fin.toℕ i
      fold-perm-id zero bg ()
      fold-perm-id (suc n) bg Fin.zero = ≡.refl
      fold-perm-id (suc n) bg (Fin.suc i) = ≡.cong suc (fold-perm-id n _ i)

      fold-perm-adequate : (n : ℕ) (bg : Fin.Fin n → Carrier X) (i : Fin.Fin n) →
        let xs = Bag.sequence n bg in
        lookup (table xs) i ≈⌊ X ⌋
          lookup (permute (fold-perm n bg) (table (fold LMS C ⟨$⟩ (lift ListCMHom (singleton LMS) ⟨$⟩ xs)))) i
      fold-perm-adequate zero bg ()
      fold-perm-adequate (suc n) bg Fin.zero = Setoid.refl X
      fold-perm-adequate (suc n) bg (Fin.suc i) = fold-perm-adequate n (bg Function.∘ Fin.suc) i
\end{code}

Last but not least, build the left adjoint:

\begin{code}
module FreeCommMonoid = BuildLeftAdjoint ListMS ListCMHom
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
