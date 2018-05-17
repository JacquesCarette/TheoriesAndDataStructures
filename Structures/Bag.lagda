\section{Structures.Bag}

This section is currently a copy of
|Structures.Multiset|, but it utilises |Sidequest2|'s permutation representation.

%{{{ Imports
\begin{code}
module Structures.Bag where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; _∘_) renaming (id to Id)
open import Function using () renaming (id to Id₀ ; _∘_ to _∘₀_)

-- open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)
-- open import Data.List.Properties using (map-++-commute; map-id; map-compose)

open import DataProperties hiding (⟨_,_⟩)
-- open import SetoidEquiv
open import ParComp
open import EqualityCombinators
open import Structures.CommMonoid renaming (Hom to _⟶̄_) -- |\-->\=|

open import Algebra   using (Monoid)
open import Data.List using (monoid)

open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open _⟶̄_    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
open CommMonoid using (eq-in ; isCommMonoid)
\end{code}
%}}}

%{{{ CtrSetoid
\subsection{CtrSetoid}

As will be explained below, the kind of ``container'' ---|ctr|--- used for
building a |Bag| needs to support a |Setoid|-polymorphic
equivalence relation.
\begin{code}
record IsCtrEquivalence {ℓ : Level} (c : Level) (Ctr : Set ℓ → Set ℓ)
  : Set (lsuc ℓ ⊍ lsuc c) where

  Obj = Setoid ℓ c

  field
    equiv        : (X : Obj) → Rel (Ctr (Setoid.Carrier X)) c
    equivIsEquiv : (X : Obj) → IsEquivalence (equiv X)

  -- handy dandy syntactic sugar for |k|ontainer equality.
  infix -666 equiv
  syntax equiv X s t  =  s ≈ₖ t ∶ X   -- ghost colon
  --
  -- The notation makes it even more explicit that the equivalence relations depend on a particular
  -- setoid object.
\end{code}

We have a type transformer |ctr| that furnishes setoids with an equivalence relation |equiv|.

Since there are no coherence constraints, we might as well say that this
|IsCtrEquivalence| is a setoid transformer: The object component of an endofunctor
on the category of setoids. Indeed:

\begin{code}
  ctrSetoid : Obj → Obj
  ctrSetoid X = record
    { Carrier        =  Ctr (Setoid.Carrier X)
    ; _≈_            =  equiv X
    ; isEquivalence  =  equivIsEquiv X
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
    𝒞                    : Set ℓ → Set ℓ         -- Carrier Mapping
    isCtrEquivalence     :  IsCtrEquivalence c 𝒞
    ∅                    :  {X : Set ℓ} → 𝒞 X
    _⊕_                  :  {X : Set ℓ} → 𝒞 X → 𝒞 X → 𝒞 X
    isCommutativeMonoid  :  {X : Setoid ℓ c} → IsCommutativeMonoid (equiv isCtrEquivalence X) _⊕_ ∅

  open IsCtrEquivalence isCtrEquivalence             public

  commMonoid : (X : Obj) → CommMonoid (ctrSetoid X)
  commMonoid X = record
    { e              =   ∅
    ; _*_            =   _⊕_
    ; isCommMonoid   =   isCommutativeMonoid
    }
\end{code}

%}}}

%{{{ Bag
\subsection{Bag}
A “bag on type X” is a structure on which one can define
\begin{itemize}
\item a \emph{commutative monoid} structure,
\item implement the concept of ``wrapping an element up as a \emph{singleton} container''
\item implement the concept of \emph{fold}; note that the name
is inspired by its implementation in the main model.  Its signature
would have suggested ``extract'', but this would have been
quite misleading. --c.f. the typing of |⟦_⟧| below.

  That is to say, we wish to have an operation |fold : ⦃x₁, …, xₙ⦄ ↦ x₁ ⊕ ⋯ ⊕ xₙ|
  where |⦃⋯⦄| are bag-comprehension brackets and so order is irrelevant, but multiplicity matters.

  Really, we are asking for a way to ``form finite sums'' on the bag.
\end{itemize}

\begin{code}
record Bag {ℓ c : Level} (X : Setoid ℓ c) : Set (lsuc ℓ ⊍ lsuc c) where
  field
    commutativeContainer : CommutativeContainer ℓ c

  open CommutativeContainer commutativeContainer     public
  open Setoid X using (_≈_) renaming (Carrier to X₀)

  field
    singleton       :  X ⟶ ctrSetoid X             -- A setoid map
    fold            :  {Y : Obj} (CMY : CommMonoid Y) →  commMonoid Y  ⟶̄  CMY
    fold-singleton  :  {CM : CommMonoid X} (x : X₀) → x ≈ fold CM ⟨$⟩ (singleton ⟨$⟩₀ x)


  -- Now for some syntactic variations.

  -- The name of the container type.
  𝒳 = 𝒞 X₀

  -- The bag notation |⦃_⦄| are some of the few reserved symbols in Agda.
  -- We shall use |⟅_⟆| as a workaround. Obtained: |\(| then selection number 9.
  --
  -- The bag's singleton embedding operation.
  ⟅_⟆ : X₀ → 𝒳
  ⟅_⟆ = singleton ⟨$⟩₀_

  -- The underlying commutative `M`onoid structure
  𝓜 : CommMonoid (ctrSetoid X)
  𝓜 = CommutativeContainer.commMonoid commutativeContainer X

  ⟦_⟧ : {Y : Obj} → CommMonoid Y → 𝒞 (Setoid.Carrier Y) → (Setoid.Carrier Y)
  ⟦ CMY ⟧ s = fold CMY ⟨$⟩ s

-- A |Bag| structure whose items are named by variations of the letter “s”, or by “t”.
--
-- Add "⦇" and "⦈" as unicode alternatives for "\(|" and "\|)" respectively.
-- ( Z NOTATION _ IMAGE BRACKET )
-- |M-x customize-variable agda-input-user-translations|
--
-- For some strange reason |⦇| cannot appear as part of an infix name.
--
-- As a work around, will use |⟦_⟧|.
--
module _ {ℓ c : Level} {X : Setoid ℓ c} (X* : Bag X) where

  module BagSrc where
    open Bag X* public using () renaming (⟅_⟆ to ⟅_⟆ₛ ; 𝓜 to 𝒮; ⟦_⟧ to ⟦_⟧ₛ; 𝒳 to 𝒮₀)

  module BagTgt where
    open Bag X* public using () renaming (⟅_⟆ to ⟅_⟆ₜ ; 𝓜 to 𝒯; ⟦_⟧ to ⟦_⟧ₜ; 𝒳 to 𝒯₀)
\end{code}

A “bag homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

In the classical contexts of sets and set-functions, the constraints take the form:
|{ f x } ≈ lift f { x }| and |fold (lift f s) ≈ f (fold s)|. In particular, the |lift| operation
mimics the behaviour of the morphism, or “map”, portion of a functor.

\begin{code}
record BagHom {ℓ c : Level} {Src Tgt : Setoid ℓ c} (Src* : Bag Src) (Tgt* : Bag Tgt)
  : Set (lsuc ℓ ⊍ lsuc c) where

  X₀ = Setoid.Carrier Src
  open Setoid Tgt using (_≈_)
  open BagSrc Src*
  open BagTgt Tgt*

  field
    lift : (Src ⟶ Tgt) →  𝒮 ⟶̄ 𝒯
    --
    -- MA: Perhaps request coherency via |Belongs.shifted-elements| ?
    -- E.g., |lift F xs ≅ shifted F xs| ?
    -- c.f. |Belongs.shift-map|!

    -- This ensures that |singleton| is sufficiently polymorphic; i.e., a natural transformation.
    -- See the Adjunction below.
    singleton-commute : (F : Src ⟶ Tgt) {x : X₀} → ⟅ F ⟨$⟩₀ x ⟆ₜ  ≈ lift F ⟨$⟩ ⟅ x ⟆ₛ  ∶  𝒯

    fold-commute : {CMX : CommMonoid Src} {CMY : CommMonoid Tgt} (𝑭 : CMX ⟶̄ CMY)
                 → {s : 𝒮₀}
                 → ⟦ CMY ⟧ₜ (lift (mor 𝑭) ⟨$⟩ s) ≈ 𝑭 ⟨$⟩ (⟦ CMX ⟧ₛ s)
                 -- MA: This is ``precisely'' the condition that |F| is a homomorphism!
                 -- Instead of requesting |F (x ⊕ y) ≈ F x ⊕ F y ∧ F ε ≈ ε|, we ask for
                 -- |F (x₁ ⊕ ⋯ ⊕ xₙ) ≈ F x₁ ⊕ ⋯ ⊕ F xₙ| for any |n : ℕ|.

open BagHom
\end{code}

\edcomm{MA}{

From Bird's theory of lists we know that every list homomorphism is the composition of a fold
after a map. Now a fold usually serves to realise an algebra as being initial and so least in some
sense.
As such, perhaps it'd be beneficial to request every |CMArrow (commMonoid Y) CMY| be expressible as
a |fold|?

}%edcomm

And now something somewhat different: To express that we have the right
functoriality properties (and ``zap''), we need to assume that we have
\emph{constructors} of |Bag| and |BagHom|.  With these in hand,
we can then phrase what extra properties must hold.  Because these properties
hold at ``different types'' than the ones for the underlying ones, these
cannot go into the above.
\begin{code}
record FunctorialMSH {ℓ c : Level}
    -- `B`ag type former ;; MS
    (𝑩 : (X : Setoid ℓ c) → Bag {ℓ} {c} X)

    -- Collection of bag `H`omomorphisms between given setoids.
    (𝑯 : {X Y : Setoid ℓ c} → BagHom {ℓ} {c} {X} {Y} (𝑩 X) (𝑩 Y))

    : Set (lsuc ℓ ⊍ lsuc c)
  where

  open Bag hiding (Obj)
  open BagHom
  open Setoid   using (Carrier)
  open IsCtrEquivalence hiding (ctrSetoid ; Obj)

  private
    Obj = Setoid ℓ c
    𝒞ₘ = λ X → 𝒞 {ℓ} {c} (𝑩 X) (Carrier X)
    𝓜ₘ = λ X → commMonoid {ℓ} {c} (𝑩 X) X

  𝑳  = λ {X Y : Obj}  (F : X ⟶ Y) → (lift 𝑯 F) ⟨$⟩_

  _≈ₘ_ : {a : Level} {A : Set a} {B : Obj} (f g : A → 𝒞ₘ B) → Set (a ⊍ c)
  _≈ₘ_ {a} {A} {B} f g = {e : A} → f e ≈ g e ∶ 𝓜ₘ B

  field
    -- Lifting the identity yields an identity morphism.
    id-pres : {X : Obj} → 𝑳 (Id {A = X}) ≈ₘ Id₀

    -- Lifting preserves composition.
    ∘-pres : {X Y Z : Obj} {F : X ⟶ Y} {G : Y ⟶ Z} → 𝑳 (G ∘ F) ≈ₘ (𝑳 G ∘₀ 𝑳 F)

    -- Lifting preserves extensional equality.
    resp-≈ : {X Y : Obj} {F G : X ⟶ Y} (let open Setoid Y renaming (_≈_ to _≈₀_))
          → (F≈G : {x : Carrier X} → F ⟨$⟩₀ x ≈₀ G ⟨$⟩₀ x) → 𝑳 F ≈ₘ 𝑳 G

    -- Lifting the singleton mapping then folding yields the orginal result.
    -- In particular, the singleton construction is injective --as we'd like.
    fold-lift-singleton : {X : Obj} (let ms = 𝑩 X ; _≈_ = equiv (isCtrEquivalence ms) X)
      → {s : 𝒞ₘ X} → s ≈ (fold (𝑩 (ctrSetoid ms X)) (𝓜ₘ X) ⟨$⟩ (𝑳 (singleton ms) s))
\end{code}
%}}}

%{{{ BuildLeftAdjoint
Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module BuildLeftAdjoint

  -- `B`ag type former ;; MS
  (𝑩   : {ℓ c : Level} (X : Setoid ℓ c) → Bag X)

  -- Collection of bag `H`omomorphisms between given setoids.
  (𝑯  : {ℓ c : Level} {X Y : Setoid ℓ c} → BagHom {ℓ} {c} (𝑩 X) (𝑩 {c = c} Y))

  (Func : {ℓ c : Level} → FunctorialMSH {ℓ} {c} 𝑩 𝑯)
  where

  open Bag
  open BagHom
  open FunctorialMSH

  Free : (ℓ c : Level) → Functor (Setoids ℓ (ℓ ⊍ c)) (MonoidCat ℓ (ℓ ⊍ c))
  Free _ _ = record
    { F₀             =   λ S → ctrSetoid (𝑩 S) S , commMonoid (𝑩 S) S
    ; F₁             =   λ F → record { _⟶̄_ (lift 𝑯 F) }
    ; identity       =   id-pres Func
    ; homomorphism   =   ∘-pres Func
    ; F-resp-≡       =   resp-≈ Func
    }

  LeftAdjoint : {ℓ o : Level} → Adjunction (Free ℓ o) (Forget ℓ (ℓ ⊍ o))
  LeftAdjoint = record
    { unit = record
      { η = λ X → singleton (𝑩 X)
      ; commute = singleton-commute 𝑯
      }
    ; counit = record
      { η        =  λ { (X , cm) → record { _⟶̄_ (fold (𝑩 X) cm) } }
      ; commute  =  fold-commute 𝑯
      }
    ; zig = fold-lift-singleton Func
    ; zag = λ { {X , CM} {m} → fold-singleton (𝑩 X) m }
    }
\end{code}
%}}}

%{{{ An implementation of |Bag| using lists with Bag equality
\subsection{An implementation of |Bag| using lists with Bag equality}
\begin{code}
module ImplementationViaList {ℓ o : Level} (X : Setoid ℓ o) where
  open Setoid
  module xx = Setoid X
  -- No: open ElemOfSing X

  open import Structures.Sidequest2


  open import Data.List
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold ; _≤_)

  ListMS : ℕ → Bag {ℓ} {o} X
  ListMS n = record
    { commutativeContainer = record
         { 𝒞                   = List
         ; isCtrEquivalence    = record
            { equiv        = λ Y → let open Permutations Y in {!!} -- _≈ₖ_
            ; equivIsEquiv = λ Y → let open Permutations Y in {!!}
            }
         ; ∅                   = [] -- c.f. |Sidequest.ε|
         ; _⊕_                 =  _++_ -- λ{ (_ , xs) (_ , ys) → (_ , xs ++ ys) } -- c.f. |Sidequest._⊕_|
         ; isCommutativeMonoid = λ {Y} →
           let open Permutations Y
               module ++ = Monoid (monoid (Carrier Y))
           in
           record
            { left-unit  = λ _ → {!!} -- ≈ₚ-refl -- c.f. |⊕-left-unit|
            ; right-unit = {!!} -- ≈ₚ-reflexive ∘₀ proj₂ ++.identity
            ; assoc      = λ xs ys zs → {!!} -- ≈ₚ-reflexive (++.assoc xs ys zs)
            ; comm       = λ xs ys → {!MA: If we could take inverses, then this would follow.
                                           However, as it stands, my inversion operator _˘ is flawed.!}
            ; _⟨∙⟩_      = λ {x} {y} {z} {w} x≈y z≈w → {!!}
            }
         }
    ; singleton = let open Permutations X in record { _⟨$⟩_ = λ x →  x ∷ []  ; cong = singleton-≈ }
    ; fold = λ {Y} CMY →
           let open CommMonoid CMY
               open Permutations Y
               -- open Lemmas CMY
           in record
         { mor      =   record { _⟨$⟩_ = {!!} ; cong = {!!} } -- record { _⟨$⟩_ = foldr _*_ e ; cong = fold-permute {CM = CMX} }
         ; pres-e   =   {!!} -- refl Y
         ; pres-*   =   {!!} -- fold-CM-over-++ CMX
         }
    ; fold-singleton = {!!} -- λ {CM} x → sym X (right-unit (isCommMonoid CM) x)
    }
\end{code}

\begin{spec}
  ListMS : Bag {ℓ} {o} X
  ListMS = record
    { commutativeContainer = record
         { 𝒞                   = List
         ; isCtrEquivalence    = record
            { equiv        = λ Y → let open BagEq Y in _⇔_
            ; equivIsEquiv = λ _ → record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
            }
         ; ∅                   = []
         ; _⊕_                 = _++_
         ; isCommutativeMonoid = λ {Y} →
           let
             open BagEq       Y   using   (≡→⇔)
             open Membership  Y   using   (elem-of)
             open ConcatTo⊎S  Y   using   (⊎S≅++)
             module ++ = Monoid (monoid (Carrier Y))
           in record
            { left-unit  = λ y → ≅-refl
            ; right-unit = λ ys → ≡→⇔ (proj₂ ++.identity ys)
            ; assoc      = λ xs ys zs → ≡→⇔ (++.assoc xs ys zs)
            ; comm       = λ xs ys →
               elem-of (xs ++ ys)         ≅˘⟨ ⊎S≅++ ⟩
               elem-of xs ⊎S elem-of ys   ≅⟨ ⊎S-comm _ _ ⟩
               elem-of ys ⊎S elem-of xs   ≅⟨ ⊎S≅++ ⟩
               elem-of (ys ++ xs)         ∎
            ; _⟨∙⟩_      = λ {x} {y} {z} {w} x⇔y z⇔w →
               elem-of (x ++ z)          ≅˘⟨ ⊎S≅++ ⟩
               elem-of x ⊎S elem-of z    ≅⟨ x⇔y ⊎S₁ z⇔w ⟩
               elem-of y ⊎S elem-of w    ≅⟨ ⊎S≅++ ⟩
               elem-of (y ++ w)          ∎
            }
         }
    ; singleton = record { _⟨$⟩_ = λ x → x ∷ [] ; cong = singleton-≈ }
    ; fold = λ {Y} CMX → let open CommMonoid CMX in record
         { mor      =   record { _⟨$⟩_ = foldr _*_ e ; cong = fold-permute {CM = CMX} }
         ; pres-e   =   refl Y
         ; pres-*   =   fold-CM-over-++ CMX
         }
    ; fold-singleton = λ {CM} x → sym X (right-unit (isCommMonoid CM) x)
    }
    where
       open IsCommutativeMonoid using (left-unit ; right-unit ; assoc) renaming (_⟨∙⟩_ to cong)
       open import Relation.Binary.SetoidReasoning renaming (_∎ to _■)

       fold-CM-over-++ : {Z : Setoid ℓ (o ⊍ ℓ)} (cm : CommMonoid Z) {s t : List (Carrier Z)}
                       →  let open CommMonoid cm ; F = foldr _*_ e in
                           F (s ++ t) ≈⌊ Z ⌋ (F s * F t)
       fold-CM-over-++ {Z} (MkCommMon e _*_ isCommMon) {[]} {t} = sym Z (left-unit isCommMon _)
       fold-CM-over-++ {Z} CMZ@(MkCommMon e _*_ isCommMon) {x ∷ s} {t} = begin⟨ Z ⟩
         let F = foldr _*_ e in
         x * F (s ++ t)   ≈⟨ cong isCommMon (refl Z) (fold-CM-over-++ CMZ ) ⟩
         x * (F s * F t)  ≈⟨ sym Z (assoc isCommMon _ _ _)                  ⟩
         (x * F s) * F t  ■

       -- to prove
       postulate cons-is-non-empty
                    : {Z : Setoid ℓ (o ⊍ ℓ)} {CM : CommMonoid Z} {x : Carrier Z} {s : List (Carrier Z)}
                        (let open BagEq Z)
                        → {a : Level} {Anything : Set a}
                        → (x ∷ s) ⇔ []
                        → Anything

       old-permute : {Z : Setoid ℓ (o ⊍ ℓ)} {CM : CommMonoid Z} {s t : List (Carrier Z)}
                      (let open BagEq Z ; open CommMonoid CM)
                    → s ⇔ t
                    → foldr _*_ e s ≈⌊ Z ⌋ foldr _*_ e t
       old-permute {Z} {CM} {s = []} {t} p with Belongs.BagEq.reflect-empty Z p
       old-permute {Z} {CM} {[]} {.[]} p | ≡.refl = Setoid.refl Z
       old-permute {Z} {CM} {s = x ∷ s} {[]} p = cons-is-non-empty {Z} {CM} p
       old-permute {Z} {CM} {s = x ∷ s} {y ∷ t} p = {!if x = y then indcution, otherwise?!}

       -- MA: Use Belongs.shifted-elements
       fold-permute : {Z : Setoid ℓ (o ⊍ ℓ)} {CM : CommMonoid Z} {s t : List (Carrier Z)}
                      (let open BagEq Z ; open CommMonoid CM)
                    → s ⇔ t
                    → foldr _*_ e s ≈⌊ Z ⌋ foldr _*_ e t
       fold-permute {Z} {MkCommMon e _*_ isCommMon} {s} {t} pf = BagEq.⇔-subst Z (foldr _*_ e) {_*_} (Setoid.refl Z) {! pres !} pf
         where open BagEq Z
               pres₀ : ∀{x y s} → (x ∷ s) ⇔ (y ∷ s) → Setoid._≈_ Z (x * foldr _*_ e s) (y * foldr _*_ e s)
               pres₀ {x} {y} {[]} pf₁ = {!!}
               pres₀ {x} {y} {x₁ ∷ s₁} pf₁ = {!!}
\end{spec}
               pres : ∀{x s y t} → (x ∷ s) ⇔ (y ∷ t) → Setoid._≈_ Z (x * foldr _*_ e s) (y * foldr _*_ e t)
               pres {x} {[]} {y} {t₁} q = {!!}
               pres {x} {a ∷ s} {y} {[]} q = {!!}
               pres {x} {a ∷ s₁} {y} {b ∷ t₁} record { to = to ; from = from ; inverse-of = inverse-of } = {!!}


\begin{spec}
      open Locations
      open Membership using (El)
      open ElemOf[]
      fold-permute : {Z : Setoid ℓ o} {CM : CommMonoid Z} {i j : List (Setoid.Carrier Z)} →
        let open BagEq Z in let open CommMonoid CM renaming (_*_ to _+_; e to e₁) in
        i ⇔ j → foldr _+_ e₁ i ≈⌊ Z ⌋ foldr _+_ e₁ j
      fold-permute {Z} {CM} {[]} {[]} i⇔j = Setoid.refl Z
      fold-permute {Z} {CM} {[]} {x ∷ j} i⇔j =
        ⊥-elim (elem-of-[] Z (_≅_.from i⇔j Π.⟨$⟩ El (here (Setoid.refl Z))))
      fold-permute {Z} {CM} {x ∷ i} {[]} i⇔j =
        ⊥-elim (elem-of-[] Z (_≅_.to i⇔j Π.⟨$⟩ El (here (Setoid.refl Z))))
      fold-permute {Z} {CM} {x ∷ i} {x₁ ∷ j} i⇔j = {!!}

ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ (ℓ ⊍ o))
  → BagHom {o = o} (ImplementationViaList.ListMS X) (ImplementationViaList.ListMS Y)
ListCMHom {ℓ} {o} X Y = record
  { lift = λ F → let g = Π._⟨$⟩_ F in record
    { mor = record
      { _⟨$⟩_ = mapL g
      ; cong = λ {xs} {ys} xs≈ys →
        elem-of (mapL g xs)   ≅⟨ shift-map F xs ⟩
        shifted F xs          ≅⟨ shifted-cong F xs≈ys ⟩
        shifted F ys          ≅˘⟨ shift-map F ys ⟩
        elem-of (mapL g ys) ∎
      }
    ; pres-e =
         elem-of []     ≅˘⟨ ⊥⊥≅elem-of-[] ⟩
         ⊥⊥             ≅⟨ ⊥⊥≅elem-of-[] ⟩
         (elem-of e₁) ∎

      -- in the proof below, *₀ and *₁ are both ++
    ; pres-* = λ {x} {y} →
      elem-of (mapL g (x *₀ y))           ≅⟨ ≡→⇔ (map-++-commute g x y) ⟩
      elem-of (mapL g x *₁ mapL g y) ∎
    }
  ; singleton-commute = λ f {x} → ≅-refl
  ; fold-commute = f-comm
  }
    where
      open ImplementationViaList
      open CommMonoid (Bag.commMonoid (ListMS X)) renaming (e to e₀; _*_ to _*₀_)
      open CommMonoid (Bag.commMonoid (ListMS Y)) renaming (e to e₁; _*_ to _*₁_)
      open Membership Y using (elem-of)
      open BagEq Y using (≡→⇔)
      open ElemOfMap
      open ElemOf[] Y
      f-comm : {W : CommMonoid X} {Z : CommMonoid Y} (f : Hom (X , W) (Y , Z))
        {lx : List (Setoid.Carrier X)} →
        Setoid._≈_ Y (foldr (CommMonoid._*_ Z) (CommMonoid.e Z) (mapL (Π._⟨$⟩_ (Hom.mor f)) lx))
                     (Hom.mor f Π.⟨$⟩ foldr (CommMonoid._*_ W) (CommMonoid.e W) lx)
      f-comm {MkCommMon e _*_ isCommMonoid₁} {MkCommMon e₂ _*₂_ isCM₂} f {[]} =
        Setoid.sym Y (Hom.pres-e f)
      f-comm {MkCommMon e _*_ isCommMonoid₁} {MkCommMon e₂ _*₂_ isCM₂} f {x ∷ lx} =
        let g = Π._⟨$⟩_ (Hom.mor f) in  begin⟨ Y ⟩
         ((g x) *₂ (foldr _*₂_ e₂ (mapL g lx)))  ≈⟨ refl ⟨∙⟩ f-comm f {lx} ⟩
         ((g x) *₂ (g (foldr _*_ e lx)))         ≈⟨ sym (Hom.pres-* f) ⟩
         (g (x * foldr _*_ e lx)) ■
        where
          open Setoid Y
          open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_; begin⟨_⟩_) renaming (_∎ to _■)
          open IsCommutativeMonoid isCM₂ using (_⟨∙⟩_)

module BuildProperties where
  open ImplementationViaList
  functoriality : {ℓ o : Level} → FunctorialMSH {ℓ} {o} ListMS ListCMHom
  functoriality {ℓ} {o} = record
    { id-pres = λ {X} {x} → BagEq.≡→⇔ X (map-id x)
    ; ∘-pres = λ {_} {_} {Z} {f} {g} {x} → BagEq.≡→⇔ Z (map-compose x)
    ; resp-≈ = λ {A} {B} {F} {G} F≈G {l} → respect-≈ {F = F} {G} F≈G l
    ; fold-lift-singleton = λ {X} {l} → BagEq.≡→⇔ X (concat-singleton l)
    }
    where
    open Membership
    open Locations using (here; there)
    open Setoid using (Carrier; trans; sym)
    open Bag using (Ctr; commMonoid)
    respect-≈ : {A B : Setoid ℓ (o ⊍ ℓ)} {F G : A ⟶ B}
      (F≈G : {x : Carrier A} → F Π.⟨$⟩ x ≈⌊ B ⌋ G Π.⟨$⟩ x)
      (lst : Ctr (ListMS A) (Carrier A))
      → mapL (Π._⟨$⟩_ F) lst ≈ mapL (Π._⟨$⟩_ G) lst ∶ commMonoid (ListMS B)
    respect-≈                 F≈G [] = ≅-refl
    respect-≈ {A} {B} {F} {G} F≈G (x ∷ lst) = record
      { to = record { _⟨$⟩_ = to-G ; cong = cong-to-G }
      ; from = record { _⟨$⟩_ = from-G ; cong = cong-from-G }
      ; inverse-of = record { left-inverse-of = left-inv ; right-inverse-of = right-inv } }
        where
          open LocEquiv B
          f = mapL (Π._⟨$⟩_ F)
          g = mapL (Π._⟨$⟩_ G)

          to-G : {l : List (Carrier A)} → elements B (f l) → elements B (g l)
          to-G {[]} (El ())
          to-G {_ ∷ _} (El (here sm)) = El (here (trans B sm F≈G))
          to-G {_ ∷ _} (El (there belongs)) = lift-el B there (to-G (El belongs))

          cong-to-G : {l : List (Carrier A)} {i j : elements B (f l)} → belongs i ≋ belongs j
            → belongs (to-G i) ≋ belongs (to-G j)
          cong-to-G {[]} ()
          cong-to-G {_ ∷ _} (hereEq x≈z y≈z) = LocEquiv.hereEq (trans B x≈z F≈G) (trans B y≈z F≈G)
          cong-to-G {_ ∷ _} (thereEq i≋j) = LocEquiv.thereEq (cong-to-G i≋j)

          from-G : {l : List (Carrier A)} → elements B (g l) → elements B (f l)
          from-G {[]} (El ())
          from-G {_ ∷ _} (El (here sm)) = El (here (trans B sm (sym B F≈G)))
          from-G {_ ∷ xs} (El (there x₁)) = lift-el B there (from-G (El x₁))

          cong-from-G : {l : List (Carrier A)} {i j : elements B (g l)} → belongs i ≋ belongs j
            → belongs (from-G i) ≋ belongs (from-G j)
          cong-from-G {[]} ()
          cong-from-G {_ ∷ _} (hereEq x≈z y≈z) = hereEq (trans B x≈z (sym B F≈G)) (trans B y≈z (sym B F≈G))
          cong-from-G {_ ∷ _} (thereEq loc₁) = thereEq (cong-from-G loc₁)

          left-inv : {l : List (Carrier A)} (y : elements B (mapL (Π._⟨$⟩_ F) l))
            → belongs (from-G (to-G y)) ≋ belongs y
          left-inv {[]} (El ())
          left-inv {_ ∷ _} (El (here sm)) = hereEq (trans B (trans B sm F≈G) (sym B F≈G)) sm
          left-inv {_ ∷ _} (El (there belongs₁)) = thereEq (left-inv (El belongs₁))

          right-inv : {l : List (Carrier A)} (y : elements B (mapL (Π._⟨$⟩_ G) l))
            → belongs (to-G (from-G y)) ≋ belongs y
          right-inv {[]} (El ())
          right-inv {_ ∷ _} (El (here sm)) = hereEq (trans B (trans B sm (sym B F≈G)) F≈G) sm
          right-inv {_ ∷ _} (El (there belongs₁)) = thereEq (right-inv (El belongs₁))
    concat-singleton : {X : Set ℓ} (lst : List X)
      → lst ≡ foldr _++_ [] (mapL (λ x → x ∷ []) lst)
    concat-singleton [] = ≡.refl
    concat-singleton (x ∷ lst) = ≡.cong (λ z → x ∷ z) (concat-singleton lst)
\end{spec}

Last but not least, build the left adjoint:

\begin{spec}
module FreeCommMonoid = BuildLeftAdjoint ImplementationViaList.ListMS ListCMHom
  BuildProperties.functoriality
\end{spec}
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
