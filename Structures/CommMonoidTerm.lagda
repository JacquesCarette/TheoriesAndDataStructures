%{{{ Imports
\begin{code}
module Structures.CommMonoidTerm where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; IsEquivalence;
  Reflexive; Symmetric; Transitive)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open import Function2         using (_$ᵢ)
open import Function          using () renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Equiv using (_≃_; id≃ ; sym≃ ; trans≃ ; _⊎≃_ ; _⟨≃≃⟩_ ; ≃-setoid ; ≃IsEquiv)
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\begin{code}
record CommMonoid {ℓ} {o} : Set (lsuc ℓ ⊍ lsuc o) where  
  constructor MkCommMon
  field setoid : Setoid ℓ o
  open Setoid setoid public

  field 
    e          : Carrier
    _*_        : Carrier → Carrier → Carrier
    left-unit  : {x : Carrier} → e * x ≈ x
    right-unit : {x : Carrier} → x * e ≈ x
    assoc      : {x y z : Carrier} → (x * y) * z ≈ x * (y * z)
    comm       : {x y : Carrier} → x * y ≈ y * x

  module ≈ = Setoid setoid

open CommMonoid hiding (_≈_)
infix -666 eq-in
eq-in = CommMonoid._≈_
syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

record Hom {ℓ} {o} (A B : CommMonoid {ℓ} {o}) : Set (ℓ ⊍ o) where
  constructor MkHom
  open CommMonoid A using () renaming (e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B using () renaming (e to e₂; _*_ to _*₂_; _≈_ to _≈₂_)

  field mor    : setoid A ⟶ setoid B
  private mor₀ = Π._⟨$⟩_ mor
  field
    pres-e : mor₀ e₁ ≈₂ e₂
    pres-* : {x y : Carrier A} → mor₀ (x *₁ y)  ≈₂  mor₀ x *₂ mor₀ y

  open Π mor public

open Hom
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.

%}}}

%{{{ MonoidCat ; Forget
\begin{code}
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (ℓ ⊍ o)
MonoidCat ℓ o = record
  { Obj = CommMonoid {ℓ} {o}
  ; _⇒_ = Hom
  ; _≡_ = λ {A} {B} F G → {x : Carrier A} → F ⟨$⟩ x ≈ G ⟨$⟩ x ∶ B
  ; id  = λ {A} → MkHom id (≈.refl A) (≈.refl A)
  ; _∘_ = λ {_} {_} {C} F G → record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  ≈.trans C (cong F (pres-e G)) (pres-e F)
    ; pres-*   =  ≈.trans C (cong F (pres-* G)) (pres-* F)
    }
  ; assoc     = λ { {D = D} → ≈.refl D}
  ; identityˡ = λ {A} {B} {F} {x} → ≈.refl B
  ; identityʳ = λ {A} {B} {F} {x} → ≈.refl B
  ; equiv     = λ {A} {B} → record
    { refl  = λ{F} {x} → ≈.refl B 
    ; sym   = λ {F} {G} F≈G {x} → ≈.sym B F≈G
    ; trans = λ {F} {G} {H} F≈G G≈H {x} → ≈.trans B F≈G G≈H
    }
  ; ∘-resp-≡ = λ {A} {B} {C} {F} {F'} {G} {G'} F≈F' G≈G' {x} → ≈.trans C (cong F G≈G') F≈F'
  }
\end{code}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ (o ⊍ ℓ)) (Setoids ℓ (o ⊍ ℓ))
Forget ℓ o = record
  { F₀             =   λ C → record { CommMonoid C }
  ; F₁             =   λ F → record { Hom F }
  ; identity       =   λ {A} → ≈.refl A
  ; homomorphism   =   λ {A} {B} {C} → ≈.refl C
  ; F-resp-≡      =   λ F≈G {x} → F≈G {x}
  }
\end{code}
%}}}

%{{{ Multiset

A “multiset on type X” is a commutative monoid with a to it from |X|.
For now, we make no constraints on the map, however it may be that
future proof obligations will require it to be an injection ---which is reasonable.

\begin{code}
record Multiset {ℓ o : Level} (X : Setoid ℓ o) : Set (lsuc ℓ ⊍ lsuc o) where
  field
    commMonoid : CommMonoid {ℓ} {ℓ ⊍ o}
    singleton : Setoid.Carrier X → CommMonoid.Carrier commMonoid
  open CommMonoid commMonoid public

open Multiset
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure.

\begin{code}
record MultisetHom {ℓ} {o} {X Y : Setoid ℓ o} (A : Multiset X) (B : Multiset Y) : Set (ℓ ⊍ o) where
  constructor MKMSHom
  field
    lift : (X ⟶ Y) → Hom (commMonoid A) (commMonoid B)

open MultisetHom
\end{code}

%}}}

\begin{code}

module _ {ℓ o : Level} (X : Setoid ℓ o) where

  X₀ = Setoid.Carrier X

  infix 5 _∙_
  infix 3 _≈ₜ_

  -- syntax of monoids over X
  data Term : Set ℓ where
    inj : X₀ → Term
    ε   : Term
    _∙_ : Term → Term → Term

  open Setoid X using () renaming (_≈_ to _≈ₓ_)

  data _≈ₜ_ : Term → Term → Set (ℓ ⊍ o) where
    -- This is an equivalence relation
    ≈ₜ-refl : {t : Term} → t ≈ₜ t
    ≈ₜ-sym  : {s t : Term} → s ≈ₜ t → t ≈ₜ s
    ≈ₜ-trans : {s t u : Term} → s ≈ₜ t → t ≈ₜ u → s ≈ₜ u
    -- where the commutative monoid laws hold
    ∙-cong : {s t u v : Term} → s ≈ₜ t → u ≈ₜ v → s ∙ u ≈ₜ t ∙ v
    ∙-assoc : {s t u : Term} → (s ∙ t) ∙ u ≈ₜ s ∙ (t ∙ u)
    ∙-comm  : {s t : Term} → s ∙ t ≈ₜ t ∙ s
    ∙-leftId : {s : Term} → ε ∙ s ≈ₜ s
    ∙-rightId : {s : Term} → s ∙ ε ≈ₜ s
    -- and it contains all equailities of the underlying setoid
    embed : {x y : X₀} → x ≈ₓ y → inj x ≈ₜ inj y
      --
      -- This means that we do NOT have unique proofs.
      -- For example, |inj x ≈ₜ inj x| can be proven in two ways: |≈ₜ-refl| or |embed ≈ₓ-refl|.
      --
      -- This may bite us in the butt; not necessarily though...

  LM : Setoid _ _
  LM = record
          { Carrier = Term
          ; _≈_ = _≈ₜ_
          ; isEquivalence = record
            { refl  =  ≈ₜ-refl
            ; sym   =  ≈ₜ-sym
            ; trans =  ≈ₜ-trans
            }
          }

  ListMS : Multiset X
  ListMS  = record
      { commMonoid = record
          { setoid     =  LM
          ; e          =  ε
          ; _*_        =  _∙_
          ; left-unit  =  ∙-leftId
          ; right-unit = ∙-rightId
          ; assoc      =  ∙-assoc
          ; comm       =  ∙-comm
          }
      ; singleton = inj
      }
      where

-- Term is functorial
term : {ℓ o : Level} {X Y : Setoid ℓ o} (F : X ⟶ Y) → (LM X) ⟶ (LM Y)
term {X = X} {Y} F = record { _⟨$⟩_ = helper ; cong = proof }
  where helper : Term X → Term Y
        helper (inj x) = inj (Π._⟨$⟩_ F x)
        helper ε = ε
        helper (s ∙ t) = helper s ∙ helper t

        proof : {s t : Term X} → _≈ₜ_ X s t → _≈ₜ_ Y (helper s) (helper t)
        proof ≈ₜ-refl = ≈ₜ-refl
        proof (≈ₜ-sym eq) = ≈ₜ-sym (proof eq)
        proof (≈ₜ-trans eq eq₁) = ≈ₜ-trans (proof eq) (proof eq₁)
        proof (∙-cong eq eq₁) = ∙-cong (proof eq) (proof eq₁)
        proof ∙-assoc = ∙-assoc
        proof ∙-comm = ∙-comm
        proof ∙-leftId = ∙-leftId
        proof ∙-rightId = ∙-rightId
        proof (embed x≈y) = embed (Π.cong F x≈y)

ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
ListCMHom X Y = MKMSHom (λ F → record
      { mor      =   term F
      ; pres-e   =   ≈ₜ-refl
      ; pres-*   =   ≈ₜ-refl
      })
\end{code}

{-
    fold : {X : Setoid ℓ o} {B : Set ℓ} →
      let A = Carrier X in
      (A → B → B) → B → Carrier (Multiset X) → B
    fold = foldr
    
    singleton-map : {A B : Setoid ℓ o} (f : A ⟶ B) {a : Setoid.Carrier A} →
      _≈_ (Multiset B) (singleton {B} (f ⟨$⟩ a)) (map (_⟨$⟩_ f) (singleton {A} a))
    singleton-map {_} {B} f = Setoid.refl (Multiset B)
-}

MultisetF : (ℓ o : Level) → Functor (Setoids ℓ o) (MonoidCat ℓ (ℓ ⊔ o))
MultisetF ℓ o = record
  { F₀ = λ S → commMonoid (ListMS S)
  ; F₁ = λ {X} {Y} f → let F = lift (ListCMHom X Y) f in record { Hom F }
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≈G → {!!}
  }
  where
    open Multiset; open MultisetHom
    
MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊔ ℓ)) (Forget ℓ (o ⊔ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = singleton (ListMS X)
                                     ; cong = {!!} }
                  ; commute = {!!} }
  ; counit = record
    { η = λ { X@(MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = {! fold _+_ z !} ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
  where
    open Multiset
    open CommMonoid
    


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
