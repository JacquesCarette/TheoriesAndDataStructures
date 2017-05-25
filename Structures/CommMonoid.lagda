%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)

open import Function.Equality using (_⟶_; _⟨$⟩_ ; cong ; id ; _∘_)
open import Function2         using (_$ᵢ)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)
open import Data.List.Any using (Any; module Membership-≡)
open Membership-≡         using (_∈_)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Equiv using (_≃_; id≃; sym≃; trans≃)
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\begin{code}
record CommMonoid {ℓ} : Set (lsuc ℓ) where  
  constructor MkCommMon
  field setoid : Setoid ℓ ℓ
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

record Hom {ℓ} (A B : CommMonoid {ℓ}) : Set ℓ where
  constructor MkHom
  open CommMonoid A using () renaming (e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B using () renaming (e to e₂; _*_ to _*₂_; _≈_ to _≈₂_) 
  field
    mor    : setoid A ⟶ setoid B
    pres-e : mor ⟨$⟩ e₁ ≈₂ e₂
    pres-* : {x y : Carrier A} → mor ⟨$⟩ (x *₁ y) ≈₂ (mor ⟨$⟩ x) *₂ (mor ⟨$⟩ y)

open Hom
\end{code}
%}}}

%{{{ MonoidCat
\begin{code}
MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat ℓ = record
  { Obj = CommMonoid
  ; _⇒_ = Hom
  ; _≡_ = λ {A} {B} F G → {x : Carrier A} → mor F ⟨$⟩ x ≈ mor G ⟨$⟩ x ∶ B
  ; id  = λ {A} → MkHom id (≈.refl A) (≈.refl A)
  ; _∘_ = λ {A} {B} {C} F G → record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  ≈.trans C (cong (mor F) (pres-e G)) (pres-e F)
    ; pres-*   =  ≈.trans C (cong (mor F) (pres-* G)) (pres-* F)
    }
  ; assoc     = λ {A} {B} {C} {D} {F} {G} {H} {x} → ≈.refl D
  ; identityˡ = λ {A} {B} {F} {x} → ≈.refl B
  ; identityʳ = λ {A} {B} {F} {x} → ≈.refl B
  ; equiv     = λ {A} {B} → record
    { refl  = λ{F} {x} → ≈.refl B 
    ; sym   = λ {F} {G} F≈G {x} → ≈.sym B F≈G
    ; trans = λ {F} {G} {H} F≈G G≈H {x} → ≈.trans B F≈G G≈H
    }
  ; ∘-resp-≡ = λ {A} {B} {C} {F} {F'} {G} {G'} F≈F' G≈G' {x} → ≈.trans C (cong (mor F) G≈G') F≈F'
  }
\end{code}
%}}}

\begin{code}
Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀ = CommMonoid.Carrier
  ; F₁ = λ F → λ x → mor F ⟨$⟩ x
  ; identity = ≡.refl
  ; homomorphism = λ {A} {B} {C} {F} {G} {x} → ≡.refl
  ; F-resp-≡ = λ {A} {B} {F} {G} F≈G {x} → {!F≈G ?!}
  }
  -- equivalent functions aren't necessarily extensionally-identical functions

module _ {ℓ : Level} where
  abstract
    Multiset : Set ℓ → Set ℓ
    Multiset X = List X

    _≈ₘ_ : {X : Set ℓ} → Multiset X → Multiset X → Set ℓ
    m₁ ≈ₘ m₂ = ∀ x → (x ∈ m₁) ≃ (x ∈ m₂)

    0ₘ : {X : Set ℓ} → Multiset X
    0ₘ = []

    refl≈ : {X : Set ℓ} → Reflexive (_≈ₘ_ {X})
    refl≈ _ = id≃

    sym≈ : {X : Set ℓ} → Symmetric (_≈ₘ_ {X})
    sym≈ s = λ x → sym≃ (s x)
    
    map : {A B : Set ℓ} → (A → B) → Multiset A → Multiset B
    map = mapL

    singleton : {X : Set ℓ} → X → Multiset X
    singleton x = x ∷ []

    fold : {A B : Set ℓ} → (A → B → B) → B → Multiset A → B
    fold = foldr
    
    singleton-map : {X Y : Set ℓ} (f : X → Y) {x : X} →
      singleton (f x) ≡ map f (singleton x)
    singleton-map f = ≡.refl

    _+ₘ_ : {X : Set ℓ} → Multiset X → Multiset X → Multiset X
    m₁ +ₘ m₂ = m₁ ++ m₂
    
  MSetoid : Set ℓ → Setoid ℓ ℓ
  MSetoid X = record { Carrier = Multiset X ; _≈_ = _≈ₘ_
      ; isEquivalence = record
        { refl = refl≈
        ; sym = sym≈
        ; trans = {!!} } }

MSMonoid : {ℓ : Level} → Set ℓ → CommMonoid {ℓ}
MSMonoid {ℓ} X = MkCommMon (MSetoid X) 0ₘ _+ₘ_ {!!} {!!} {!!} {!!}

MultisetF : (ℓ : Level) → Functor (Sets ℓ) (MonoidCat ℓ)
MultisetF ℓ = record
  { F₀ = MSMonoid
  ; F₁ = λ f → MkHom (record { _⟨$⟩_ = map f ; cong = {!!} }) {!!} {!!}
  ; identity = {!!} -- λ _ → {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

MultisetLeft : (ℓ : Level) → Adjunction (MultisetF ℓ) (Forget ℓ)
MultisetLeft ℓ = record
  { unit = record { η = λ X → singleton ; commute = singleton-map }
  ; counit = record
    { η = λ { X@(MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = fold _+_ z ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!} -- λ {(MkHom f _ _) x → {!!}}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
\end{code}

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
