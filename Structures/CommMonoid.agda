module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List using (List; _∷_ ; []; _++_; foldr; map)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_ ; const)
open import Function2 using (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties

record CommMonoid {ℓ} : Set (lsuc ℓ) where
  constructor cmon
  field 
    m : Set ℓ
    e : m
    _*_ : m → m → m
    left-unit : ∀ x → e * x ≡ x
    right-unit : ∀ x → x * e ≡ x
    assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    comm : ∀ x y → x * y ≡ y * x

open CommMonoid

record Homomorphism {ℓ} (A B : CommMonoid {ℓ}) : Set ℓ where
  constructor hom
  open CommMonoid A renaming (m to m₁; e to e₁; _*_ to _*₁_)
  open CommMonoid B renaming (m to m₂; e to e₂; _*_ to _*₂_) 
  field
    f : m₁ → m₂
    pres-e : f e₁ ≡ e₂ 
    pres-* : (x y : m₁) → f (x *₁ y) ≡ (f x) *₂ (f y)

MonoidAlg : ∀ {ℓ} → OneSortedAlg ℓ
MonoidAlg = record
  { Alg = CommMonoid
  ; Carrier = m
  ; Hom = Homomorphism
  ; mor = Homomorphism.f
  ; comp = λ F G → hom (f F ∘ f G)
                       (≡.trans (≡.cong (f F) (pres-e G)) (pres-e F))
                       (λ x y → ≡.trans (≡.cong (f F) (pres-* G x y)) (pres-* F (f G x) (f G y)))
  ; comp-is-∘ = ≐-refl
  ; Id = hom id ≡.refl (λ _ _ → ≡.refl)
  ; Id-is-id = ≐-refl
  }
  where open Homomorphism

MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat ℓ = oneSortedCategory ℓ MonoidAlg

Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ MonoidAlg

postulate
   MSRep : {ℓ : Level} → Set ℓ → Set ℓ
   singleton : {ℓ : Level} {X : Set ℓ} → (x : X) → MSRep X
   zero : {ℓ : Level} → {X : Set ℓ} → MSRep X
   sum-inv : {ℓ : Level} {X Y : Set ℓ} (f : X → Y) → MSRep X → MSRep Y
   union : {ℓ : Level} {X : Set ℓ} → MSRep X → MSRep X → MSRep X
   sum-with-mult : {ℓ : Level} (CM : CommMonoid {ℓ}) → MSRep (m CM) → m CM
   
Multiset : {ℓ : Level} → Set ℓ → CommMonoid {ℓ}
Multiset X = cmon (MSRep X) zero union {!!} {!!} {!!} {!!}

MultisetF : (ℓ : Level) → Functor (Sets ℓ) (MonoidCat ℓ)
MultisetF ℓ = record
  { F₀ = Multiset
  ; F₁ = λ f → hom (sum-inv f) {!!} {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

MultisetLeft : (ℓ : Level) → Adjunction (MultisetF ℓ) (Forget ℓ)
MultisetLeft ℓ = record
  { unit = record { η = λ X → λ (x : X) → singleton x ; commute = {!!} }
  ; counit = record
    { η = λ { X@(cmon A z _+_ _ _ _ _) → hom (sum-with-mult X) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
