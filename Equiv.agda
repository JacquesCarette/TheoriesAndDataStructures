{-# OPTIONS --without-K #-}

module Equiv where

open import Level using (_⊔_)
open import Function using (_∘_; id)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂) renaming (map to _×→_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

infix 4 _≐_
infix 3 _≃_
infixr 5 _●_

infix 8 _⊎≃_
infixr 7 _×≃_

------------------------------------------------------------------------------
-- Extensional equivalence of (unary) functions

_≐_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} → (f g : A → B) → Set (ℓ ⊔ ℓ')
_≐_ {A = A} f g = (x : A) → f x ≡ g x

≐-refl : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} → (f ≐ f)
≐-refl _ = refl

≐-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → (f ≐ g) → (g ≐ f)
≐-sym H x = sym (H x)

≐-trans : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → (f ≐ g) → (g ≐ h) → (f ≐ h)
≐-trans H G x = trans (H x)  (G x)

∘-resp-≐ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {f h : B → C} {g i : A → B} →
  (f ≐ h) → (g ≐ i) → f ∘ g ≐ h ∘ i
∘-resp-≐ {f = f} {i = i} f≐h g≐i x = trans (cong f (g≐i x)) (f≐h (i x)) 

≐-isEquivalence : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → IsEquivalence (_≐_ {ℓ} {ℓ′} {A} {B})
≐-isEquivalence = record { refl = ≐-refl ; sym = ≐-sym ; trans = ≐-trans }

-- generally useful
cong∘l : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
  {g i : A → B} → (f : B → C) →
  (g ≐ i) → (f ∘ g) ≐ (f ∘ i)
cong∘l f g~i x = cong f (g~i x)

cong∘r : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} 
  {f h : B → C} → (g : A → B) →
  (f ≐ h) → (f ∘ g) ≐ (h ∘ g)
cong∘r g f~h x = f~h (g x)

------------------------------------------------------------------------------
-- Quasi-equivalences a la HoTT:
record isqinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  constructor qinv
  field
    g : B → A
    α : (f ∘ g) ≐ id
    β : (g ∘ f) ≐ id

-- We explicitly choose quasi-equivalences, even though these
-- these are not a proposition.  This is fine for us, as we're
-- explicitly looking at equivalences-of-equivalences, and we
-- so we prefer a symmetric definition over a truncated one.

------------------------------------------------------------------------------
-- Equivalences between sets A and B: a function f and a quasi-inverse for f.

_≃_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isqinv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , qinv id (λ _ → refl) (λ _ → refl))

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , qinv A→B e.β e.α
  where module e = isqinv equiv

abstract
  trans≃ :  ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → A ≃ B → B ≃ C → A ≃ C
  trans≃ {A = A} {B} {C} (f , qinv f⁻¹ fα fβ) (g , qinv g⁻¹ gα gβ) = 
    (g ∘ f) , (qinv (f⁻¹ ∘ g⁻¹) (λ x → trans (cong g (fα (g⁻¹ x))) (gα x))
                                          (λ x → trans (cong f⁻¹ (gβ (f x))) (fβ x)))
  -- more convenient infix version, flipped
  _●_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → B ≃ C → A ≃ B → A ≃ C
  a ● b = trans≃ b a

  -- since we're abstract, these all us to do restricted expansion
  β₁ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {f : B ≃ C} {g : A ≃ B} →
    proj₁ (f ● g) ≐ (proj₁ f ∘ proj₁ g)
  β₁ x = refl

  β₂ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {f : B ≃ C} {g : A ≃ B} →
    isqinv.g (proj₂ (f ● g)) ≐ (isqinv.g (proj₂ g) ∘ (isqinv.g (proj₂ f)))
  β₂  x = refl

≃IsEquiv : {ℓ : Level.Level} → IsEquivalence {Level.suc ℓ} {ℓ} {Set ℓ} _≃_
≃IsEquiv = record { refl = id≃ ; sym = sym≃ ; trans = trans≃ }

-- useful throughout below as an abbreviation
gg : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → (B → A)
gg z = isqinv.g (proj₂ z)

-- equivalences are injective

inj≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (eq : A ≃ B) → (x y : A) → (proj₁ eq x ≡ proj₁ eq y → x ≡ y)
inj≃ (f , qinv g α β) x y p = trans
  (sym (β x)) (trans
  (cong g p) (
  β y))

-- equivalence is a congruence for plus/times

-- ⊕

abstract
  private
    _⊎≐_ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
      {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
      (α : f ∘ finv ≐ id) → (β : g ∘ ginv ≐ id) →
      (f ⊎→ g) ∘ (finv ⊎→ ginv) ≐ id {A = C ⊎ D}
    _⊎≐_ α β (inj₁ x) = cong inj₁ (α x)
    _⊎≐_ α β (inj₂ y) = cong inj₂ (β y)

  _⊎≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
  (fp , eqp) ⊎≃ (fq , eqq) =
    Data.Sum.map fp fq ,
    qinv (P.g ⊎→ Q.g) (P.α ⊎≐ Q.α) (P.β ⊎≐ Q.β)
    where module P = isqinv eqp
          module Q = isqinv eqq

  β⊎₁ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → proj₁ (f ⊎≃ g) ≐ Data.Sum.map (proj₁ f) (proj₁ g)
  β⊎₁ _ = refl

  β⊎₂ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → gg (f ⊎≃ g) ≐ Data.Sum.map (gg f) (gg g)
  β⊎₂ _ = refl

-- ⊗

abstract
  private
    _×≐_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
      {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
      (α : f ∘ finv ≐ id) → (β : g ∘ ginv ≐ id) →
      (f ×→ g) ∘ (finv ×→ ginv) ≐ id {A = C × D}
    _×≐_ α β (x , y) = cong₂ _,_ (α x) (β y)

  _×≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
  (fp , eqp) ×≃ (fq , eqq) =
    Data.Product.map fp fq ,
    qinv
      (P.g ×→ Q.g)
      (_×≐_ {f = fp} {g = fq} P.α Q.α)
      (_×≐_ {f = P.g} {g = Q.g} P.β Q.β)
    where module P = isqinv eqp
          module Q = isqinv eqq

  β×₁ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → proj₁ (f ×≃ g) ≐ Data.Product.map (proj₁ f) (proj₁ g)
  β×₁ _ = refl

  β×₂ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → gg (f ×≃ g) ≐ Data.Product.map (gg f) (gg g)
  β×₂ _ = refl

------------------------------------------------------------------------------
