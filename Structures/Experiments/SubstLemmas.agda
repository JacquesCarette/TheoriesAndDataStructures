{-# OPTIONS --without-K #-}

module SubstLemmas where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong₂) 
open import Data.Nat using (ℕ; _+_; _*_)

------------------------------------------------------------------------------
-- Lemmas about subst (and a couple about trans)

subst-dist : 
  {a b : Level} {A : Set a} {B : A → Set b} 
  (f : {x : A} → B x → B x → B x) → 
  {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → (v₁ v₂ : B x₂) → 
  subst B x₂≡x₁ (f v₁ v₂) ≡ f (subst B x₂≡x₁ v₁) (subst B x₂≡x₁ v₂)
subst-dist f refl v₁ v₂ = refl 

subst-trans : 
  {a b : Level} {A : Set a} {B : A → Set b} {x₁ x₂ x₃ : A} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₃≡x₂ : x₃ ≡ x₂) → (v : B x₃) →  
  subst B x₂≡x₁ (subst B x₃≡x₂ v) ≡ subst B (trans x₃≡x₂ x₂≡x₁) v
subst-trans refl refl v = refl

subst₂+ : {b : Level} {B : ℕ → Set b} {x₁ x₂ x₃ x₄ : ℕ} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₄≡x₃ : x₄ ≡ x₃) → (v₁ : B x₂) → (v₂ : B x₄) → 
  (f : {x₁ x₂ : ℕ} → B x₁ → B x₂ → B (x₁ + x₂)) → 
  subst B (cong₂ _+_ x₂≡x₁ x₄≡x₃) (f v₁ v₂) ≡ 
  f (subst B x₂≡x₁ v₁) (subst B x₄≡x₃ v₂)
subst₂+ refl refl v₁ v₂ f = refl

subst₂* : {b : Level} {B : ℕ → Set b} {x₁ x₂ x₃ x₄ : ℕ} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₄≡x₃ : x₄ ≡ x₃) → (v₁ : B x₂) → (v₂ : B x₄) → 
  (f : {x₁ x₂ : ℕ} → B x₁ → B x₂ → B (x₁ * x₂)) → 
  subst B (cong₂ _*_ x₂≡x₁ x₄≡x₃) (f v₁ v₂) ≡ 
  f (subst B x₂≡x₁ v₁) (subst B x₄≡x₃ v₂)
subst₂* refl refl v₁ v₂ f = refl

trans-syml : {A : Set} {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl
trans-syml refl = refl

trans-symr : {A : Set} {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symr refl = refl

subst-subst :
  {a b : Level} {A : Set a} {B : A → Set b}
  {x y : A} → (eq : x ≡ y) → (eq' : y ≡ x) → (irr : sym eq ≡ eq') →
  (v : B y) → subst B eq (subst B eq' v) ≡ v
subst-subst refl .refl refl v = refl

------------------------------------------------------------------------------
