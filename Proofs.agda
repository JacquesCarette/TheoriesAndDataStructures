{-# OPTIONS --without-K #-}

module Proofs where

-- Various general lemmas

open import Level using (Level)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)

-- re-open some sub-files 'public'

open import LeqLemmas       public
open import FinNatLemmas    public
open import FiniteFunctions public
open import VectorLemmas    public

------------------------------------------------------------------------------
-- Some generally useful functions

-- From Alan Jeffrey's post to Agda list

_⊨_⇒_≡_ : ∀ {I : Set} (F : I → Set) {i j} →
  (i ≡ j) → (F i) → (F j) → Set
(F ⊨ refl ⇒ x ≡ y) = (x ≡ y)

xcong : ∀ {I J F G} (f : I → J) (g : ∀ {i} → F i → G (f i)) →
  ∀ {i j} (i≡j : i ≡ j) {x y} →
    (F ⊨ i≡j ⇒ x ≡ y) → (G ⊨ cong f i≡j ⇒ g x ≡ g y)
xcong f g refl refl = refl

congD! : {a b : Level} {A : Set a} {B : A → Set b}
         (f : (x : A) → B x) → {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → 
         subst B x₂≡x₁ (f x₂) ≡ f x₁
congD! f refl = refl

-- Courtesy of Wolfram Kahl, a dependent cong₂                                  

cong₂D! : {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} 
         (f : (x : A) → B x → C)
       → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
       → (x₂≡x₁ : x₂ ≡ x₁) → subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
cong₂D! f refl refl = refl

inj-injective : ∀ {A B : Set} {a : A} {b : B} → inj₁ a ≡ inj₂ b → ⊥
inj-injective ()

------------------------------------------------------------------------------
