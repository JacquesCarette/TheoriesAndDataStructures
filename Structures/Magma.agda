module Structures.Magma where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Data.Empty

open import Function2 using (_$ᵢ)
open import Equiv
open import Forget

open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≣_; refl to ≣-refl; sym to ≣-sym; cong to ≣-cong;
            trans to ≣-trans; cong₂ to ≣-cong₂)

-----------
-- A Free Magma is a binary tree.

record Magma {a} : Set (lsuc a) where
  constructor mag
  field
    A : Set a
    _*_ : A → A → A
    
record Hom {ℓ} (C D : Magma {ℓ}) : Set ℓ where
  constructor hom
  open Magma C renaming (_*_ to _*₁_)
  open Magma D renaming (A to B; _*_ to _*₂_)
  field
    h : A → B
    pres-* : ∀ x y → h (x *₁ y) ≣ h x *₂ h y

private
  Alg : ∀ {ℓ} → OneSortedAlg {ℓ}
  Alg = record
          { Alg = Magma
          ; obj = A
          ; Hom = Hom
          ; func = h
          ; comp = λ h₁ h₂ → hom (h h₁ ◎ h h₂) (λ x y → ≣-trans (≣-cong (h h₁) (pres-* h₂ x y)) (pres-* h₁ (h h₂ x) (h h₂ y)))
          ; o-is-∘ = refl∼
          ; idH = hom idF (λ _ _ → ≣-refl)
          ; idH-is-id = refl∼
          }
      where open Magma
            open Hom
  
MagmaCat : ∀ o → Category _ o o
MagmaCat o = oneSorted o Alg

Forget : ∀ o → Functor (MagmaCat o) (Sets o)
Forget o = mkForgetful o Alg

data Tree {a : Level} (A : Set a) : Set a where
 Leaf : A → Tree A
 Branch : Tree A → Tree A → Tree A

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Tree A → Tree B
map f (Leaf x)      = Leaf (f x)
map f (Branch s t) = Branch (map f s) (map f t)

induct : ∀ {a c} {A : Set a} {P : Tree A → Set c}
  → ((x : A) → P (Leaf x)) → ({t₁ t₂ : Tree A} → P t₁ → P t₂ → P (Branch t₁ t₂))
  → (t : Tree A) → P t
induct         f g (Leaf x)     = f x
induct {P = P} f g (Branch s t) = g (induct {P = P} f g s) (induct {P = P} f g t)

fold : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → B → B) → Tree A → B
fold f g (Leaf x)      = f x
fold f g (Branch s t) = g (fold f g s) (fold f g t)

TreeF : ∀ o → Functor (Sets o) (MagmaCat o)
TreeF o = record
  { F₀ = λ A → mag (Tree A) Branch
  ; F₁ = λ f → hom (map f) (λ _ _ → ≣-refl)
  ; identity = induct refl∼ (≣-cong₂ Branch)
  ; homomorphism = induct refl∼ (≣-cong₂ Branch)
  ; F-resp-≡ = λ F≡G → induct (λ _ → ≣-cong Leaf F≡G) (≣-cong₂ Branch)
  }

TreeLeft : ∀ o → Adjunction (TreeF o) (Forget o)
TreeLeft o = record
  { unit = record { η = λ _ → Leaf ; commute = λ _ → ≣-refl }
  ; counit = record { η = λ { (mag _ _+_) → hom (fold idF _+_) (λ _ _ → ≣-refl) }
                    ; commute = λ { {mag _ _*₁_} {mag _ _*₂_} (hom f pres-*) →
                        induct refl∼ (λ {t₁} {t₂} p₁ p₂ → ≣-trans (≣-cong₂ _*₂_ p₁ p₂) (≣-sym (pres-* (fold idF _*₁_ t₁)  (fold idF _*₁_ t₂)))) } }
  ; zig = induct refl∼ (≣-cong₂ Branch)
  ; zag = ≣-refl }

-- Looks like there is no right adjoint, because its binary constructor would have to anticipate
-- all magma _*_, so that "singleton (x * y)" has to be the same as "Binary x y".

