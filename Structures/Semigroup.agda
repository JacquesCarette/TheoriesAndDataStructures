module Structures.Semigroup where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; map; []; _∷_; _++_)

open import Function2 using (_$ᵢ)
open import EqualityCombinators
open import Forget

-----------
-- A Free Semigroup is a Non-empty list

record Semigroup {a} : Set (lsuc a) where
  constructor sg
  field
    A : Set a
    _*_ : A → A → A
    assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c

record Hom {ℓ} (C D : Semigroup {ℓ}) : Set ℓ where
  constructor hom
  open Semigroup C renaming (_*_ to _*₁_)
  open Semigroup D renaming (A to B; _*_ to _*₂_)
  field
    h : A → B
    pres-* : ∀ x y → h (x *₁ y) ≡ h x *₂ h y

private
  Alg : ∀ {ℓ} → OneSortedAlg ℓ
  Alg = record
          { Alg = Semigroup
          ; Carrier = A
          ; Hom = Hom
          ; mor = h
          ; comp = λ h₁ h₂ → hom (h h₁ ◎ h h₂) (λ x y → ≡.trans (≡.cong (h h₁) (pres-* h₂ x y)) (pres-* h₁ (h h₂ x) (h h₂ y)))
          ; comp-is-∘ = ≐-refl
          ; Id = hom idF (λ _ _ → ≡.refl)
          ; Id-is-id = ≐-refl
          }
      where open Semigroup
            open Hom
  
SemigroupCat : ∀ o → Category _ o o
SemigroupCat o = oneSortedCategory o Alg

Forget : ∀ o → Functor (SemigroupCat o) (Sets o)
Forget o = mkForgetful o Alg

NEList : {a : Level} → Set a → Set a
NEList A = A × List A

mapNE : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → NEList A → NEList B
mapNE f (x , l) = (f x) , map f l

{-
induct : ∀ {a c} {A : Set a} {P : Tree A → Set c}
  → ((x : A) → P (Leaf x)) → ({t₁ t₂ : Tree A} → P t₁ → P t₂ → P (Branch t₁ t₂))
  → (t : Tree A) → P t
induct         f g (Leaf x)     = f x
induct {P = P} f g (Branch s t) = g (induct {P = P} f g s) (induct {P = P} f g t)

fold : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → B → B) → Tree A → B
fold f g (Leaf x)      = f x
fold f g (Branch s t) = g (fold f g s) (fold f g t)
-}

concat : ∀ {a} {A : Set a} → NEList A → NEList A → NEList A
concat (x₀ , l₀) (x₁ , l₁) = (x₀ , l₀ ++ (x₁ ∷ l₁))

Free : ∀ o → Functor (Sets o) (SemigroupCat o)
Free o = record
  { F₀ = λ A → sg (NEList A) concat {!!}
  ; F₁ = λ f → hom (mapNE f) {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≡G → {!!}
  }

TreeLeft : ∀ o → Adjunction (Free o) (Forget o)
TreeLeft o = record
  { unit   = record { η = λ _ x → x , [] ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ {(sg A _*_ _) → hom {!!} {!!}} ; commute = {!!} }
  ; zig = {!!}
  ; zag = {!!} }

