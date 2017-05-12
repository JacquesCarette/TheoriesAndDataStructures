module Structures.TwoSorted where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; [_,_]) renaming (map to map⊎)

open import Function2 using (_$ᵢ)
open import Equiv
open import Forget

open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≣_; refl to ≣-refl; sym to ≣-sym; cong to ≣-cong;
            trans to ≣-trans; cong₂ to ≣-cong₂)

-----------
-- A Free TwoSorted container is a ?.

record TwoSorted {a} : Set (lsuc a) where
  constructor two
  field
    A : Set a
    B : Set a
    
record Hom {ℓ} (C D : TwoSorted {ℓ}) : Set ℓ where
  constructor hom
  open TwoSorted C renaming (A to A₁; B to B₁)
  open TwoSorted D renaming (A to A₂; B to B₂)
  field
    h₁ : A₁ → A₂
    h₂ : B₁ → B₂

TwoCat : ∀ o → Category (lsuc o) o o
TwoCat o = record
  { Obj = TwoSorted {o}
  ; _⇒_ = Hom
  ; _≡_ = λ { {A} {B} (hom g₁ g₂) (hom h₁ h₂) → (g₁ ≐ h₁) × (g₂ ≐ h₂)}
  ; id = hom idF idF
  ; _∘_ = λ { (hom h₁ h₂) (hom g₁ g₂) → hom (h₁ ◎ g₁) (h₂ ◎ g₂)}
  ; assoc = ≐-refl , ≐-refl
  ; identityˡ = ≐-refl , ≐-refl
  ; identityʳ = ≐-refl , ≐-refl
  ; equiv = record { refl = ≐-refl , ≐-refl
                   ; sym = λ { (i≡j₁ , i≡j₂)  → ≐-sym i≡j₁ , ≐-sym i≡j₂ }
                   ; trans = λ { (i≡j₁ , i≡j₂) (j≡k₁ , j≡k₂) → (≐-trans i≡j₁ j≡k₁) , (≐-trans i≡j₂ j≡k₂)} }
  ; ∘-resp-≡ = λ g≡i f≡h → ∘-resp-≐ (proj₁ g≡i) (proj₁ f≡h) , ∘-resp-≐ (proj₂ g≡i) (proj₂ f≡h)
  }

Forget : ∀ o → Functor (TwoCat o) (Sets o)
Forget o = record
  { F₀ = TwoSorted.A
  ; F₁ = Hom.h₁
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  ; F-resp-≡ = λ x {y} → proj₁ x y
  }

open import Data.Empty
open import Data.Unit

Free : ∀ o → Functor (Sets o) (TwoCat o)
Free o = record
  { F₀ = λ A → two A (Lift ⊥)
  ; F₁ = λ f → hom f idF
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → ( λ x → F≡G {x}) , ≐-refl
  }

Cofree : ∀ o → Functor (Sets o) (TwoCat o)
Cofree o = record
  { F₀ = λ A → two A (Lift ⊤)
  ; F₁ = λ f → hom f idF
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → ( λ x → F≡G {x}) , ≐-refl
  }

Left : ∀ o → Adjunction (Free o) (Forget o)
Left o = record
  { unit   = record { η = λ X x → x ; commute = λ _ → ≣-refl }
  ; counit = record { η = λ { (two A B) → hom idF (λ { (lift ()) }) }
                    ; commute = λ f → ≐-refl , (λ { (lift ())}) }
  ; zig = ≐-refl , (λ { (lift ()) })
  ; zag = ≣-refl }

Right :  ∀ o → Adjunction (Forget o) (Cofree o)
Right o = record
  { unit = record { η = λ { (two A B) → hom idF (λ _ → lift tt) }
                  ; commute = λ f → ≐-refl , ≐-refl }
  ; counit = record { η = λ _ → idF ; commute = λ _ → ≣-refl }
  ; zig = ≣-refl
  ; zag = ≐-refl , (λ {(lift tt) → ≣-refl }) }

Merge : ∀ o → Functor (TwoCat o) (Sets o)
Merge o = record
  { F₀ = λ S → A S × B S
  ; F₁ = λ {(hom h₁ h₂) (a₁ , b₁) → (h₁ a₁) , (h₂ b₁)}
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  ; F-resp-≡ = λ {(F≡G₁ , F≡G₂) {x} → ≣-cong₂ _,_ (F≡G₁ (proj₁ x)) (F≡G₂ (proj₂ x))}
  }
  where open TwoSorted

Dup : ∀ o → Functor (Sets o) (TwoCat o)
Dup o = record
  { F₀ = λ A → two A A
  ; F₁ = λ f → hom f f
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → (λ x → F≡G {x}) , λ _ → F≡G
  }

Right₂ : ∀ o → Adjunction (Dup o) (Merge o)
Right₂ o = record
  { unit = record { η = λ X x → x , x ; commute = λ f → ≣-refl }
  ; counit = record { η = λ {(two A B) → hom proj₁ proj₂} ; commute = λ {(hom f g) → ≐-refl , ≐-refl} }
  ; zig = ≐-refl , ≐-refl
  ; zag = ≣-refl }

Choice : ∀ o → Functor (TwoCat o) (Sets o)
Choice o = record
  { F₀ = λ S → A S ⊎ B S
  ; F₁ = λ { (hom f g) → map⊎ f g}
  ; identity = λ {_} → λ { {(inj₁ x)} → ≣-refl ; {(inj₂ x)} → ≣-refl}
  ; homomorphism = λ { {x = (inj₁ x)} → ≣-refl ; {x = (inj₂ x)} → ≣-refl}
  ; F-resp-≡ = {!!} -- λ { ( F≡G₁ , F≡G₂ ) → λ { {(inj₁ x)} → ≣-cong inj₁ (F≡G₁ x) ; {(inj₂ x)} → ≣-cong inj₂ (F≡G₂ x)}}
  }
  where open TwoSorted

from⊎ : ∀ {ℓ} {A : Set ℓ} → A ⊎ A → A
from⊎ = [ idF , idF ]′

Left₂ : ∀ o → Adjunction (Choice o) (Dup o)
Left₂ o = record
  { unit   = record { η = λ {(two A B) → hom inj₁ inj₂} ; commute = λ f → ≐-refl , ≐-refl }
           ; counit = record { η = λ _ → from⊎ ; commute = λ f → λ { { (inj₁ x) } → ≣-refl ; {(inj₂ x)} → ≣-refl}}
  ; zig = λ {_} → λ { {(inj₁ x)} → ≣-refl ; {(inj₂ x)} → ≣-refl}
  ; zag = ≐-refl , ≐-refl }
