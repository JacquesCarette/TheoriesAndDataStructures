module Structures.AbelianGroup where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′) renaming (map to map⊎)
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; swap; zip) renaming (map to map×)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Function2 using (_$ᵢ)
open import Equiv
open import Relation.Unary using (Pred; _∈_; _∪_; _∩_)
open import Data.Empty

open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≣_; refl to ≣-refl; sym to ≣-sym; cong to ≣-cong;
            trans to ≣-trans; cong₂ to ≣-cong₂)

open import Algebra hiding (Monoid)
open import Algebra.Structures

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; inject+; raise)
open import Data.Integer using (ℤ; _+_; +_; -_)
open import Data.Integer.Properties using (commutativeRing)

G1 : ∀ (c : Level) (A : Set c) → AbelianGroup c c
G1 c A = record
  { Carrier = A → ℤ
  ; _≈_ = _≐_
  ; _∙_ = λ h₁ h₂ a → h₁ a + h₂ a
  ; ε = λ _ → + 0
  ; _⁻¹ = λ h₁ a → - h₁ a
  ; isAbelianGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isEquivalence = ≐-isEquivalence
          ; assoc = λ h₁ h₂ h₃ a → AG.+-assoc (h₁ a) (h₂ a) (h₃ a)
          ; ∙-cong = λ x≡y u≡v a → AG.+-cong (x≡y a) (u≡v a)
          }
        ; identity = (λ h a → proj₁ AG.+-identity (h a)) , (λ h a → proj₂ AG.+-identity (h a))
        }
      ; inverse = (λ h a → proj₁ AG.-‿inverse (h a)) , (λ h a → proj₂ AG.-‿inverse (h a))
      ; ⁻¹-cong = λ i≡j a → ≣-cong (λ z → - z) (i≡j a)
      }
    ; comm = λ h₁ h₂ a → AG.+-comm (h₁ a) (h₂ a)
    }
  }
  where
    module AG = CommutativeRing commutativeRing

record GroupHom {o ℓ} (C D : AbelianGroup o ℓ) : Set (o ⊔ ℓ) where
  constructor abhom
  open AbelianGroup C renaming (Carrier to A; _∙_ to _+₁_; ε to 0₁; _⁻¹ to -₁_)
  open AbelianGroup D renaming (Carrier to B; _∙_ to _+₂_; ε to 0₂; _⁻¹ to -₂_)
  field
    h : A → B
    pres-+ : ∀ x y → h (x +₁ y) ≣ h x +₂ h y
    pres-0 : h 0₁ ≣ 0₂
    pres-inv : ∀ x → h (-₁ x) ≣ -₂ (h x)

AbelianGroupCat : ∀ o ℓ → Category (lsuc (o ⊔ ℓ)) (o ⊔ ℓ) o
AbelianGroupCat o ℓ = record
  { Obj = AbelianGroup o ℓ
  ; _⇒_ = GroupHom
  ; _≡_ = λ h₁ h₂ → h h₁ ≐ h h₂
  ; id = abhom idF (λ _ _ → ≣-refl) ≣-refl ≐-refl
  ; _∘_ = λ {(abhom h₁ p+₁ p0₁ pinv₁) (abhom h₂ p+₂ p0₂ pinv₂) →
              abhom (h₁ ◎ h₂) (λ x y → ≣-trans (≣-cong h₁ (p+₂ x y)) (p+₁ (h₂ x) (h₂ y)))
              (≣-trans (≣-cong h₁ p0₂) p0₁) (λ x → ≣-trans (≣-cong h₁ (pinv₂ x)) (pinv₁ (h₂ x))) }
  ; assoc = ≐-refl
  ; identityˡ = ≐-refl
  ; identityʳ = ≐-refl
  ; equiv = record { IsEquivalence ≐-isEquivalence}
  ; ∘-resp-≡ = ∘-resp-≐
  }
    where open AbelianGroup
          open GroupHom
          open import Relation.Binary using (IsEquivalence)

UG : ∀ o ℓ → Functor (AbelianGroupCat o ℓ) (Sets o)
UG o ℓ = record
  { F₀ = Carrier
  ; F₁ = λ { (abhom h _ _ _) → h }
  ; identity = ≣-refl
  ; homomorphism = ≣-refl
  ; F-resp-≡ = _$ᵢ
  }
  where open AbelianGroup

open import Function.Equality using (_⟨$⟩_)
open import Function.Injection using (Injection; _↣_; module Injection)
open import Data.Fin.Properties using ()

record DirectSum {o : Level} (A : Set o) : Set (lsuc o) where
  constructor FormalSum
  field
    f : A → ℤ
    B : Pred A o
    finite : Σ ℕ (λ n → (Σ A B ↣ Fin n))

open import Relation.Nullary using (¬_)

private
  -- why is this defined in Data.Fin.Properties but not exported?
  drop-suc : ∀ {o} {m n : Fin o} → Fin.suc m ≣ Fin.suc n → m ≣ n
  drop-suc ≣-refl = ≣-refl
  
  inject+-inject : ∀ {m n} → {i j : Fin m} → inject+ n i ≣ inject+ n j → i ≣ j
  inject+-inject {i = Fin.zero} {Fin.zero} ≣-refl = ≣-refl
  inject+-inject {i = Fin.zero} {Fin.suc _} ()
  inject+-inject {i = Fin.suc i} {Fin.zero} ()
  inject+-inject {i = Fin.suc i} {Fin.suc j} pf = ≣-cong Fin.suc (inject+-inject (drop-suc pf))

  raise-inject : ∀ {m n} → {i j : Fin m} → raise n i ≣ raise n j → i ≣ j
  raise-inject {n = ℕ.zero} pf = pf
  raise-inject {n = suc n} pf = raise-inject {n = n} (drop-suc pf)

  raise≢inject+ : (m n : ℕ) (i : Fin m) (j : Fin n) → ¬ (raise n i ≣ inject+ m j)
  raise≢inject+ m (suc n) i Fin.zero ()
  raise≢inject+ m _ i (Fin.suc j) eq = raise≢inject+ m _ i j (drop-suc eq)
  
  on-right₁ : {ℓ ℓ′ : Level} {A : Set ℓ} {B₁ B₂ : A → Set ℓ′} {a₁ a₂ : A} {b₁ : B₁ a₁} {b₂ : B₁ a₂} → (a₁ , b₁) ≣ (a₂ , b₂) → _≣_ {_} {Σ A (B₁ ∪ B₂)} (a₁ , inj₁ b₁) (a₂ , inj₁ b₂)
  on-right₁ ≣-refl = ≣-refl

  on-right₂ : {ℓ ℓ′ : Level} {A : Set ℓ} {B₁ B₂ : A → Set ℓ′} {a₁ a₂ : A} {b₁ : B₂ a₁} {b₂ : B₂ a₂} → (a₁ , b₁) ≣ (a₂ , b₂) → _≣_ {_} {Σ A (B₁ ∪ B₂)} (a₁ , inj₂ b₁) (a₂ , inj₂ b₂)
  on-right₂ ≣-refl = ≣-refl  

G2 : ∀ (c : Level) (A : Set c) → AbelianGroup (lsuc c) c
G2 c A = record
  { Carrier = DirectSum A
  ; _≈_ = λ a₁ a₂ → f a₁ ≐ f a₂
  ; _∙_ = λ { (FormalSum f₁ B₁ (n₁ , fin₁)) (FormalSum f₂ B₂ (n₂ , fin₂)) →
            FormalSum (λ a → f₁ a + f₂ a) (B₁ ∪ B₂)
                           (n₁ +ℕ n₂ , record { to = record { _⟨$⟩_ = λ { (a , inj₁ b) → inject+ n₂ (to fin₁ ⟨$⟩ (a , b))
                                                                        ; (a , inj₂ b) → raise n₁ (to fin₂ ⟨$⟩ (a , b))}
                                                       ; cong = λ { {i} {.i} ≣-refl → ≣-refl } }
                                               ; injective = λ { {(a₁ , inj₁ b₁)} {(a₂ , inj₁ b₂)} pf → on-right₁ (injective fin₁ (inject+-inject pf))
                                                               ; {(a₁ , inj₂ b₁)} {(a₂ , inj₁ b₂)} pf → ⊥-elim (raise≢inject+ _ _ _ _ pf)
                                                               ; {(a₁ , inj₁ b₁)} {(a₂ , inj₂ b₂)} pf → ⊥-elim (raise≢inject+ _ _ _ _ (≣-sym pf))
                                                               ; {(a₁ , inj₂ b₁)} {(a₂ , inj₂ b₂)} pf → on-right₂ (injective fin₂ (raise-inject {n = n₁} pf))
                                                               } }) }
  ; ε = FormalSum (λ _ → + 0) (λ _ → Lift ⊥) (0 , record { to = record { _⟨$⟩_ = λ {(_ , lift ())} ; cong = λ { {i} {.i} ≣-refl → ≣-refl } }
                                                         ; injective = λ { {(_ , lift ())} }})
  ; _⁻¹ = λ h₁ → FormalSum (λ a → - f h₁ a) (B h₁) (finite h₁)
  ; isAbelianGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isEquivalence = record { IsEquivalence ≐-isEquivalence}
          ; assoc = λ h₁ h₂ h₃ a → AG.+-assoc (f h₁ a) (f h₂ a) (f h₃ a)
          ; ∙-cong = λ x≡y u≡v a → AG.+-cong (x≡y a) (u≡v a)
          }
        ; identity = (λ h a → proj₁ AG.+-identity (f h a)) , (λ h a → proj₂ AG.+-identity (f h a))
        }
      ; inverse = (λ h a → proj₁ AG.-‿inverse (f h a)) , (λ h a → proj₂ AG.-‿inverse (f h a))
      ; ⁻¹-cong = λ i≡j a → ≣-cong (λ z → - z) (i≡j a)
      }
    ; comm = λ h₁ h₂ a → AG.+-comm (f h₁ a) (f h₂ a)
    }
  }
  where
    module AG = CommutativeRing commutativeRing
    open DirectSum
    open Injection
    open import Relation.Binary using (IsEquivalence)
