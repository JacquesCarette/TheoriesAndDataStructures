module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; _≟_; _≤_; _+_; z≤n; s≤s; module ≤-Reasoning)
open import Data.Vec using (Vec; lookup; []; _∷_; map; _∈_; here; there) renaming (sum to vsum)
open import Data.Fin using (Fin; zero)
open import Data.Nat.Properties

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_ ; const)
open import Function2 using (_$ᵢ)

open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Relation.Binary.PropositionalEquality using (inspect; [_])

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

record Multiset {ℓ : Level} (X : Set ℓ) : Set ℓ where
  constructor MS
  field
    size : ℕ
    Carrier : Vec (X × ℕ) size 
    inj : ∀ (i j : Fin size) → proj₁ (lookup i Carrier) ≡ proj₁ (lookup j Carrier) → i ≡ j

zeroMS : {ℓ : Level} (X : Set ℓ) → Multiset X
zeroMS X = MS 0 [] (λ {()})

open Multiset

weight : {ℓ : Level} {X : Set ℓ} → (m : Multiset X) → Vec ℕ (size m)
weight m = map (λ x → ℕ.suc (proj₂ x)) (Carrier m)

postulate
  _+M_ : {ℓ : Level} {X : Set ℓ} → Multiset X → Multiset X → Multiset X
  pres-pts-A : {ℓ : Level} {X : Set ℓ} (A B : Multiset X) (x : X) (n : ℕ) →
    (x , n) ∈ Carrier A → Σ ℕ (λ m → ((x , m) ∈ Carrier (A +M B)) × (n ≤ m))
  pres-pts-B : {ℓ : Level} {X : Set ℓ} (A B : Multiset X) (x : X) (n : ℕ) →
    (x , n) ∈ Carrier B → Σ ℕ (λ m → ((x , m) ∈ Carrier (A +M B)) × (n ≤ m))
  pres-weight : {ℓ : Level} {X : Set ℓ} (A B : Multiset X) →
    vsum (weight A) + vsum (weight B) ≡ vsum (weight (uncurry _+M_ (A , B)))

private
  module _ {ℓ : Level} {X : Set ℓ} (x : X) where
    sing-v : Vec (X × ℕ) 1
    sing-v = (x , 0) ∷ []
    
    sing-uniq : (i j : Fin 1) → proj₁ (lookup i sing-v) ≡ proj₁ (lookup j sing-v) → i ≡ j
    sing-uniq zero zero pf = ≡.refl
    sing-uniq zero (Fin.suc ()) pf
    sing-uniq (Fin.suc ()) j pf
    
singleton : {ℓ : Level} {X : Set ℓ} (x : X) → Multiset X
singleton {ℓ} {X} x = MS 1 (sing-v x) (sing-uniq {ℓ} {X} x)

open ≤-Reasoning

DecidableX : {ℓ : Level} → (X : Set ℓ) → Decidable (_≡_ {ℓ} {X})
DecidableX X x y with singleton x | inspect singleton x | singleton y | inspect singleton y | uncurry _+M_ (singleton x , singleton y) | inspect (uncurry _+M_) (singleton x , singleton y)
DecidableX X x y | .(MS 1 ((x , 0) ∷ []) _) | [ ≡.refl ] | .(MS 1 ((y , 0) ∷ []) _) | [ ≡.refl ] | (MS zero v inj₃) | [ eq ] = no (λ _ → ¬i+1+j≤i 0 (begin
  2 ≡⟨ pres-weight (singleton x) (singleton y) ⟩
  vsum (weight (singleton x +M singleton y)) ≡⟨ ≡.cong (λ z → vsum (weight z)) eq ⟩
  0 ∎))
DecidableX X x y | .(MS 1 ((x , 0) ∷ []) (sing-uniq x)) | [ ≡.refl ] | .(MS 1 ((y , 0) ∷ []) (sing-uniq y)) | [ ≡.refl ] | (MS (ℕ.suc zero) ((z , n) ∷ []) inj₃) | [ eq ] = yes (
  let x-pf = pres-pts-A (singleton x) (singleton y) x 0 here in
  {!!})
DecidableX X x y | .(MS 1 ((x , 0) ∷ []) (sing-uniq x)) | [ ≡.refl ] | .(MS 1 ((y , 0) ∷ []) (sing-uniq y)) | [ ≡.refl ] | (MS (ℕ.suc (ℕ.suc zero)) v inj₃) | [ eq ] = no {!!}
DecidableX X x y | .(MS 1 ((x , 0) ∷ []) (sing-uniq x)) | [ ≡.refl ] | .(MS 1 ((y , 0) ∷ []) (sing-uniq y)) | [ ≡.refl ] | (MS (ℕ.suc (ℕ.suc (ℕ.suc s))) v inj₃) | [ eq ] = no {!!}

MSMonoid : {ℓ : Level} → Set ℓ → CommMonoid {ℓ}
MSMonoid X = cmon (Multiset X) (zeroMS X) {!!} {!!} {!!} {!!} {!!}

{-
MultisetF : (ℓ : Level) → Functor (Sets ℓ) (MonoidCat ℓ)
MultisetF ℓ = record
  { F₀ = MSMonoid
  ; F₁ = λ f → hom {!!} {!!} {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

MultisetLeft : (ℓ : Level) → Adjunction (MultisetF ℓ) (Forget ℓ)
MultisetLeft ℓ = record
  { unit = record { η = λ X → {!!} ; commute = {!!} }
  ; counit = record
    { η = λ { X@(cmon A z _+_ _ _ _ _) → hom {!!} {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
-}
