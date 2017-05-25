module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_ ; const)
open import Function.Equality using (_⟶_; _⟨$⟩_)
  renaming (id to idF; _∘_ to _⊚_)
open import Function2 using (_$ᵢ)

open import Data.List using (List; []; _++_; _∷_; foldr)
  renaming (map to mapL)
open import Data.List.Any using (Any; module Membership-≡)
open Membership-≡ using (_∈_)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Equiv using (_≃_; id≃; sym≃; trans≃)

record CommMonoid {ℓ} : Set (lsuc ℓ) where
  constructor cmon
  field
    s : Setoid ℓ ℓ

  open Setoid s renaming (Carrier to m) public
  
  field 
    e : m
    _*_ : m → m → m
    left-unit : ∀ x → e * x ≈ x
    right-unit : ∀ x → x * e ≈ x
    assoc : ∀ x y z → (x * y) * z ≈ x * (y * z)
    comm : ∀ x y → x * y ≈ y * x

record Homomorphism {ℓ} (A B : CommMonoid {ℓ}) : Set ℓ where
  constructor hom
  open CommMonoid A renaming (s to s₁; m to m₁; e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B renaming (s to s₂; m to m₂; e to e₂; _*_ to _*₂_; _≈_ to _≈₂_) 
  field
    f : s₁ ⟶ s₂
    pres-e : f ⟨$⟩ e₁ ≈₂ e₂ 
    pres-* : (x y : m₁) → f ⟨$⟩ (x *₁ y) ≈₂ (f ⟨$⟩ x) *₂ (f ⟨$⟩ y)
    
MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat ℓ = record
  { Obj = CommMonoid
  ; _⇒_ = Homomorphism
  ; _≡_ = λ {_} {B} F G → ∀ x → let open CommMonoid B in
            Homomorphism.f F ⟨$⟩ x ≈ Homomorphism.f G ⟨$⟩ x
  ; id = hom idF {!!} {!!}
  ; _∘_ = λ {(hom f₁ pres-e₁ pres-*₁) (hom f₂ pres-e₂ pres-*₂) →
              hom (f₁ ⊚ f₂) {!!} {!!}}
  ; assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; equiv = record { refl = {!!} ; sym = {!!} ; trans = {!!} }
  ; ∘-resp-≡ = {!!}
  }

Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀ = CommMonoid.m
  ; F₁ = λ { (hom f _ _) → λ x → f ⟨$⟩ x}
  ; identity = ≡.refl
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

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
MSMonoid {ℓ} X = cmon (MSetoid X) 0ₘ _+ₘ_ {!!} {!!} {!!} {!!}

MultisetF : (ℓ : Level) → Functor (Sets ℓ) (MonoidCat ℓ)
MultisetF ℓ = record
  { F₀ = MSMonoid
  ; F₁ = λ f → hom (record { _⟨$⟩_ = map f ; cong = {!!} }) {!!} {!!}
  ; identity = λ _ → {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

MultisetLeft : (ℓ : Level) → Adjunction (MultisetF ℓ) (Forget ℓ)
MultisetLeft ℓ = record
  { unit = record { η = λ X → singleton ; commute = singleton-map }
  ; counit = record
    { η = λ { X@(cmon A z _+_ _ _ _ _) →
          hom (record { _⟨$⟩_ = fold _+_ z ; cong = {!!} }) {!!} {!!} }
    ; commute = λ {(hom f _ _) x → {!!}}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
