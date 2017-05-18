module Structures.Monoid where

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

record Monoid {ℓ} : Set (lsuc ℓ) where
  constructor mon
  field 
    m : Set ℓ
    e : m
    _*_ : m → m → m
    left-unit : ∀ x → e * x ≡ x
    right-unit : ∀ x → x * e ≡ x
    assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)

record Homomorphism {ℓ} (A B : Monoid {ℓ}) : Set ℓ where
  constructor hom
  open Monoid A renaming (m to m₁; e to e₁; _*_ to _*₁_)
  open Monoid B renaming (m to m₂; e to e₂; _*_ to _*₂_) 
  field
    f : m₁ → m₂
    pres-e : f e₁ ≡ e₂ 
    pres-* : (x y : m₁) → f (x *₁ y) ≡ (f x) *₂ (f y)

MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat = {!!}

Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = ?
