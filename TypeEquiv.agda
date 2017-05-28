{-# OPTIONS --without-K #-}

module TypeEquiv where

import Level using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)

open import Algebra using (CommutativeSemiring)
open import Algebra.Structures
  using (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)
  
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Equiv
  using (_≐_; ≐-refl; _≃_; id≃; sym≃; ≃IsEquiv; qinv; _⊎≃_; _×≃_)

------------------------------------------------------------------------------
-- Type Equivalences

-- for each type combinator, define two functions that are inverses, and
-- establish an equivalence.  These are all in the 'semantic space' with
-- respect to Pi combinators.

-- swap₊

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

abstract

  swapswap₊ : {A B : Set} → swap₊ ○ swap₊ {A} {B} ≐ id
  swapswap₊ (inj₁ a) = refl
  swapswap₊ (inj₂ b) = refl

swap₊equiv : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
swap₊equiv = (swap₊ , qinv swap₊ swapswap₊ swapswap₊)

-- unite₊ and uniti₊

unite₊ : {A : Set} → ⊥ ⊎ A → A
unite₊ (inj₁ ())
unite₊ (inj₂ y) = y

uniti₊ : {A : Set} → A → ⊥ ⊎ A
uniti₊ a = inj₂ a

abstract

  uniti₊∘unite₊ : {A : Set} → uniti₊ ○ unite₊ ≐ id {A = ⊥ ⊎ A}
  uniti₊∘unite₊ (inj₁ ())
  uniti₊∘unite₊ (inj₂ y) = refl

  -- this is so easy, Agda can figure it out by itself (see below)

  unite₊∘uniti₊ : {A : Set} → unite₊ ○ uniti₊ ≐ id {A = A}
  unite₊∘uniti₊ _ = refl

unite₊equiv : {A : Set} → (⊥ ⊎ A) ≃ A
unite₊equiv = (unite₊ , qinv uniti₊ unite₊∘uniti₊ uniti₊∘unite₊)

uniti₊equiv : {A : Set} → A ≃ (⊥ ⊎ A)
uniti₊equiv = sym≃ unite₊equiv

-- unite₊′ and uniti₊′

unite₊′ : {A : Set} → A ⊎ ⊥ → A
unite₊′ (inj₁ x) = x
unite₊′ (inj₂ ())

uniti₊′ : {A : Set} → A → A ⊎ ⊥
uniti₊′ a = inj₁ a

abstract

  uniti₊′∘unite₊′ : {A : Set} → uniti₊′ ○ unite₊′ ≐ id {A = A ⊎ ⊥}
  uniti₊′∘unite₊′ (inj₁ _) = refl
  uniti₊′∘unite₊′ (inj₂ ())

  -- this is so easy, Agda can figure it out by itself (see below)

  unite₊′∘uniti₊′ : {A : Set} → unite₊′ ○ uniti₊′ ≐ id {A = A}
  unite₊′∘uniti₊′ _ = refl

unite₊′equiv : {A : Set} → (A ⊎ ⊥) ≃ A
unite₊′equiv = (unite₊′ , qinv uniti₊′ ≐-refl uniti₊′∘unite₊′)

uniti₊′equiv : {A : Set} → A ≃ (A ⊎ ⊥)
uniti₊′equiv = sym≃ unite₊′equiv

-- unite⋆ and uniti⋆

unite⋆ : {A : Set} → ⊤ × A → A
unite⋆ (tt , x) = x

uniti⋆ : {A : Set} → A → ⊤ × A
uniti⋆ x = tt , x

abstract

  uniti⋆∘unite⋆ : {A : Set} → uniti⋆ ○ unite⋆ ≐ id {A = ⊤ × A}
  uniti⋆∘unite⋆ (tt , x) = refl

unite⋆equiv : {A : Set} → (⊤ × A) ≃ A
unite⋆equiv = unite⋆ , qinv uniti⋆ ≐-refl uniti⋆∘unite⋆

uniti⋆equiv : {A : Set} → A ≃ (⊤ × A)
uniti⋆equiv = sym≃ unite⋆equiv

-- unite⋆′ and uniti⋆′

unite⋆′ : {A : Set} → A × ⊤ → A
unite⋆′ (x , tt) = x

uniti⋆′ : {A : Set} → A → A × ⊤
uniti⋆′ x = x , tt

abstract

  uniti⋆′∘unite⋆′ : {A : Set} → uniti⋆′ ○ unite⋆′ ≐ id {A = A × ⊤}
  uniti⋆′∘unite⋆′ (x , tt) = refl

unite⋆′equiv : {A : Set} → (A × ⊤) ≃ A
unite⋆′equiv = unite⋆′ , qinv uniti⋆′ ≐-refl uniti⋆′∘unite⋆′

uniti⋆′equiv : {A : Set} → A ≃ (A × ⊤)
uniti⋆′equiv = sym≃ unite⋆′equiv

-- swap⋆

swap⋆ : {A B : Set} → A × B → B × A
swap⋆ (a , b) = (b , a)

abstract

  swapswap⋆ : {A B : Set} → swap⋆ ○ swap⋆ ≐ id {A = A × B}
  swapswap⋆ (a , b) = refl 

swap⋆equiv : {A B : Set} → (A × B) ≃ (B × A)
swap⋆equiv = swap⋆ , qinv swap⋆ swapswap⋆ swapswap⋆

-- assocl₊ and assocr₊

assocl₊ : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

abstract

  assocl₊∘assocr₊ : {A B C : Set} → assocl₊ ○ assocr₊ ≐ id {A = ((A ⊎ B) ⊎ C)}
  assocl₊∘assocr₊ (inj₁ (inj₁ a)) = refl
  assocl₊∘assocr₊ (inj₁ (inj₂ b)) = refl
  assocl₊∘assocr₊ (inj₂ c) = refl

  assocr₊∘assocl₊ : {A B C : Set} → assocr₊ ○ assocl₊ ≐ id {A = (A ⊎ (B ⊎ C))}
  assocr₊∘assocl₊ (inj₁ a) = refl
  assocr₊∘assocl₊ (inj₂ (inj₁ b)) = refl
  assocr₊∘assocl₊ (inj₂ (inj₂ c)) = refl

assocr₊equiv : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
assocr₊equiv =
  assocr₊ , qinv assocl₊ assocr₊∘assocl₊ assocl₊∘assocr₊

assocl₊equiv : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
assocl₊equiv = sym≃ assocr₊equiv


-- assocl⋆ and assocr⋆

assocl⋆ : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl⋆ (a , (b , c)) = ((a , b) , c)

assocr⋆ : {A B C : Set} → ((A × B) × C) → (A × (B × C))
assocr⋆ ((a , b) , c) = (a , (b , c))

abstract

  assocl⋆∘assocr⋆ : {A B C : Set} → assocl⋆ ○ assocr⋆ ≐ id {A = ((A × B) × C)}
  assocl⋆∘assocr⋆ = ≐-refl

  assocr⋆∘assocl⋆ : {A B C : Set} → assocr⋆ ○ assocl⋆ ≐ id {A = (A × (B × C))}
  assocr⋆∘assocl⋆ = ≐-refl

assocl⋆equiv : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
assocl⋆equiv = 
  assocl⋆ , qinv assocr⋆ assocl⋆∘assocr⋆ assocr⋆∘assocl⋆

assocr⋆equiv : {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
assocr⋆equiv = sym≃ assocl⋆equiv

-- distz and factorz, on left

distz : { A : Set} → (⊥ × A) → ⊥
distz = proj₁

factorz : {A : Set} → ⊥ → (⊥ × A)
factorz ()

abstract

  distz∘factorz : {A : Set} → distz ○ factorz {A} ≐ id
  distz∘factorz ()

  factorz∘distz : {A : Set} → factorz {A} ○ distz ≐ id
  factorz∘distz (() , proj₂)

distzequiv : {A : Set} → (⊥ × A) ≃ ⊥
distzequiv {A} = 
  distz , qinv factorz (distz∘factorz {A}) factorz∘distz

factorzequiv : {A : Set} → ⊥ ≃ (⊥ × A)
factorzequiv {A} = sym≃ distzequiv

-- distz and factorz, on right

distzr : { A : Set} → (A × ⊥) → ⊥
distzr = proj₂

factorzr : {A : Set} → ⊥ → (A × ⊥)
factorzr ()

abstract

  distzr∘factorzr : {A : Set} → distzr ○ factorzr {A} ≐ id
  distzr∘factorzr ()

  factorzr∘distzr : {A : Set} → factorzr {A} ○ distzr ≐ id
  factorzr∘distzr (_ , ())

distzrequiv : {A : Set} → (A × ⊥) ≃ ⊥
distzrequiv {A} = 
  distzr , qinv factorzr (distzr∘factorzr {A}) factorzr∘distzr

factorzrequiv : {A : Set} → ⊥ ≃ (A × ⊥)
factorzrequiv {A} = sym≃ distzrequiv

-- dist and factor, on right

dist : {A B C : Set} → ((A ⊎ B) × C) → (A × C) ⊎ (B × C)
dist (inj₁ x , c) = inj₁ (x , c)
dist (inj₂ y , c) = inj₂ (y , c)

factor : {A B C : Set} → (A × C) ⊎ (B × C) → ((A ⊎ B) × C)
factor (inj₁ (a , c)) = inj₁ a , c
factor (inj₂ (b , c)) = inj₂ b , c

abstract

  dist∘factor : {A B C : Set} → dist {A} {B} {C} ○ factor ≐ id
  dist∘factor (inj₁ x) = refl
  dist∘factor (inj₂ y) = refl

  factor∘dist : {A B C : Set} → factor {A} {B} {C} ○ dist ≐ id
  factor∘dist (inj₁ x , c) = refl
  factor∘dist (inj₂ y , c) = refl

distequiv : {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
distequiv = dist , qinv factor dist∘factor factor∘dist

factorequiv : {A B C : Set} →  ((A × C) ⊎ (B × C)) ≃ ((A ⊎ B) × C)
factorequiv = sym≃ distequiv

-- dist and factor, on left

distl : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
distl (x , inj₁ x₁) = inj₁ (x , x₁)
distl (x , inj₂ y) = inj₂ (x , y)

factorl : {A B C : Set} → (A × B) ⊎ (A × C) → A × (B ⊎ C)
factorl (inj₁ (x , y)) = x , inj₁ y
factorl (inj₂ (x , y)) = x , inj₂ y

abstract

  distl∘factorl : {A B C : Set} → distl {A} {B} {C} ○ factorl ≐ id
  distl∘factorl (inj₁ (x , y)) = refl
  distl∘factorl (inj₂ (x , y)) = refl

  factorl∘distl : {A B C : Set} → factorl {A} {B} {C} ○ distl ≐ id
  factorl∘distl (a , inj₁ x) = refl
  factorl∘distl (a , inj₂ y) = refl

distlequiv : {A B C : Set} → (A × (B ⊎ C)) ≃ ((A × B) ⊎ (A × C))
distlequiv = distl , qinv factorl distl∘factorl factorl∘distl

factorlequiv : {A B C : Set} → ((A × B) ⊎ (A × C)) ≃ (A × (B ⊎ C))
factorlequiv = sym≃ distlequiv

------------------------------------------------------------------------------
-- Commutative semiring structure

typesPlusIsSG : IsSemigroup {Level.suc Level.zero} {Level.zero} {Set} _≃_ _⊎_
typesPlusIsSG = record {
  isEquivalence = ≃IsEquiv ;
  assoc = λ t₁ t₂ t₃ → assocr₊equiv {t₁} {t₂} {t₃} ;
  ∙-cong = _⊎≃_
  }

typesTimesIsSG : IsSemigroup {Level.suc Level.zero} {Level.zero} {Set} _≃_ _×_
typesTimesIsSG = record {
  isEquivalence = ≃IsEquiv ;
  assoc = λ t₁ t₂ t₃ → assocr⋆equiv {t₁} {t₂} {t₃} ;
  ∙-cong = _×≃_
  }

typesPlusIsCM : IsCommutativeMonoid _≃_ _⊎_ ⊥
typesPlusIsCM = record {
  isSemigroup = typesPlusIsSG ;
  identityˡ = λ t → unite₊equiv {t} ;
  comm = λ t₁ t₂ → swap₊equiv {t₁} {t₂}
  }

typesTimesIsCM : IsCommutativeMonoid _≃_ _×_ ⊤
typesTimesIsCM = record {
  isSemigroup = typesTimesIsSG ;
  identityˡ = λ t → unite⋆equiv {t} ;
  comm = λ t₁ t₂ → swap⋆equiv {t₁} {t₂}
  }

typesIsCSR : IsCommutativeSemiring _≃_ _⊎_ _×_ ⊥ ⊤
typesIsCSR = record {
  +-isCommutativeMonoid = typesPlusIsCM ;
  *-isCommutativeMonoid = typesTimesIsCM ;
  distribʳ = λ t₁ t₂ t₃ → distequiv {t₂} {t₃} {t₁} ; 
  zeroˡ = λ t → distzequiv {t}
  }

typesCSR : CommutativeSemiring (Level.suc Level.zero) Level.zero
typesCSR = record {
  Carrier = Set ;
  _≈_ = _≃_ ;
  _+_ = _⊎_ ;
  _*_ = _×_ ;
  0# = ⊥ ;
  1# = ⊤ ;
  isCommutativeSemiring = typesIsCSR
  }

------------------------------------------------------------------------------
