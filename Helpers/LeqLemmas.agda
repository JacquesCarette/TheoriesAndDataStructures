{-# OPTIONS --without-K #-}

module LeqLemmas where

open import Data.Nat
  using (ℕ; suc; _+_; _*_; _<_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Nat.Properties using (n≤m+n; module ≤-Reasoning)
open import Relation.Binary using (Decidable)

------------------------------------------------------------------------------
-- Proofs and definitions about ≤ on natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

cong+r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i + k ≤ j + k
cong+r≤ {0}     {j}     z≤n       k = n≤m+n j k
cong+r≤ {suc i} {0}     ()        k -- absurd
cong+r≤ {suc i} {suc j} (s≤s i≤j) k = s≤s (cong+r≤ {i} {j} i≤j k)

cong+l≤ : ∀ {i j} → i ≤ j → (k : ℕ) → k + i ≤ k + j
cong+l≤ {i} {j} i≤j k =
  begin (k + i
           ≡⟨ +-comm k i ⟩
         i + k
           ≤⟨ cong+r≤ i≤j k ⟩
         j + k
           ≡⟨ +-comm j k ⟩
         k + j ∎)
  where open ≤-Reasoning

cong*r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i * k ≤ j * k
cong*r≤ {0}     {j}     z≤n       k = z≤n
cong*r≤ {suc i} {0}     ()        k -- absurd
cong*r≤ {suc i} {suc j} (s≤s i≤j) k = cong+l≤ (cong*r≤ i≤j k) k

------------------------------------------------------------------------------
