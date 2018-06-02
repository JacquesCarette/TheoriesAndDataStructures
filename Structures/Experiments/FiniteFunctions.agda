{-# OPTIONS --without-K #-}

module FiniteFunctions where

open import Data.Vec using (tabulate; _∷_)
open import Data.Fin using (Fin; zero; suc) 
open import Data.Nat using (ℕ; suc) 
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; module ≡-Reasoning)
open import Function using (_∘_)

------------------------------------------------------------------------------
-- Important: Extensionality for finite functions

finext : {n : ℕ} {A : Set} → {f g : Fin n → A} → ((i : Fin n) → f i ≡ g i) → 
         (tabulate f ≡ tabulate g)
finext {0} _ = refl
finext {suc n} {_} {f} {g} fi≡gi = 
  begin (tabulate {suc n} f 
           ≡⟨ refl ⟩
         f zero ∷ tabulate {n} (f ∘ suc)
           ≡⟨ cong (λ x → x ∷ tabulate {n} (f ∘ suc)) (fi≡gi zero) ⟩ 
         g zero ∷ tabulate {n} (f ∘ suc)
           ≡⟨ cong (_∷_ (g zero))
                (finext {f = f ∘ suc} {g ∘ suc} (fi≡gi ∘ suc)) ⟩ 
         g zero ∷ tabulate {n} (g ∘ suc)
           ≡⟨ refl ⟩
         tabulate g ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
