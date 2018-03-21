\section{Structures.Sidequest.SummerHole}

The pesky hole from the summer of 2017.

%{{{ Imports
\begin{code}
open import Structures.CommMonoid using (CommMonoid ; module CommMonoid ; module IsCommutativeMonoid)

open import Level           using (Level)
open import Relation.Binary using (Setoid ; IsEquivalence)
open import Function        using (_$_)
open import EqualityCombinators hiding (reflexive)

-- open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat hiding (_*_ ; fold)
open import Data.Vec 

module Structures.Sidequest.SummerHole {s₁ s₂} (S : Setoid s₁ s₂) (C : CommMonoid S) where

open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.Vector
open import Structures.Sidequest.Permutations.ActionProperties S
open import Structures.Sidequest.Permutations.Group S
open import Structures.Sidequest.Equality S renaming (_≈_ to _≈ₖ_) hiding (refl ; trans)
open import Structures.Sidequest.Permutations.BagEquality S

open CommMonoid C
open IsCommutativeMonoid isCommMonoid -- \edcomm{MA}{The field name really oughtn't be abbreviated!}

private
  open module ≈₀ = Setoid S using (Carrier ; _≈_)
  Seq = Vec Carrier  
\end{code}
%}}}

\begin{code}
-- fold is a setoid homomorphism

fold : {n : ℕ} → Seq n → Carrier
fold = foldr (λ _ → Carrier) _*_ e

fold-cong : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → fold xs ≈ fold ys
fold-cong []-cong = ≈.refl
fold-cong (x≈y ∷-cong xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
-- commutativity is not used here and so this result is valid for non-commutative monoids as well.

open import Relation.Binary.SetoidReasoning

-- commutativity here!
proposition₄ : {n : ℕ} {zs : Seq n} {x y : Carrier}
             → fold (x ∷ y ∷ zs) ≈ fold (y ∷ x ∷ zs)
proposition₄ {n} {zs} {x} {y} = begin⟨ S ⟩
    fold (x ∷ y ∷ zs)
  ≈˘⟨ assoc _ _ _ ⟩
    (x * y) * fold zs
  ≈⟨ comm _ _ ⟨∙⟩  ≈.refl ⟩
    (y * x) * fold zs
  ≈⟨ assoc _ _ _ ⟩
    fold (y ∷ x ∷ zs)
  ∎

open import Data.Fin  hiding (_+_ ; fold ; _≤_)

proposition₃ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x y : Carrier}
             → fold (x ∷ y ∷ xs) ≈ fold (y ∷ insert xs i x)
proposition₃ {.0} {[]} {zero} =  proposition₄
proposition₃ {.0} {[]} {suc ()}
proposition₃ {.(suc _)} {x ∷ xs} {zero} = proposition₄
proposition₃ {.(suc _)} {hd ∷ xs} {suc i} {x} {y} = begin⟨ S ⟩
    fold (x ∷ y ∷ hd ∷ xs)
  ≈⟨ proposition₄ ⟩
    fold (y ∷ x ∷ hd ∷ xs)
  ≡⟨ ≡.refl ⟩
    y * fold (x ∷ hd ∷ xs)
  ≈⟨   ≈.refl  ⟨∙⟩ proposition₃ ⟩
    y * fold (hd ∷ insert xs i x)
  ≡⟨ ≡.refl ⟩
    fold (y ∷ hd ∷ insert xs i x)
  ∎

proposition₂ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x : Carrier}
             → fold (x ∷ xs) ≈ fold (insert xs i x)
proposition₂ {.0} {[]} {zero} =   ≈.refl 
proposition₂ {.0} {[]} {suc ()}
proposition₂ {.(suc _)} {y ∷ xs} {zero} =   ≈.refl 
proposition₂ {.(suc _)} {y ∷ xs} {suc i} = proposition₃

open import Relation.Binary.PropositionalEquality using (inspect; [_])

proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n n} → fold xs ≈ fold (p ◈ xs)
proposition₁ {xs = []} {[]} =   ≈.refl 
proposition₁ {xs = x ∷ xs} {zero  ∷ ps} =   ≈.refl  ⟨∙⟩ proposition₁
proposition₁ {xs = x ∷ xs} {suc p ∷ ps} with ps ◈ xs | inspect (_◈_ ps) xs
proposition₁ {_} {x ∷ xs} {suc () ∷ ps} | [] | _
proposition₁ {_} {x ∷ xs} {suc p ∷ ps} | x′ ∷ xs′ | [ ps◈xs≈xs′ ] = begin⟨ S ⟩
    x * fold xs
  ≈⟨  ≈.refl  ⟨∙⟩ proposition₁ ⟩
    x * fold (ps ◈ xs)
  ≡⟨ ≡.cong (λ zs → x * fold zs) ps◈xs≈xs′ ⟩
    x * fold (x′ ∷ xs′)
  ≡⟨ ≡.refl ⟩
    fold (x ∷ x′ ∷ xs′)
  ≈⟨ proposition₄ ⟩
    fold (x′ ∷ x ∷ xs′)
  ≡⟨ ≡.refl ⟩
    x′ * fold (x ∷ xs′)
  ≈⟨  ≈.refl  ⟨∙⟩ proposition₂ ⟩
    x′ * fold (insert xs′ p x)
  ∎

-- This is essentially |Multiset.fold-permute|, the pesky-hole from the summer.
proposition₀ : {n : ℕ} {xs ys : Seq n} → xs ≈ₚ ys → fold xs ≈ fold ys
proposition₀ (MkEq p p◈xs≈ys) = ≈.trans proposition₁ (fold-cong p◈xs≈ys)
\end{code}

% Quick Folding Instructions:
% C-c C-s :: show/unfold region
% C-c C-h :: hide/fold region
% C-c C-w :: whole file fold
% C-c C-o :: whole file unfold
%
% Local Variables:
% folded-file: t
% eval: (fold-set-marks "%{{{ " "%}}}")
% eval: (fold-whole-buffer)
% fold-internal-margins: 0
% end:
