\section{Structures.Sidequest.Permutations.ActionProperties}

 Documenting properties of |_◈_| and |_◇_|; most notably the elimination results,
\begin{spec}
      ◈-elimination : ∀ p xs ys →  p ◈ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◇ ys
     ◇-elimination : ∀ p xs ys →  p ◇ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◈ ys
\end{spec}

( These names are the other way around wrt “inversion”; they ought to be swapped. c.f. Equality.lagda )

%{{{ Imports
\begin{code}
open import Level using (Level)
open import Relation.Binary using (Setoid)

open import EqualityCombinators  hiding (reflexive)
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)
open import DataProperties using (_‼_)

open import Data.Vec
open import Data.Nat hiding (fold ; _*_)
open import Data.Fin hiding (_+_ ; fold ; _≤_)

open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.Vector

module Structures.Sidequest.Permutations.ActionProperties {ℓ c : Level} (𝒮 : Setoid c ℓ) where

open import Structures.Sidequest.Equality 𝒮 renaming (_≈_ to _≈ₖ_)

private
  open module ≈₀ = Setoid 𝒮 using (Carrier)
  Seq = Vec Carrier
\end{code}

Subscript 0 for ``underlying'', or `base', equality.
%}}}

%{{{ ◈-elimination and inversionTheorem
\begin{code}
◇-cong₂ : {n m : ℕ} {ps : Permutation n m} {xs ys : Seq m}
        → xs ≈ₖ ys → ps ◇ xs  ≈ₖ  ps ◇ ys
◇-cong₂  []-cong = refl _
◇-cong₂ {ps = zero ∷ ps}     (x≈y ∷-cong xs≈ys) = x≈y  ∷-cong  ◇-cong₂ xs≈ys
◇-cong₂ {ps = suc p ∷ ps} eq@(_   ∷-cong xs≈ys)
  = lookup-cong₂ {i = p} xs≈ys  ∷-cong  ◇-cong₂ (remove-cong₂ {i = suc p} eq)

◈-elimination : {n m : ℕ} (p : Permutation n m)  (xs : Seq n) (ys : Seq m)
              → p ◈ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◇ ys
◈-elimination p xs _ eq  =  reflexive (≡.sym (inversionTheorem p xs)) ⟨≈ₖ≈⟩ ◇-cong₂ eq
\end{code}
%}}}

%{{{ ◇-elimination and inversionTheorem˘
The other form as well,
\begin{code}
◈-cong₂ : {n m : ℕ} {ps : Permutation n m} {xs ys : Seq n}
        → xs ≈ₖ ys → ps ◈ xs ≈ₖ ps ◈ ys
◈-cong₂ []-cong                          =  refl _
◈-cong₂ {ps = _ ∷ _} (x≈y ∷-cong xs≈ys)  =  insert-cong₁ (◈-cong₂ xs≈ys)  ⟨≈ₖ≈⟩  insert-cong₃ x≈y

◇-elimination : {n m : ℕ} (p : Permutation n m)  (xs : Seq m) (ys : Seq n)
              → p ◇ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◈ ys
◇-elimination p xs ys eq  =  reflexive (≡.sym (inversionTheorem˘ p xs))  ⟨≈ₖ≈⟩  ◈-cong₂ eq
\end{code}
%}}}

%{{{ Id is the unit of the actions
\begin{code}
Id-◈ : {n : ℕ} {xs : Seq n} → Id ◈ xs ≈ₖ xs
Id-◈ {xs = []   }  =  []-cong
Id-◈ {xs = _ ∷ _}  =  ≈₀.refl ∷-cong Id-◈

Id-◇ : {m : ℕ} {xs : Seq m} → Id ◇ xs ≈ₖ xs
Id-◇ {xs = []   }  =  []-cong
Id-◇ {xs = _ ∷ _}  =  ≈₀.refl ∷-cong Id-◇
\end{code}
%}}}


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
