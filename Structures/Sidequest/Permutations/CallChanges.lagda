\section{|Structures.Sidequest.Permutations.CallChanges|}

A (failed) attempt to interpret factorial numbers as sequences of side-by-side swaps.

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.CallChanges where

open import Level using (Level)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

-- open import EqualityCombinators  hiding (reflexive)
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)
open import DataProperties using (_‼_)

open import Data.Maybe
open import Data.List as List
open import Data.Vec as Vec
open import Data.Nat hiding (fold ; _*_)
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_ ; fold ; _≤_)
open import Data.Product using (_,_)

open import FinUtils using (suc′)
open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.SME
\end{code}


\begin{code}
lastPermutation : (n : ℕ) → Permutation n n
lastPermutation zero = []
lastPermutation (suc n) = fromℕ n ∷ lastPermutation n
\end{code}

\begin{code}
{-# TERMINATING #-} -- The |inject₁| is in the way of the termination checker.
permSME₀ :  {n : ℕ} → Permutation n n → SME n n
permSME₀ [] = 𝕀
permSME₀ (_ ∷ []) = 𝕀
permSME₀ {suc (suc n)} (zero ∷ is) = 𝕀 {1} ⊗ permSME₀ is
permSME₀ {suc (suc n)} (suc iₙ ∷ is) = (𝕀 {1} ⊗ permSME₀ (lastPermutation (suc n))) ⨾ 𝕏′ {suc n} zero ⨾ permSME₀ (inject₁ iₙ ∷ is)

permSME :  {m n : ℕ} → Permutation m n → SME m n
permSME p with homogeneity p
... | ≡.refl = permSME₀ p
\end{code}

\begin{code}
{-# TERMINATING #-} -- The |inject₁| is in the way of the termination checker.
perm𝕏s :  {m n : ℕ} → (Fin m → Fin n) → Permutation (suc m) (suc m) → List (Fin n) → List (Fin n)
perm𝕏s _f (_ ∷ []) = Id₀
perm𝕏s {suc m} f (zero ∷ is) = perm𝕏s (f ∘₀ inject₁) is
perm𝕏s {suc m} f (suc iₘ ∷ is)
  = perm𝕏s (f ∘₀ inject₁) (lastPermutation (suc m))
  ∘₀ (f (fromℕ m) ∷_)
  ∘₀ perm𝕏s f (inject₁ iₘ ∷ is)
\end{code}

\begin{code}
permSME₁ :  {m n : ℕ} → Permutation (suc m) (suc n) → SME (suc m) (suc n)
permSME₁ p with homogeneity p
... | ≡.refl = List.foldr (λ i r → 𝕏′ i ⨾ r) 𝕀 (perm𝕏s Id₀ p [])
\end{code}

%{{{ noPermutation ; sucPermutation
\begin{code}
noPermutation : (n : ℕ) → Permutation n n
noPermutation zero = []
noPermutation (suc n) = zero ∷ noPermutation n

sucPermutation : {n : ℕ} → Permutation n n → Maybe (Permutation n n)
sucPermutation [] = nothing
sucPermutation (i ∷ is) = maybe
  (λ is′ → just (i ∷ is′))
  (maybe (λ i′ → just (i′ ∷ noPermutation _)) nothing (suc′ i))
  (sucPermutation is)
\end{code}
%}}}

\begin{code}
perm : {n : ℕ} → Permutation (suc n) (suc n) → Vec ℕ (suc n)
perm {n} p = Vec.map toℕ (permSME₁ p ◣ allFin (suc n))
  where
    open Action (≡.setoid (Fin (suc n)))
\end{code}

\begin{code}
perms : {n : ℕ} → Permutation (suc n) (suc n) → List (Vec ℕ (suc n))
perms {n} p = List.map (Vec.map toℕ) (perm𝕏s Id₀ p [] ◺ allFin (suc n))
  where
    open Action (≡.setoid (Fin (suc n)))
\end{code}

Using the original |_◺_|,
the following list of 15 permuted vectors takes seconds to generate via
|C-c C-n|:
\begin{spec}
perms (zero ∷ suc (suc zero) ∷ suc zero ∷ suc zero ∷ zero ∷ [])
\end{spec}
(Using the current |_◺_|, both this and below are instanteneous.)

Using the original |_◺_|,
the 24 permuted vectors of the following take almost 400 seconds ---
and contain duplicates! \unfinished
\begin{spec}
perms (suc zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ [])

0   (1 ∷ 0 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷
1   (1 ∷ 2 ∷ 0 ∷ 3 ∷ 4 ∷ []) ∷  rot 3
0   (2 ∷ 1 ∷ 0 ∷ 3 ∷ 4 ∷ []) ∷
1   (2 ∷ 0 ∷ 1 ∷ 3 ∷ 4 ∷ []) ∷  rot 3
0   (0 ∷ 2 ∷ 1 ∷ 3 ∷ 4 ∷ []) ∷
2   (0 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ []) ∷
0   (2 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ []) ∷  nofix 4
1   (2 ∷ 3 ∷ 0 ∷ 1 ∷ 4 ∷ []) ∷  rot 4
0   (3 ∷ 2 ∷ 0 ∷ 1 ∷ 4 ∷ []) ∷  nofix 4
1   (3 ∷ 0 ∷ 2 ∷ 1 ∷ 4 ∷ []) ∷
0   (0 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []) ∷
2   (0 ∷ 3 ∷ 1 ∷ 2 ∷ 4 ∷ []) ∷
0   (3 ∷ 0 ∷ 1 ∷ 2 ∷ 4 ∷ []) ∷  rot 4
1   (3 ∷ 1 ∷ 0 ∷ 2 ∷ 4 ∷ []) ∷  nofix 4
0   (1 ∷ 3 ∷ 0 ∷ 2 ∷ 4 ∷ []) ∷  nofix 4
1   (1 ∷ 0 ∷ 3 ∷ 2 ∷ 4 ∷ []) ∷  nofix 4
0   (0 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ []) ∷

2   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷
0   (1 ∷ 0 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷
1   (1 ∷ 2 ∷ 0 ∷ 3 ∷ 4 ∷ []) ∷
0   (2 ∷ 1 ∷ 0 ∷ 3 ∷ 4 ∷ []) ∷
1   (2 ∷ 0 ∷ 1 ∷ 3 ∷ 4 ∷ []) ∷
0   (0 ∷ 2 ∷ 1 ∷ 3 ∷ 4 ∷ []) ∷
3   (0 ∷ 2 ∷ 1 ∷ 4 ∷ 3 ∷ []) ∷ []

Missing:
    (1 ∷ 3 ∷ 2 ∷ 0 ∷ 4 ∷ []) ∷
    (1 ∷ 2 ∷ 3 ∷ 0 ∷ 4 ∷ []) ∷
    (2 ∷ 1 ∷ 3 ∷ 0 ∷ 4 ∷ []) ∷
    (2 ∷ 3 ∷ 1 ∷ 0 ∷ 4 ∷ []) ∷
    (3 ∷ 2 ∷ 1 ∷ 0 ∷ 4 ∷ []) ∷
    (3 ∷ 1 ∷ 2 ∷ 0 ∷ 4 ∷ []) ∷


List.map toℕ (perm𝕏s Id₀ (suc zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []) [])
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 3 ∷ []

List.map toℕ (perm𝕏s Id₀ (suc zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []) [])
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷  3 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷  3 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷  3 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷  3 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷
0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷  4 ∷ []
\end{spec}
(The |perm𝕏s| calculations have always been fast.)

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
