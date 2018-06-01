\section{Structures.Sidequest.Permutations.Testing}

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.Testing where

open import Level using (Level)
open import Function using (_$_)
open import DataProperties hiding (⟨_,_⟩)
open import EqualityCombinators
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)

open import Data.Vec
open import Data.Nat hiding (fold ; _*_)
open import Data.Fin hiding (_+_ ; fold ; _≤_)

open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.Vector
\end{code}
%}}}

\begin{code}
aPerm : Permutation 5 5
aPerm = suc (suc (suc zero)) ∷ zero ∷ suc (suc zero) ∷ zero ∷ zero ∷ []

-- |aPerm : [x₀, …, x₄] ↦ [x₃, x₀, x₄, x₁, x₂]|
seeP-rev : seePerm aPerm ≡ 3 ∷ 0 ∷ 4 ∷ 1 ∷ 2 ∷ []
seeP-rev = ≡.refl
-- Shouldn't at least one of these *end* with a 0? That is to insert into an empty list?
VecPa≡30412 : seePerm′ aPerm ≡ 1 ∷ 3 ∷ 4 ∷ 0 ∷ 2 ∷ []
VecPa≡30412 = ≡.refl

aPerm-as-vec  : Vec (Fin 5) 5
aPerm-as-vec = toVector aPerm

aPerm-as-vec-look : map toℕ aPerm-as-vec  ≡  3 ∷ 0 ∷ 4 ∷ 1 ∷ 2 ∷ []
  -- |≡ suc (suc (suc zero)) ∷ zero ∷ suc (suc (suc (suc zero))) ∷ suc zero ∷ suc (suc zero) ∷ []|
aPerm-as-vec-look = ≡.refl

well : fromVector
       (suc (suc (suc zero)) ∷ zero ∷ (suc (suc (suc (suc zero)))) ∷ suc zero ∷ suc (suc zero) ∷ [])
       ≡ suc (suc (suc zero)) ∷  zero ∷  (suc (suc zero)) ∷ suc zero ∷ zero ∷ []
       -- almost aPerm:                                      ^ offending piece
well = ≡.refl

aPerm˘ : Permutation 5 5
aPerm˘ = suc zero ∷ suc (suc zero) ∷ suc (suc zero) ∷ zero ∷ zero ∷ []

test-inv : aPerm˘ ◈ (aPerm ◈ allFin _) ≡ allFin _
test-inv = ≡.refl

test-inv₃ : aPerm ◈ allFin _  ≡  aPerm˘ ◇ allFin _
test-inv₃ = ≡.refl

test-inv2 : aPerm ◇ (aPerm ◈ allFin _) ≡ allFin _
test-inv2 = ≡.refl
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
