\section{Structures.Sidequest.Permutations.BagEquality}

And now we really want to use our |Permutation| to define a bag equality on lists.
But this is a bit of a pain, as |Permutation| really acts on |Vec|. But, of course,
a |List| is just a |Vec| that has forgotten its |length| (or the other way around
if you are thinking in terms of ornaments).  This type equivalence will be shown
elsewhere, so here we set things up using |Vec|.

%{{{ Imports
\begin{code}
open import Level           using (Level)
open import Relation.Binary using (Setoid ; IsEquivalence)
open import Function        using (_$_)
open import EqualityCombinators hiding (reflexive)

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ   ; zero ; suc ; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)

module Structures.Sidequest.Permutations.BagEquality {s₁ s₂} (S : Setoid s₁ s₂) where

open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.Vector
open import Structures.Sidequest.Permutations.ActionProperties S
open import Structures.Sidequest.Permutations.Group S
open import Structures.Sidequest.Equality S renaming (_≈_ to _≈ₖ_)

private
  open module ≈₀ = Setoid S using (Carrier) renaming (_≈_ to _≈₀_)
  Seq = Vec Carrier
\end{code}
%}}}

Equality-(of vectors)-up-to-permutation.

\begin{code}
record _≈ₚ_ {n m : ℕ} (xs : Seq n) (ys : Seq m) : Set s₂ where
  constructor MkEq
  field
    witness : Permutation n m
    proof   : witness ◈ xs ≈ₖ ys

≈ₚ-refl :  {n : ℕ} {xs : Seq n} → xs ≈ₚ xs
≈ₚ-refl = record { witness = Id ; proof = Id-◈ }

≈ₚ-sym : {n m : ℕ} {xs : Seq n} {ys : Seq m} → xs ≈ₚ ys → ys ≈ₚ xs
≈ₚ-sym (MkEq w pf) = MkEq (w ˘) (sym (◈-solve-linear-equation {_} {_} {w} pf))

≈ₚ-trans : {n m r : ℕ} {xs : Seq n} {ys : Seq m} {zs : Seq r}
         → xs ≈ₚ ys → ys ≈ₚ zs → xs ≈ₚ zs
≈ₚ-trans (MkEq witness proof) (MkEq witness₁ proof₁) =
  MkEq (witness ⊙ witness₁)
       (trans ◈-compose (trans (◈-cong₂ proof) proof₁))

≈ₚ-isEquivalence : {n : ℕ} → IsEquivalence (_≈ₚ_ {n} {n})
≈ₚ-isEquivalence = record { refl = ≈ₚ-refl ; sym = ≈ₚ-sym ; trans = ≈ₚ-trans }

singleton-≈ : {x y : Carrier} → x ≈₀ y → (x ∷ []) ≈ₚ (y ∷ [])
singleton-≈ = λ x≈y → MkEq Id (x≈y ∷-cong []-cong)
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
