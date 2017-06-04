Stuff copied over from the RATH-Agda libraries.

\begin{code}
module RATH where

open import Level renaming (_⊔_ to _⊍_)

open import Relation.Binary
open import Relation.Binary.Sum using (_⊎-setoid_)

infix 1 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊍ i₂) (i₁ ⊍ i₂ ⊍ k₁ ⊍ k₂)
A ⊎⊎ B = A ⊎-setoid B

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
