\section{SetoidSetoid}

%{{{ Imports
\begin{code}
module SetoidSetoid where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid)

open import DataProperties using (⊤; tt)
open import SetoidEquiv
\end{code}
%}}}

%{{{ _≈S_ ; SSetoid
Setoid of setoids |SSetoid|, and ``setoid'' of equality proofs.
\begin{code}
SSetoid : (ℓ o : Level) → Setoid (lsuc o ⊍ lsuc ℓ) (o ⊍ ℓ)
SSetoid ℓ o = record
  { Carrier = Setoid ℓ o
  ; _≈_ = _≅_
  ; isEquivalence = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans } }
\end{code}

Given two elements of a given Setoid |A|, define a Setoid of equivalences of
those elements.  We consider all such equivalences to be equivalent.  In other
words, for |e₁ e₂ : Setoid.Carrier A|, then |e₁ ≈ₛ e₂|, as a type, is contractible.
\begin{code}
_≈S_ : ∀ {a ℓa} {A : Setoid a ℓa} → (e₁ e₂ : Setoid.Carrier A) → Setoid ℓa ℓa
_≈S_ {A = A} e₁ e₂ = let open Setoid A renaming (_≈_ to _≈ₛ_) in
  record { Carrier = e₁ ≈ₛ e₂ ; _≈_ = λ _ _ → ⊤
         ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }
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
