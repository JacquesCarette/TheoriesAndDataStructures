\section{Indexed Setoid Equivalence}

%{{{ Imports
\begin{code}
module ISEquiv where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)
import Relation.Binary.Indexed as I

open import Function.Inverse using () renaming (Inverse to _≅_)
open import Function.Equality using (_⟨$⟩_; _⟶_; Π)
\end{code}
%}}}

\begin{code}
IndexedSetoidEquivalence : {s₁ s₂ f₁ f₂ t₁ t₂ : Level}
    (S : Setoid s₁ s₂)
    (From : I.Setoid (Setoid.Carrier S) f₁ f₂)
    (To : I.Setoid (Setoid.Carrier S) t₁ t₂) →
    Set (s₁ ⊔ s₂ ⊔ f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂)
IndexedSetoidEquivalence S From To = {x y : Setoid.Carrier S} → Setoid._≈_ S x y → (From I.at x) ≅ (To I.at y)

module ISE-Combinators {s₁ s₂ f₁ f₂ t₁ t₂ : Level}
    (S : Setoid s₁ s₂)
    (From : I.Setoid (Setoid.Carrier S) f₁ f₂)
    (To : I.Setoid (Setoid.Carrier S) t₁ t₂) where

  open Setoid S

  _$→_ : IndexedSetoidEquivalence S From To → {x y : Carrier} (x≈y : x ≈ y) → From I.at x ⟶ To I.at y
  eq $→ x≈y = _≅_.to (eq x≈y)

  _$←_ : IndexedSetoidEquivalence S From To → {x y : Carrier} (y≈x : y ≈ x) → To I.at x ⟶ From I.at y
  eq $← y≈x = _≅_.from (eq y≈x)

  ap-⇒ : IndexedSetoidEquivalence S From To → {x y : Carrier} (x≈y : x ≈ y) →
      Setoid.Carrier (From I.at x) → Setoid.Carrier (To I.at y)
  ap-⇒ eq x≈y xx = eq $→ x≈y ⟨$⟩ xx

  ap-⇐ : IndexedSetoidEquivalence S From To → {x y : Carrier} (y≈x : y ≈ x) →
      Setoid.Carrier (To I.at x) → Setoid.Carrier (From I.at y)
  ap-⇐ eq y≈x xx = eq $← y≈x ⟨$⟩ xx

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
