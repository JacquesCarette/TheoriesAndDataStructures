\section{Indexed Setoid Equivalence}

%{{{ Imports
\begin{code}
module ISEquiv where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)
import Relation.Binary.Indexed as I

open import Function using () renaming (_∘_ to _⊚_)
open import Function.Inverse using () renaming (Inverse to _≅_; id to ≅-refl)
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

Liftable : {s₁ s₂ f₁ f₂ : Level}
    (S : Setoid s₁ s₂)
    (X : I.Setoid (Setoid.Carrier S) f₁ f₂) → Set (s₁ ⊔ s₂ ⊔ f₁ ⊔ f₂)
Liftable S X = IndexedSetoidEquivalence S X X

ISE-refl : {s₁ s₂ ℓx₁ ℓx₂ : Level} {S : Setoid s₁ s₂} {X : I.Setoid (Setoid.Carrier S) ℓx₁ ℓx₂}
  (L : Liftable S X) → IndexedSetoidEquivalence S X X
ISE-refl L = L

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


  ISE-sym : IndexedSetoidEquivalence S From To → IndexedSetoidEquivalence S To From
  ISE-sym From≅To {x} {y} x≈y = record
    { to = record
      { _⟨$⟩_ = ap-⇐ From≅To (sym x≈y)
      ; cong = Π.cong (From≅To $← (sym x≈y)) }
    ; from = record
      { _⟨$⟩_ = ap-⇒ From≅To (sym x≈y)
      ; cong = Π.cong (From≅To $→ sym x≈y) }
    ; inverse-of = record
      { left-inverse-of = _≅_.right-inverse-of (From≅To (sym x≈y))
      ; right-inverse-of = _≅_.left-inverse-of (From≅To (sym x≈y)) }
    }

module ISE-Trans {s₁ s₂ a₁ a₂ b₁ b₂ c₁ c₂ : Level}
    (S : Setoid s₁ s₂)
    (A : I.Setoid (Setoid.Carrier S) a₁ a₂)
    (B : I.Setoid (Setoid.Carrier S) b₁ b₂)
    (C : I.Setoid (Setoid.Carrier S) c₁ c₂) where

  ISE-trans : IndexedSetoidEquivalence S A B → IndexedSetoidEquivalence S B C → IndexedSetoidEquivalence S A C
  ISE-trans A≅B B≅C {x} {y} x≈y = record
    { to = record
      { _⟨$⟩_ = (ap-⇒₂ B≅C x≈y) ⊚ (ap-⇒₁ A≅B refl)
      ; cong = Π.cong (B≅C $→₂ x≈y) ⊚ (Π.cong (A≅B $→₁ refl)) }
    ; from = record
      { _⟨$⟩_ = ap-⇐₁ A≅B refl ⊚ ap-⇐₂ B≅C x≈y
      ; cong = Π.cong (A≅B $←₁ refl) ⊚ Π.cong (B≅C $←₂ x≈y) }
    ; inverse-of = record
      { left-inverse-of = λ aa → I.Setoid.trans A
        (Π.cong (A≅B $←₁ refl) (_≅_.left-inverse-of (B≅C x≈y) (ap-⇒₁ A≅B refl aa)))
        (_≅_.left-inverse-of (A≅B refl) aa)
      ; right-inverse-of = λ cc → I.Setoid.trans C
        (Π.cong (B≅C $→₂ x≈y) (_≅_.right-inverse-of (A≅B refl) (ap-⇐₂ B≅C x≈y cc)))
        (_≅_.right-inverse-of (B≅C x≈y) cc) }
    }
    where
      open Setoid S
      open ISE-Combinators S A B
        renaming (ap-⇐ to ap-⇐₁; ap-⇒ to ap-⇒₁; _$→_ to _$→₁_; _$←_ to _$←₁_)
      open ISE-Combinators S B C
        renaming (ap-⇐ to ap-⇐₂; ap-⇒ to ap-⇒₂; _$→_ to _$→₂_; _$←_ to _$←₂_)
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
