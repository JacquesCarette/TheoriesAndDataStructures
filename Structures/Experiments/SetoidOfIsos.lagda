%{{{ Imports
\begin{code}
module SetoidOfIsos where

open import Level renaming (_⊔_ to _⊍_)
open import Relation.Binary using (Setoid)

open import Function.Equality using (Π)

open import SetoidEquiv
\end{code}
%}}}

%{{{ Isos between Isos: _≋_ , id≋, trans≋, sym≋, and setoid of such things: _≅S_
\begin{code}
record _≋_ {a b ℓa ℓb} {A : Setoid a ℓa} {B : Setoid b ℓb} (eq₁ eq₂ : A ≅ B) : Set (a ⊍ b ⊍ ℓa ⊍ ℓb) where
  constructor eq
  open _≅_
  open Setoid A using () renaming (_≈_ to _≈₁_)
  open Setoid B using () renaming (_≈_ to _≈₂_)
  open Π
  field
    to≈ :   ∀ x → to   eq₁ ⟨$⟩ x ≈₂ to   eq₂ ⟨$⟩ x
    from≈ : ∀ x → from eq₁ ⟨$⟩ x ≈₁ from eq₂ ⟨$⟩ x

module _ {a b ℓa ℓb} {A : Setoid a ℓa} {B : Setoid b ℓb} where
  id≋ : {x : A ≅ B} → x ≋ x
  id≋ = eq (λ _ → Setoid.refl B) (λ _ → Setoid.refl A)

  sym≋ : {i j : A ≅ B} → i ≋ j → j ≋ i
  sym≋ (eq to≈ from≈) = eq (λ x → Setoid.sym B (to≈ x)) (λ x → Setoid.sym A (from≈ x))

  trans≋ : {i j k : A ≅ B} → i ≋ j → j ≋ k → i ≋ k
  trans≋ (eq to≈₀ from≈₀) (eq to≈₁ from≈₁) = eq (λ x → Setoid.trans B (to≈₀ x) (to≈₁ x)) (λ x → Setoid.trans A (from≈₀ x) (from≈₁ x))

_≅S_ : ∀ {a b ℓa ℓb} (A : Setoid a ℓa) (B : Setoid b ℓb) → Setoid (ℓb ⊍ (ℓa ⊍ (b ⊍ a))) (ℓb ⊍ (ℓa ⊍ (b ⊍ a)))
_≅S_ A B = record
  { Carrier = A ≅ B
  ; _≈_ = _≋_
  ; isEquivalence = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ } }
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
