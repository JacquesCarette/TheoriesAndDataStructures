%{{{ Imports
\begin{code}
module SetoidEquiv where

open import Level renaming (_⊔_ to _⊍_)
open import Relation.Binary using (Setoid)

open import EqualityCombinators using (_≡_; module ≡)
\end{code}
%}}}

%{{{ Setoid isos: _≅_, ≅-refl, ≅-trans, ≅-sym, _≅⟨_⟩_, _∎ , ≡→≅
\begin{code}
open import Function using (flip)
open import Function.Inverse public using () renaming
  (Inverse to _≅_
  ; id     to ≅-refl
  ; sym    to ≅-sym
  )

≅-trans : {a b c ℓa ℓb ℓc : Level} {A : Setoid a ℓa} {B : Setoid b ℓb} {C : Setoid c ℓc}
        → A ≅ B → B ≅ C → A ≅ C
≅-trans = flip Function.Inverse._∘_

infix  3 _∎
infixr 2 _≅⟨_⟩_ _≅˘⟨_⟩_

_≅⟨_⟩_ : {x y z ℓx ℓy ℓz : Level} (X : Setoid x ℓx) {Y : Setoid y ℓy} {Z : Setoid z ℓz}
      →  X ≅ Y → Y ≅ Z → X ≅ Z
X ≅⟨ X≅Y ⟩ Y≅Z = ≅-trans X≅Y Y≅Z

_≅˘⟨_⟩_ : {x y z ℓx ℓy ℓz : Level} (X : Setoid x ℓx) {Y : Setoid y ℓy} {Z : Setoid z ℓz}
      →  Y ≅ X → Y ≅ Z → X ≅ Z
X ≅˘⟨ Y≅X ⟩ Y≅Z = ≅-trans (≅-sym Y≅X) Y≅Z

_∎ : {x ℓx : Level} (X : Setoid x ℓx) → X ≅ X
X ∎ = ≅-refl

-- |≅-reflexive|
≡→≅ : {a ℓa : Level} {A B : Setoid a ℓa} → A ≡ B → A ≅ B
≡→≅ ≡.refl = ≅-refl
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
