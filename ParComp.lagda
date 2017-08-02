\section{Parallel Composition}

We need a way to put two |SetoidFamily| ``side by side'' -- a form of
parellel composition.  To achieve this requires a certain amount of
infrastructure: parallel composition of relations, and both disjoint
sum and cartesian product of |Setoid|s.  So the next couple of sections
proceed with that infrastruction, before diving in to the crux of the
matter.

%{{{ Imports
\begin{code}
module ParComp where

open import Level
open import Relation.Binary    using  (Setoid; REL; Rel)
open import Function           using  (flip) renaming (id to id₀; _∘_ to _⊚_)
open import Function.Equality  using  (Π; _⟨$⟩_; cong; id; _⟶_; _∘_)
open import Function.Inverse   using  () renaming (_InverseOf_ to Inv)
open import Relation.Binary.Product.Pointwise using (_×-setoid_)

open import Categories.Category using (Category)
open import Categories.Object.Coproduct

open import DataProperties
open import SetoidEquiv

open import TypeEquiv using (swap₊; swap⋆)
\end{code}
%}}}

%{{{ \subsection{Parallel Composition of relations} _∥_ ; [_∥_] ; ∥-sym ; ∥-trans
\subsection{Parallel Composition of relations}

Parallel composition of heterogeneous relations.

Note that this is a specialized version of the standard library's
|_⊎-Rel_| (see |Relation.Binary.Sum|); this one gets rid of the
bothersome |₁∼₂| term.

\begin{code}
data _∥_ {a₁ b₁ c₁ a₂ b₂ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} {A₂ : Set a₂} {B₂ : Set b₂}
  (R₁ : REL A₁ B₁ c₁) (R₂ : REL A₂ B₂ c₂)
  : REL (A₁ ⊎ A₂) (B₁ ⊎ B₂) (c₁ ⊔ c₂) where
  left  : {x : A₁} {y : B₁} (r₁ : R₁ x y) → (R₁ ∥ R₂) (inj₁ x) (inj₁ y)
  right : {x : A₂} {y : B₂} (r₂ : R₂ x y) → (R₁ ∥ R₂) (inj₂ x) (inj₂ y)

elim : {a₁ b₁ a₂ b₂ c₁ c₂ d : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} {A₂ : Set a₂} {B₂ : Set b₂}
  {R₁ : REL A₁ B₁ c₁} {R₂ : REL A₂ B₂ c₂}
  (P : {a : A₁ ⊎ A₂} {b : B₁ ⊎ B₂} (pf : (R₁ ∥ R₂) a b) → Set d)
  (F : {a : A₁} {b : B₁} → (f : R₁ a b) → P (left f))
  (G : {a : A₂} {b : B₂} → (g : R₂ a b) → P (right g))
  {a : A₁ ⊎ A₂} {b : B₁ ⊎ B₂} → (x : (R₁ ∥ R₂) a b) → P x
elim P F G (left r₁) = F r₁
elim P F G (right r₂) = G r₂

-- If the argument relations are symmetric then so is their parallel composition.
∥-sym : {a a′ c c′ : Level} {A : Set a} {R₁ : Rel A c}
  {A′ : Set a′} {R₂ : Rel A′ c′}
  (sym₁ : {x y : A} → R₁ x y → R₁ y x) (sym₂ : {x y : A′} → R₂ x y → R₂ y x)
  {x y : A ⊎ A′}
  → (R₁ ∥ R₂) x y → (R₁ ∥ R₂) y x
∥-sym {R₁ = R₁} {R₂ = R₂} sym₁ sym₂ pf =
  elim (λ {a b} (x : (R₁ ∥ R₂) a b) → (R₁ ∥ R₂) b a) (left ⊚ sym₁) (right ⊚ sym₂) pf

∥-trans : {a a′ ℓ ℓ′ : Level} (A : Setoid a ℓ) (A′ : Setoid a′ ℓ′)
  {x y z : Setoid.Carrier A ⊎ Setoid.Carrier A′} →
  let R₁ = Setoid._≈_ A in let R₂ = Setoid._≈_ A′ in
  (R₁ ∥ R₂) x y → (R₁ ∥ R₂) y z → (R₁ ∥ R₂) x z
∥-trans A A′ {inj₁ x} (left r₁) (left r₂) = left (Setoid.trans A r₁ r₂)
∥-trans A A′ {inj₂ y₂} (right r₂) (right r₃) = right (Setoid.trans A′ r₂ r₃)
\end{code}
%}}}

%{{{ \subsection{Union and product of |Setoid|} |_⊎S_| |_×S_|
\subsection{Union and product of |Setoid|}
\begin{code}
module _ {ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} (S₁ : Setoid ℓA₁ ℓa₁) (S₂ : Setoid ℓA₂ ℓa₂) where
  infix 3 _⊎S_ _×S_

  open Setoid S₁ renaming (Carrier to s₁; _≈_ to _≈₁_; refl to refl₁; sym to sym₁)
  open Setoid S₂ renaming (Carrier to s₂; _≈_ to _≈₂_; refl to refl₂; sym to sym₂)

  _⊎S_ : Setoid (ℓA₁ ⊔ ℓA₂) (ℓa₁ ⊔ ℓa₂)
  _⊎S_  = record
    { Carrier = s₁ ⊎ s₂
    ; _≈_ = _≈₁_ ∥ _≈₂_
    ; isEquivalence = record
      { refl = λ { {inj₁ x} → left refl₁ ; {inj₂ y} → right refl₂ }
      ; sym = ∥-sym sym₁ sym₂
      ; trans = ∥-trans S₁ S₂
      }
    }

  _×S_ : Setoid (ℓA₁ ⊔ ℓA₂) (ℓa₁ ⊔ ℓa₂)
  _×S_ = S₁ ×-setoid S₂
\end{code}
%}}}

%{{{ \subsection{Union of |Setoid| is commutative} |⊎S-comm|
\subsection{Union of |Setoid| is commutative}
\begin{code}
module _ {ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} (S₁ : Setoid ℓA₁ ℓa₁) (S₂ : Setoid ℓA₂ ℓa₂) where
  ⊎S-comm : (S₁ ⊎S S₂) ≅ (S₂ ⊎S S₁)
  ⊎S-comm = record
    { to = record { _⟨$⟩_ = swap₊ ; cong = λ { (left r₁) → right r₁ ; (right r₂) → left r₂} }
    ; from = record { _⟨$⟩_ = swap₊ ; cong = λ { (left r₁) → right r₁ ; (right r₂) → left r₂} }
    ; inverse-of = record
      { left-inverse-of = λ { (inj₁ x) → left (refl S₁) ; (inj₂ y) → right (refl S₂)}
      ; right-inverse-of = λ { (inj₁ x) → left (refl S₂) ; (inj₂ y) → right (refl S₁)} }
    }
    where open Setoid
\end{code}
%}}}
%{{{ \subsection{|_⊎S_| is a congruence} |_⊎S₁_|
\subsection{|_⊎S_| is a congruence}
\begin{code}
module _ {ℓA₁ ℓa₁ ℓA₂ ℓa₂ ℓA₃ ℓa₃ ℓA₄ ℓa₄ : Level}
  {S₁ : Setoid ℓA₁ ℓa₁} {S₂ : Setoid ℓA₂ ℓa₂} {S₃ : Setoid ℓA₃ ℓa₃} {S₄ : Setoid ℓA₄ ℓa₄} where
  _⊎S₁_ : S₁ ≅ S₃ → S₂ ≅ S₄ → (S₁ ⊎S S₂) ≅ (S₃ ⊎S S₄)
  1≅3 ⊎S₁ 2≅4 = record
    { to = record
      { _⟨$⟩_ = λ { (inj₁ x) → inj₁ (to 1≅3 ⟨$⟩ x) ; (inj₂ y) → inj₂ (to 2≅4 ⟨$⟩ y)}
      ; cong = λ { (left r₁) → left (cong (to 1≅3) r₁) ; (right r₂) → right (cong (to 2≅4) r₂)} }
    ; from = record
      { _⟨$⟩_ = λ { (inj₁ x) → inj₁ (from 1≅3 ⟨$⟩ x) ; (inj₂ y) → inj₂ (from 2≅4 ⟨$⟩ y)}
      ; cong = λ { (left r₁) → left (cong (from 1≅3) r₁) ; (right r₂) → right (cong (from 2≅4) r₂)} }
    ; inverse-of = record
      { left-inverse-of = λ { (inj₁ x) → left (left-inverse-of 1≅3 x)
                            ; (inj₂ y) → right (left-inverse-of 2≅4 y)}
      ; right-inverse-of = λ { (inj₁ x) → left (right-inverse-of 1≅3 x)
                             ; (inj₂ y) → right (right-inverse-of 2≅4 y)} }
    }
    where open _≅_
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
