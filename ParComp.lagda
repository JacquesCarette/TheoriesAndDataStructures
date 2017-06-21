\section{Some}

%{{{ Imports
\begin{code}
module ParComp where

open import Level
open import Relation.Binary using (Setoid)

open import DataProperties
open import SetoidEquiv

open import TypeEquiv using (swap₊)
\end{code}
%}}}

%{{{ \subsection{Parallel Composition} _∥_ ; [_∥_] ; ∥-sym ; _⊎⊎_
\subsection{Parallel Composition}

Parallel composition of heterogeneous relations.

\begin{code}
data _∥_ {a₁ b₁ c₁ a₂ b₂ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} (_~₁_ : A₁ → B₁ → Set c₁)
  {A₂ : Set a₂} {B₂ : Set b₂} (_~₂_ : A₂ → B₂ → Set c₂)
  : A₁ ⊎ A₂ → B₁ ⊎ B₂ → Set (a₁ ⊔ b₁ ⊔ c₁ ⊔ a₂ ⊔ b₂ ⊔ c₂) where
  left  : {x : A₁} {y : B₁} (x~₁y : x ~₁ y) → (_~₁_ ∥ _~₂_) (inj₁ x) (inj₁ y)
  right : {x : A₂} {y : B₂} (x~₂y : x ~₂ y) → (_~₁_ ∥ _~₂_) (inj₂ x) (inj₂ y)

-- Non-working ``eliminator'' for this type.
[_∥_] : {a₁ b₁ c₁ a₂ b₂ c₂ ℓ : Level}
        {A₁ : Set a₁} {B₁ : Set b₁} {_~₁_ : A₁ → B₁ → Set c₁}
        {A₂ : Set a₂} {B₂ : Set b₂} {_~₂_ : A₂ → B₂ → Set c₂}
     →
        {Z : {a : A₁ ⊎ A₂} {b : B₁ ⊎ B₂} → (_~₁_ ∥ _~₂_) a b → Set ℓ}
        (F : {a : A₁} {b : B₁} (a~b : a ~₁ b) → Z (left a~b))
        (G : {a : A₂} {b : B₂} (a~b : a ~₂ b) → Z (right a~b))
     →
        {x : A₁ ⊎ A₂} {y : B₁ ⊎ B₂}
     → (x∥y : (_~₁_ ∥ _~₂_) x y)  → Z x∥y
[ F ∥ G ] (left  x~y) = F x~y
[ F ∥ G ] (right x~y) = G x~y

-- If the argument relations are symmetric then so is their parallel composition.
∥-sym : {a a′ c c′ : Level} {A : Set a} {_~_ : A → A → Set c}
  {A′ : Set a′} {_~′_ : A′ → A′ → Set c′}
  (sym₁ : {x y : A} → x ~ y → y ~ x) (sym₂ : {x y : A′} → x ~′ y → y ~′ x)
  {x y : A ⊎ A′}
  →
    (_~_ ∥ _~′_) x y → (_~_ ∥ _~′_) y x
∥-sym sym₁ sym₂ (left x~y )  =  left  (sym₁ x~y)
∥-sym sym₁ sym₂ (right x~y)  =  right (sym₂ x~y)
--
-- ought to be just: |[ left ∘ sym₁ ∥ right ∘ sym₂ ]|
---
-- Instead, I can use, with much distasteful yellow,
-- |∥-sym sym₁ sym₂ = [ (λ pf → left (sym₁ pf)) ∥ (λ pf → right (sym₂ pf)) ] |

infix 3 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊔ i₂) (i₁ ⊔ i₂ ⊔ k₁ ⊔ k₂)
A ⊎⊎ B = record
  { Carrier = A₀ ⊎ B₀
  ; _≈_ = ≈₁ ∥ ≈₂
  ; isEquivalence = record
    { refl   =  λ{ {inj₁ x} → left refl₁ ; {inj₂ x} → right refl₂ }
    ; sym    =  λ{ (left eq) → left (sym₁ eq) ; (right eq) → right (sym₂ eq)}
                -- ought to be writable as [ left ∘ sym₁ ∥ right ∘ sym₂ ]
    ; trans  =  λ{  (left  eq) (left  eqq) → left  (trans₁ eq eqq)
                  ; (right eq) (right eqq) → right (trans₂ eq eqq)
                  }
    }
  }
  where
    open Setoid A renaming (Carrier to A₀ ; _≈_ to ≈₁ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁)
    open Setoid B renaming (Carrier to B₀ ; _≈_ to ≈₂ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂)
\end{code}
%}}}

%{{{ \subsection{|⊎⊎-comm|}
\subsection{|⊎⊎-comm|}
\begin{code}
⊎⊎-comm : {a b aℓ bℓ : Level} {A : Setoid a aℓ} {B : Setoid b bℓ} → (A ⊎⊎ B)  ≅  (B ⊎⊎ A)
⊎⊎-comm {A = A} {B} = record
  { to           =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥   }
  ; from         =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥′ }
  ; inverse-of   =  record { left-inverse-of = swap²≈∥≈id ; right-inverse-of = swap²≈∥≈id′ }
  }
  where

    open Setoid A renaming (Carrier to A₀ ; _≈_ to ≈₁ ; refl to refl₁)
    open Setoid B renaming (Carrier to B₀ ; _≈_ to ≈₂ ; refl to refl₂)

    swap-on-∥ : {i j : A₀ ⊎ B₀} → (≈₁ ∥ ≈₂) i j → (≈₂ ∥ ≈₁) (swap₊ i) (swap₊ j)
    swap-on-∥ (left  x∼₁y)  =  right x∼₁y
    swap-on-∥ (right x∼₂y)  =  left  x∼₂y

    swap²≈∥≈id : (z : A₀ ⊎ B₀) → (≈₁ ∥ ≈₂) (swap₊ (swap₊ z)) z
    swap²≈∥≈id (inj₁ _)  =  left  refl₁
    swap²≈∥≈id (inj₂ _)  =  right refl₂

    {-
       Tried to obtain the following via |∥-sym| ...
    -}

    swap-on-∥′ : {i j : B₀ ⊎ A₀} → (≈₂ ∥ ≈₁) i j → (≈₁ ∥ ≈₂) (swap₊ i) (swap₊ j)
    swap-on-∥′ (left  x~y) = right x~y
    swap-on-∥′ (right x~y) = left  x~y

    swap²≈∥≈id′ : (z : B₀ ⊎ A₀) → (≈₂ ∥ ≈₁) (swap₊ (swap₊ z)) z
    swap²≈∥≈id′ (inj₁ _)  =  left  refl₂
    swap²≈∥≈id′ (inj₂ _)  =  right refl₁
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
