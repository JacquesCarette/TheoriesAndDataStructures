\section{Parallel Composition}

%{{{ Imports
\begin{code}
module ParComp where

open import Level
open import Relation.Binary    using  (Setoid)
open import Function           using  (_∘_)
open import Function.Equality  using  (Π; _⟨$⟩_; cong)

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

-- non-dependent eliminator
[_∥_]′ : {a₁ b₁ c₁ a₂ b₂ c₂ ℓ : Level}
        {A₁ : Set a₁} {B₁ : Set b₁} {_~₁_ : A₁ → B₁ → Set c₁}
        {A₂ : Set a₂} {B₂ : Set b₂} {_~₂_ : A₂ → B₂ → Set c₂}
     →
        {Z : (a : A₁ ⊎ A₂) (b : B₁ ⊎ B₂) → Set ℓ}
        (F : {a : A₁} {b : B₁} (a~b : a ~₁ b) → Z (inj₁ a) (inj₁ b))
        (G : {a : A₂} {b : B₂} (a~b : a ~₂ b) → Z (inj₂ a) (inj₂ b))
     →
        {x : A₁ ⊎ A₂} {y : B₁ ⊎ B₂}
     → (_~₁_ ∥ _~₂_) x y  → Z x y
[ F ∥ G ]′ (left  x~y) = F x~y
[ F ∥ G ]′ (right x~y) = G x~y

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
--
-- Instead, I can use, with much distasteful yellow,
-- |∥-sym sym₁ sym₂ = [ left ∘ sym₁ ∥ right ∘ sym₂ ]′|

-- Motivation for introducing parallel composition:
infix 3 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊔ i₂) (i₁ ⊔ i₂ ⊔ k₁ ⊔ k₂)
A ⊎⊎ B = record
  { Carrier         =   A₀ ⊎ B₀
  ; _≈_             =   ≈₁ ∥ ≈₂
  ; isEquivalence   =   record
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

%{{{ \subsection{|⊎⊎₁|}
\subsection{|⊎⊎₁| - parallel composition of equivalences}
\begin{code}
_⊎⊎₁_ : {a b c d aℓ bℓ cℓ dℓ : Level} {A : Setoid a aℓ} {B : Setoid b bℓ} {C : Setoid c cℓ}
  {D : Setoid d dℓ} → A ≅ C → B ≅ D → (A ⊎⊎ B) ≅ (C ⊎⊎ D)
_⊎⊎₁_ {A = A} {B} {C} {D} A≅C B≅D = record
  { to           =   record { _⟨$⟩_ = A→C   ⊎₁ B→D ; cong = cong-AB }
  ; from         =   record { _⟨$⟩_ = _⟨$⟩_ (from A≅C) ⊎₁ _⟨$⟩_ (from B≅D) ; cong = cong-CD }
  ; inverse-of   =   record { left-inverse-of  = left-inv ; right-inverse-of = right-inv }
  }
  where
  
    open _≅_
    
    A→C = _⟨$⟩_ (to A≅C)
    B→D = _⟨$⟩_ (to B≅D)
    C→A = _⟨$⟩_ (from A≅C)
    D→B = _⟨$⟩_ (from B≅D)
    
    open Setoid A renaming (Carrier to AA; _≈_ to _≈₁_)
    open Setoid B renaming (Carrier to BB; _≈_ to _≈₂_)
    open Setoid C renaming (Carrier to CC; _≈_ to _≈₃_)
    open Setoid D renaming (Carrier to DD; _≈_ to _≈₄_)

    _≈∥≈₁₂_  =  _≈₁_ ∥ _≈₂_
    _≈∥≈₃₄_  =  _≈₃_ ∥ _≈₄_

    cong-AB : {i j : AA ⊎ BB} → i ≈∥≈₁₂ j → (A→C ⊎₁ B→D) i  ≈∥≈₃₄  (A→C ⊎₁ B→D) j
    cong-AB (left x~₁y) = left   (cong (to A≅C) x~₁y)
    cong-AB (right x~₂y) = right (cong (to B≅D) x~₂y)

    cong-CD : {i j : CC ⊎ DD} → i ≈∥≈₃₄ j → (C→A ⊎₁ D→B) i  ≈∥≈₁₂  (C→A ⊎₁ D→B) j
    cong-CD (left x~₁y) = left   (cong (from A≅C) x~₁y)
    cong-CD (right x~₂y) = right (cong (from B≅D) x~₂y)

    left-inv : (x : AA ⊎ BB) → (C→A ⊎₁ D→B) ((A→C ⊎₁ B→D) x)  ≈∥≈₁₂  x
    left-inv (inj₁ x) = left  (left-inverse-of A≅C x)
    left-inv (inj₂ y) = right (left-inverse-of B≅D y)

    right-inv : (x : CC ⊎ DD) → (A→C ⊎₁ B→D) ((C→A ⊎₁ D→B) x)  ≈∥≈₃₄  x
    right-inv (inj₁ x) = left  (right-inverse-of A≅C x)
    right-inv (inj₂ y) = right (right-inverse-of B≅D y)

    -- \edcomm{MA}{Ideally the eliminator would work and we'd use it to simplify the above inv-proofs.}
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
