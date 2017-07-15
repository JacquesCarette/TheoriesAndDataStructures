\section{Parallel Composition}

%{{{ Imports
\begin{code}
module ParComp where

open import Level
open import Relation.Binary    using  (Setoid; REL; Rel)
open import Function           using  (_∘_)
open import Function.Equality  using  (Π; _⟨$⟩_; cong)
open import Function.Inverse   using  () renaming (_InverseOf_ to Inv)

open import DataProperties
open import SetoidEquiv
open import ISEquiv

open import TypeEquiv using (swap₊)
\end{code}
%}}}

%{{{ \subsection{Parallel Composition} _∥_ ; [_∥_] ; ∥-sym ; _⊎⊎_
\subsection{Parallel Composition}

Parallel composition of heterogeneous relations.

\begin{code}
data _∥_ {a₁ b₁ c₁ a₂ b₂ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} {A₂ : Set a₂} {B₂ : Set b₂}
  (R₁ : REL A₁ B₁ c₁) (R₂ : REL A₂ B₂ c₂)
  : REL (A₁ ⊎ A₂) (B₁ ⊎ B₂) (c₁ ⊔ c₂) where
  left  : {x : A₁} {y : B₁} (r₁ : R₁ x y) → (R₁ ∥ R₂) (inj₁ x) (inj₁ y)
  right : {x : A₂} {y : B₂} (r₂ : R₂ x y) → (R₁ ∥ R₂) (inj₂ x) (inj₂ y)

elim : {a₁ b₁ a₂ b₂ c₁ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} {A₂ : Set a₂} {B₂ : Set b₂}
  {R₁ : REL A₁ B₁ c₁} {R₂ : REL A₂ B₂ c₂}
  (P : {a : A₁ ⊎ A₂} {b : B₁ ⊎ B₂} (pf : (R₁ ∥ R₂) a b) → Set (c₁ ⊔ c₂))
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
  elim (λ {a b} (x : (R₁ ∥ R₂) a b) → (R₁ ∥ R₂) b a) (left ∘ sym₁) (right ∘ sym₂) pf

∥-trans : {a a′ ℓ ℓ′ : Level} (A : Setoid a ℓ) (A′ : Setoid a′ ℓ′)
  {x y z : Setoid.Carrier A ⊎ Setoid.Carrier A′} →
  let R₁ = Setoid._≈_ A in let R₂ = Setoid._≈_ A′ in
  (R₁ ∥ R₂) x y → (R₁ ∥ R₂) y z → (R₁ ∥ R₂) x z
∥-trans A A′ {inj₁ x} (left r₁) (left r₂) = left (Setoid.trans A r₁ r₂)
∥-trans A A′ {inj₂ y₂} (right r₂) (right r₃) = right (Setoid.trans A′ r₂ r₃)

-- Motivation for introducing parallel composition:
infix 3 _⊎⊎_ _⊎S_
_⊎S_ : {ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} → Setoid ℓA₁ ℓa₁ → Setoid ℓA₂ ℓa₂ → Setoid (ℓA₁ ⊔ ℓA₂) (ℓa₁ ⊔ ℓa₂)
S₁ ⊎S S₂ = record
  { Carrier = s₁ ⊎ s₂
  ; _≈_ = _≈₁_ ∥ _≈₂_
  ; isEquivalence = record
    { refl = λ { {inj₁ x} → left refl₁ ; {inj₂ y} → right refl₂ }
    ; sym = ∥-sym sym₁ sym₂
    ; trans = ∥-trans S₁ S₂
    }
  }
  where
    open Setoid S₁ renaming (Carrier to s₁; _≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁)
    open Setoid S₂ renaming (Carrier to s₂; _≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂)
    R = λ x y → (_≈₁_ ∥ _≈₂_) x y

_⊎⊎_ : {ℓS ℓs ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} {S : Setoid ℓS ℓs}
  → SetoidFamily S ℓA₁ ℓa₁ → SetoidFamily S ℓA₂ ℓa₂ → SetoidFamily S _ _
X ⊎⊎ Y = record
  { index = λ s → A.index s ⊎S B.index s
  ; reindex = λ x≈y → record
    { _⟨$⟩_ = (λ y → A.reindex x≈y ⟨$⟩ y) ⊎₁ (λ y → B.reindex x≈y ⟨$⟩ y)
    ; cong = λ { (left r₁) → left (Π.cong (A.reindex x≈y) r₁)
               ; (right r₂) → right (Π.cong (B.reindex x≈y) r₂) }
    }
  ; id-coh = λ { {a} {inj₁ x} → left A.id-coh ; {a} {inj₂ y} → right B.id-coh}
  ; sym-iso = λ x≈y → record
    { left-inverse-of = [ (λ x → left (Inv.left-inverse-of (A.sym-iso x≈y) x)) ,
                          (λ x → right (Inv.left-inverse-of (B.sym-iso x≈y) x)) ]
    ; right-inverse-of = [ (λ x → left (Inv.right-inverse-of (A.sym-iso x≈y) x)) ,
                           (λ y → right (Inv.right-inverse-of (B.sym-iso x≈y) y)) ]
    }
  ; trans-coh = λ { {b = inj₁ _} a≈b b≈c → left (A.trans-coh a≈b b≈c )
                  ; {b = inj₂ _} x≈y y≈z → right (B.trans-coh x≈y y≈z) }
  }
    where
      module A = SetoidFamily X
      module B = SetoidFamily Y
\end{code}
%}}}

%{{{ \subsection{|⊎⊎-comm|}
\subsection{|⊎⊎-comm|}
\begin{spec}
⊎⊎-comm : {ℓS ℓs ℓA ℓB ℓa ℓb : Level} {S : Setoid ℓS ℓs} →
  let s = Setoid.Carrier S in
  {A : I.Setoid s ℓA ℓa} {B : I.Setoid s ℓB ℓb} → IndexedSetoidEquivalence S (A ⊎⊎ B) (B ⊎⊎ A)
⊎⊎-comm {S = S} {A} {B} {x} {y} x≈y = record
  { to = record { _⟨$⟩_ = [ inj₂ ∘ {!!} , {!!} ] ; cong = {!!} }
  ; from = record { _⟨$⟩_ = {!!} ; cong = {!!} }
  ; inverse-of = record { left-inverse-of = {!!} ; right-inverse-of = {!!} }
  }
  {- record
  { to           =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥   }
  ; from         =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥′ }
  ; inverse-of   =  record { left-inverse-of = swap²≈∥≈id ; right-inverse-of = swap²≈∥≈id′ }
  -}
  where

    open I.Setoid A renaming (Carrier to A₀ ; _≈_ to ≈₁ ; refl to refl₁)
    open I.Setoid B renaming (Carrier to B₀ ; _≈_ to ≈₂ ; refl to refl₂)

    swap-on-∥ : {i j : A₀ x ⊎ B₀ x} → (≈₁ ∥ ≈₂) i j → (≈₂ ∥ ≈₁) (swap₊ i) (swap₊ j)
    swap-on-∥ (left  x∼₁y)  =  right x∼₁y
    swap-on-∥ (right x∼₂y)  =  left  x∼₂y

    swap²≈∥≈id : (z : A₀ x ⊎ B₀ x) → (≈₁ ∥ ≈₂) (swap₊ (swap₊ z)) z
    swap²≈∥≈id (inj₁ _)  =  left  refl₁
    swap²≈∥≈id (inj₂ _)  =  right refl₂

    {-
       Tried to obtain the following via |∥-sym| ...
    -}

    swap-on-∥′ : {i j : B₀ x ⊎ A₀ x} → (≈₂ ∥ ≈₁) i j → (≈₁ ∥ ≈₂) (swap₊ i) (swap₊ j)
    swap-on-∥′ (left  x~y) = right x~y
    swap-on-∥′ (right x~y) = left  x~y

    swap²≈∥≈id′ : (z : B₀ x ⊎ A₀ x) → (≈₂ ∥ ≈₁) (swap₊ (swap₊ z)) z
    swap²≈∥≈id′ (inj₁ _)  =  left  refl₂
    swap²≈∥≈id′ (inj₂ _)  =  right refl₁
\end{spec}
%}}}

%{{{ \subsection{|⊎⊎₁|}
\subsection{|⊎⊎₁| - parallel composition of equivalences}
\begin{spec}
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
\end{spec}
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
