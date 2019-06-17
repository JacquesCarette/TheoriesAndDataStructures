\section{First}

JC: Just made the Agda work, this needs massively cleaned up (names, etc).

%{{{ Imports
\begin{code}
module Structures.RightUnar where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (const ; id ; _∘_ ; _$_)
open import Data.Empty
open import Data.Nat using (ℕ ; zero ; suc)

open import Helpers.Categorical
open import Helpers.Function2 using (_$ᵢ)
open import Helpers.Forget
open import Helpers.EqualityCombinators

import Structures.UnaryAlgebra as U
\end{code}
%}}}

%{{{ RightUnar ; Hom
\subsection{Definition}
\begin{code}

record RightUnar ℓ : Set (lsuc ℓ) where
  constructor RU
  field
    Carrier : Set ℓ
    _*_      : Carrier → Carrier → Carrier
    ignore-right : ∀ x y z → x * y ≡ x * z

open RightUnar

record Hom {ℓ} (X Y : RightUnar ℓ) : Set ℓ where
  constructor hom
  open RightUnar X using () renaming (_*_ to _*₁_)
  open RightUnar Y using () renaming (_*_ to _*₂_)
  field
    mor          : Carrier X → Carrier Y
    pres-* : {x y : Carrier X} → mor (x *₁ y) ≡ mor x *₂ mor y

open Hom
\end{code}

%}}}

%{{{
\subsection{Category and Forgetful Functor}
\begin{code}
RightUnarAlg : {ℓ : Level} → OneSortedAlg ℓ
RightUnarAlg {ℓ} = record
  { Alg         =   RightUnar ℓ
  ; Carrier     =   Carrier
  ; Hom         =   Hom
  ; mor         =   mor
  ; comp        =   λ F G → record
    { mor       =   mor F ∘ mor G
    ; pres-*    =   ≡.cong (mor F) (pres-* G) ⟨≡≡⟩ pres-* F
    }
  ; comp-is-∘   =   ≐-refl
  ; Id          =   hom id ≡.refl
  ; Id-is-id    =   ≐-refl
  }

RightUnars : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
RightUnars ℓ = oneSortedCategory ℓ RightUnarAlg

Forget : (ℓ : Level) → Functor (RightUnars ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ RightUnarAlg
\end{code}

%}}}

%{{{
\subsection{Syntax}
\begin{code}
data Thing {a : Level} (A : Set a) : Set a where
  Raw : A → ℕ → Thing A

open Thing

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Thing A → Thing B
map f (Raw a n) = Raw (f a) n
\end{code}

The \AgdaField{ignore-right} law tells us what to do when we 'act'.
\begin{code}
combine : {a : Level} {A : Set a} → Thing A → Thing A → Thing A
combine (Raw x n) _ = Raw x (suc n)
\end{code}

and that \AgdaFunction{combine} generally ignores its right argument
\begin{code}
combine-ignores-right : ∀ {ℓ : Level} {X : Set ℓ} (x y z : Thing X) → combine x y ≡ combine x z
combine-ignores-right (Raw x _) _ _ = ≡.refl
\end{code}
%}}}

%{{{
\begin{code}
map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
         → f ≐ᵢ g
         → map f ≐ map g
map-cong f≡g (Raw x n) = ≡.cong (λ z → Raw z n) (f≡g {x})

RightUnarF : (ℓ : Level) → Functor (Sets ℓ) (RightUnars ℓ)
RightUnarF ℓ = record
  { F₀ = λ A → RU (Thing A) combine combine-ignores-right
  ; F₁ = λ f → hom (map f) λ { {Raw x n} → ≡.refl}
  ; identity = λ { (Raw x n) → ≡.refl}
  ; homomorphism = λ { (Raw x n) → ≡.refl}
  ; F-resp-≡ = map-cong
  }
\end{code}

``fold'' in this case is perhaps just as well called eval. It applies the
action n times, but we know we can pick any value on the 'right', so we
may as well pick x.

\begin{code}
eval : {ℓ : Level} (M : RightUnar ℓ) → Thing (Carrier M) → Carrier M
eval M (Raw x zero) = x
eval M (Raw x (suc n)) = _*_ M (eval M (Raw x n)) x
\end{code}

We also have an induction principle:
\begin{code}
ind : {ℓ ℓ′ : Level} {Y : Set ℓ}
      (P : Thing Y → Set ℓ′)
    → ((y : Y) → P (Raw y zero))
    → ((y : Y) (n : ℕ) → P (Raw y n) → P (Raw y (suc n)))
    → (z : Thing Y) → P z
ind P zp sp (Raw x zero) = zp x
ind P zp sp (Raw x (suc n)) = sp x n (ind P zp sp (Raw x n))
\end{code}

We can now use induction to prove that eval is natural.
\begin{code}
eval-naturality : {ℓ : Level} {M N : RightUnar ℓ} (F : Hom M N)
                → eval N ∘ map (mor F) ≐ mor F ∘ eval M
eval-naturality {ℓ} {M} {N} F = ind (λ x → eval N (map (mor F) x) ≡ mor F (eval M x))
  (λ _ → ≡.refl) λ y n ev-nat-n → ≡.trans (≡.cong (λ z → _*_ N z (mor F y)) ev-nat-n)
  (≡.sym (pres-* F))
\end{code}

But that eval ``computes'' does not need induction per se, so a direct proof is nicer.
\begin{code}
eval-compute : {ℓ : Level} (A : RightUnar ℓ) (x : Carrier A) (n : ℕ) (y : Thing (Carrier A)) →
  _*_ A (eval A (Raw x n)) x ≡ _*_ A (eval A (Raw x n)) (eval A y)
eval-compute A x zero y = ignore-right A x x _
eval-compute A x (suc n) y = ignore-right A (_*_ A (eval A (Raw x n)) x) x (eval A y)
\end{code}

Lastly, we need to show that ``folding'' combine over a nested composition recovers
the thing we started with. We'll do this one by Agda-level induction.

\begin{code}
eval-combine : ∀ {ℓ : Level} {X : Set ℓ} (x : X) (n : ℕ) →
  Raw x n ≡ eval (RU (Thing X) combine (combine-ignores-right {X = X} )) (Raw (Raw x 0) n)
eval-combine x zero = ≡.refl
eval-combine x (suc n) = ≡.cong (λ z → combine z (Raw x 0)) (eval-combine x n)
\end{code}

And we can put everything together to show that indeed we have an adjunction.
\begin{code}
LeftThing : (ℓ : Level) → Adjunction (RightUnarF ℓ) (Forget ℓ)
LeftThing ℓ = record
  { unit    =  record { η = λ _ x → Raw x 0 ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ A → hom (eval A) λ { {Raw x n} {y} → eval-compute A x n y }
    ; commute  =  eval-naturality
    }
  ; zig   =   λ { (Raw x n) → eval-combine x n}
  ; zag   =   ≡.refl
  }
\end{code}

What is perhaps not immediately apparent is that this is a structure we've seen before.
\begin{code}
iso : (ℓ : Level) → StrongEquivalence (RightUnars ℓ) (U.Unarys ℓ)
iso ℓ = record
  { F = record
    { F₀ = λ { (RU X _*_ _) → U.MkUnary X λ x → x * x}
    ; F₁ = λ { (hom mor₁ pres-*₁) → U.MkHom mor₁ λ {x} → pres-*₁ {x} {x}}
    ; identity = λ _ → ≡.refl
    ; homomorphism = λ _ → ≡.refl
    ; F-resp-≡ = id
    }
  ; G = record
    { F₀ = λ { (U.MkUnary Carrier₁ Op) → RU Carrier₁ (λ x _ → Op x) λ _ _ _ → ≡.refl}
    ; F₁ = λ { (U.MkHom mor₁ pres-op) → hom mor₁ λ {x} → pres-op {x}}
    ; identity = λ _ → ≡.refl
    ; homomorphism = λ _ → ≡.refl
    ; F-resp-≡ = id
    }
  ; weak-inverse = record
    { F∘G≅id = record
      { F⇒G = record { η = λ X → U.MkHom id ≡.refl ; commute = λ _ _ → ≡.refl }
      ; F⇐G = record { η = λ X → U.MkHom id ≡.refl ; commute = λ _ _ → ≡.refl }
      ; iso = λ X → record { isoˡ = λ x → ≡.refl ; isoʳ = λ _ → ≡.refl }
      }
    ; G∘F≅id = record
      { F⇒G = record { η = λ X → hom id λ {x} {y} → ignore-right X x x y ; commute = λ _ _ → ≡.refl }
      ; F⇐G = record { η = λ X → hom id λ {x} {y} → ignore-right X x y x ; commute = λ _ _ → ≡.refl }
      ; iso = λ X → record { isoˡ = λ _ → ≡.refl ; isoʳ = λ _ → ≡.refl }
      }
    }
  }
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
