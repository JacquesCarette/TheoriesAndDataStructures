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
    ignore-right    : ∀ x y z → x * y ≡ x * z

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

The \AgdaField{ignore-right} law tells us what to do when we 'act':
\begin{code}
combine : {a : Level} {A : Set a} → Thing A → Thing A → Thing A
combine (Raw x n) _ = Raw x (suc n)
\end{code}

Given the proof obligations below, probably an 'induction' combinator might make sense.
%}}}

%{{{
\begin{code}
map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
         → f ≐ᵢ g
         → map f ≐ map g
map-cong f≡g (Raw x n) = ≡.cong (λ z → Raw z n) (f≡g {x})

RightUnarF : (ℓ : Level) → Functor (Sets ℓ) (RightUnars ℓ)
RightUnarF ℓ = record
  { F₀ = λ A → RU (Thing A) combine
      λ { (Raw x n) (Raw x₁ _) (Raw x₂ _) → ≡.refl}
  ; F₁ = λ f → hom (map f) λ { {Raw x n} → ≡.refl}
  ; identity = λ { (Raw x n) → ≡.refl}
  ; homomorphism = λ { (Raw x n) → ≡.refl}
  ; F-resp-≡ = map-cong
  }

-- evaluation applies the action n times. We can pick any value, so pick x !
eval : {ℓ : Level} (M : RightUnar ℓ) → Thing (Carrier M) → Carrier M
eval M (Raw x zero) = x
eval M (Raw x (suc n)) = _*_ M (eval M (Raw x n)) x

eval-naturality : {ℓ : Level} {M N : RightUnar ℓ} (F : Hom M N)
                → eval N ∘ map (mor F) ≐ mor F ∘ eval M
eval-naturality {ℓ} {M} {N} F (Raw x zero) = ≡.refl
eval-naturality {ℓ} {M} {N} F (Raw x (suc n)) = {!!}

eval-compute : {ℓ : Level} (A : RightUnar ℓ) (x : Carrier A) (n : ℕ) (y : Thing (Carrier A)) →
  _*_ A (eval A (Raw x n)) x ≡ _*_ A (eval A (Raw x n)) (eval A y)
eval-compute A x zero y = ignore-right A x x _
eval-compute A x (suc n) y = ignore-right A (_*_ A (eval A (Raw x n)) x) x (eval A y)

LeftThing : (ℓ : Level) → Adjunction (RightUnarF ℓ) (Forget ℓ)
LeftThing ℓ = record
  { unit    =  record { η = λ _ x → Raw x 0 ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ A → hom (eval A) λ { {Raw x n} {y} → eval-compute A x n y }
    ; commute  =  eval-naturality
    }
  ; zig   =   λ { (Raw x n) → {!!}}
  ; zag   =   ≡.refl
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
