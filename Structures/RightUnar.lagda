\section{First}

A \emph{Right Unar} is a magma whose operation is constant in the first argument
and in some sense is an \emph{indexed} unary algebra since every element gives rise
to a unique unary operation.

\edcomm{MA}{

According to wikipedia, https://en.wikipedia.org/wiki/Magma_(algebra),
what we have below is actually a “left unar”! However, if we change perspective
by thinking of “*” as backwards composition, as WK does with “⨾”, then our name
is “not wrong”. However, such duality is pervasive in categorial settings.

Instead, it may be prudent to simply call our structures “Pre-Unars”
since it is the argument at the ‘pre’ position for which the axiom focuses on.
Likewise, “post-unars”.

JC, please provide links to where more info on unars can be found.
}

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

import Structures.UnaryAlgebra as U hiding (Forget)
\end{code}
%}}}

%{{{ RightUnar ; Hom
\subsection{Definition}
\begin{code}
record RightUnar ℓ : Set (lsuc ℓ) where
  constructor RU
  field
    Carrier      : Set ℓ
    _*_          : Carrier → Carrier → Carrier
    ignore-right : ∀ x y z → x * y ≡ x * z

open RightUnar

record Hom {ℓ} (X Y : RightUnar ℓ) : Set ℓ where
  constructor hom
  open RightUnar X using () renaming (_*_ to _*₁_)
  open RightUnar Y using () renaming (_*_ to _*₂_)
  field
    mor    : Carrier X → Carrier Y
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

%{{{ The free pre-unar
\subsection{Syntax}

Suppose we wish to construct right unar terms over some set $A$, then our options are
\begin{enumerate}
\item A variable of type $A$,
\item An expression $l * r$ for two existing terms $l$ and $r$.
\end{enumerate}
Unfolding this definition shows that terms are of the form
$x_0 * x_1 * ⋯ * x_n$ for some parenthesising.

If we parenthesise right-wards, then we find that by the “ignore-right”
axiom, the important pieces of the term are its left-most element
and how many arguments ---the remaining right side--- were used in
producing the term. Note that “ignore-right” informs us that any
right hand expression would do, even $x_0$ itself, so since the remaining
$x_i$ do not matter, semantically, the term can be \emph{reconstructed}
provided we supply $n$ arbitrary elements of $A$. This is nearly a “cons”
for the free monoid, but since only the length of the tail of the list
is important, that is all we keep.

Hence, we could use $A × ℕ$ as a representation of the free algebra of this type.
However, we have hinted at the resemblance ot unary algebras and indeed we find
the type $Eventually A \;≅\; A × ℕ$ already there. Let's use it.
\begin{code}
open import Structures.UnaryAlgebra hiding (Forget ; Hom)
{-
data Eventually {ℓ} (A : Set ℓ) : Set ℓ where
  base   :              A → Eventually A
  step   :   Eventually A → Eventually A
-}
\end{code}

Before conjecturing further, let's write an interpreter to gain confidence
that we're moving in the correct trajectory (•̀ᴗ•́)و

Our interpreter, fold, eval, whatever you wish to call it applies the
action “n” times, but we know we can pick any value on the ‘right’, so we
may as well pick the base element. Incidentally, the “extract” below
could have been renamed “force”.

\begin{code}
eval : {ℓ : Level} (M : RightUnar ℓ) → Eventually (Carrier M) → Carrier M
eval M (base x) = x -- *_ M x x
eval M (step x) = _*_ M (eval M x) (extract x)

-- eval M e ≡ iterate (_*_ M (extract e)) e
-- Would require _*_ to be associative.
\end{code}

The \AgdaField{ignore-right} law tells us what to do when we “act”:
\begin{code}
_⟪_ : {a : Level} {A : Set a} → Eventually A → Eventually A → Eventually A
l ⟪ r = step l  {- “LHS l gains another arbitrary argument. ” -}
\end{code}
That is to say, in the alternate representation: $(x, n) ⟪ r  =  (x, n + 1)$.

This operation unquestionablly ignores its second argument and so we have
a functor that produces such pre-unars.
\begin{code}
RightUnarF : (ℓ : Level) → Functor (Sets ℓ) (RightUnars ℓ)
RightUnarF ℓ = record
  { F₀            =  λ A → RU (Eventually A) _⟪_ (λ _ _ _ → ≡.refl)
  ; F₁            =  λ f → hom (map f) ≡.refl
  ; identity      =  reflection
  ; homomorphism  =  elim ≡.refl (≡.cong step)
  ; F-resp-≡      =  map-congᵢ
  }
\end{code}

Note that from “Eventually” we already have induction and elimination rules, and a number of
naturality laws. Here's a direct proof of eval's naturality.

\begin{code}
eval-naturality : {ℓ : Level} {M N : RightUnar ℓ} (F : Hom M N)
                → eval N ∘ map (mor F) ≐ mor F ∘ eval M
eval-naturality {ℓ} {M} {N} F (base x) = ≡.refl -- ≡.sym (pres-* F)
eval-naturality {ℓ} {M} {N} F (step x) = let open ≡.≡-Reasoning in
  begin
   (eval N ∘ map (mor F)) (step x)
  ≡⟨ ≡.refl ⟩
   (eval N ∘ step) (map (mor F) x)
  ≡⟨ ≡.refl ⟩
   _*_ N (eval N ((map (mor F) x))) (extract ((map (mor F) x)))
  ≡⟨ ≡.cong (λ it → _*_ N it (extract ((map (mor F) x)))) (eval-naturality F x) ⟩
   _*_ N (mor F (eval M x)) (extract ((map (mor F) x)))
  ≡⟨ ignore-right N _ _ _ ⟩
   _*_ N (mor F (eval M x)) (mor F (extract x))
  ≡⟨ ≡.sym (pres-* F) ⟩
   mor F (_*_ M (eval M x) (extract x))
  ≡⟨ ≡.refl ⟩
   (mor F ∘ eval M) (step x)
  ∎
\end{code}

Moreover, interpreter is a homomorphism.
\begin{code}
eval-compute : {ℓ : Level} (M : RightUnar ℓ) -- (x : Carrier A) {n : ℕ}
    (x y : Eventually (Carrier M))
  → let _⊕_ = _*_ M
  in
       eval M (x ⟪ y)
    ≡  eval M x ⊕ eval M y

eval-compute M (base x) y = ignore-right M x x (eval M y)
eval-compute M 𝓍@(step x) y = ignore-right M (_*_ M (eval M x) (extract x)) (extract x) (eval M y)


eval-combine : ∀ {ℓ : Level} {X : Set ℓ} (e : Eventually X)
  → e ≡ eval (RU (Eventually X) _⟪_ λ _ _ _ → ≡.refl) (iterate step (base (base e)))
eval-combine _  = ≡.refl
\end{code}

% Lastly, we need to show that ``folding'' combine over a nested composition recovers
% the thing we started with. We'll do this one by Agda-level induction.

Here's a reason for our naming.
\begin{code}
_≈_ : ∀ {ℓ} {A : Set ℓ} (x y : Eventually A) → Set ℓ
l ≈ r  =  extract l  ≡  extract r

{- neato! -}
_ : ∀ {ℓ} {A : Set ℓ} {x y : Eventually A}
  → (x ⟪ y) ≈  x
_ = ≡.refl
\end{code}

And we can put everything together to show that indeed we have an adjunction.

\begin{code}
LeftThing : (ℓ : Level) → Adjunction (RightUnarF ℓ) (Forget ℓ)
LeftThing ℓ = record
  { unit    =  record { η = λ _ → base ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ M → hom (eval M) λ { {x} {y} → eval-compute M x y }
    ; commute  =  eval-naturality
    }
  ; zig   =   λ e → elim  ≡.refl (λ _ → ≡.refl) e
  ; zag   =   ≡.refl
  }
\end{code}

As mentioned, this merely a different presentation of a structure we have already seen.
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
