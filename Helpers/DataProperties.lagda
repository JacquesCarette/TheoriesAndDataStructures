\section{Properties of Sums and Products}

This module is for those domain-ubiquitous properties that, disappointingly,
we could not locate in the standard library. ---The standard library needs some
sort of ``table of contents \emph{with} subsection'' to make it easier to know
of what is available.

This module re-exports (some of) the contents of the standard library's |Data.Product| and |Data.Sum|.

%{{{ Imports
\begin{code}
module DataProperties where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (id ; _∘_ ; const)
open import EqualityCombinators

open import Data.Product public using (_×_; proj₁; proj₂; Σ; _,_; swap ; uncurry) renaming (map to _×₁_ ; <_,_> to ⟨_,_⟩)
open import Data.Sum     public using (inj₁; inj₂; [_,_])  renaming (map to _⊎₁_)
open import Data.Nat            using (ℕ; zero; suc)
\end{code}

\subsection*{Precedence Levels}

The standard library assigns precedence level of 1 for the infix operator |_⊎_|,
which is rather odd since infix operators ought to have higher precedence that equality
combinators, yet the standard library assigns |_≈⟨_⟩_| a precedence level of 2.
The usage of these two ---e.g. in |CommMonoid.lagda|--- causes an annoying number of
parentheses and so we reassign the level of the infix operator to avoid such a situation.

\begin{code}
infixr 3 _⊎_
_⊎_ = Data.Sum._⊎_
\end{code}

%}}}

%{{{ Generalised Bot and Top
\subsection{Generalised Bot and Top}
To avoid a flurry of |lift|'s, and for the sake of clarity, we define level-polymorphic
empty and unit types.
\begin{code}
open import Level

data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : {a ℓ : Level} {A : Set a} → ⊥ {ℓ} → A
⊥-elim ()

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt
\end{code}
%}}}

%{{{ sums
\subsection{Sums}

   %{{{ the ⊎ operation on functions is a functorial congruence

Just as |_⊎_| takes types to types, its ``map'' variant |_⊎₁_| takes
functions to functions and is a functorial congruence:
It preserves identity, distributes over composition, and preserves
extenstional equality.

\begin{code}
⊎-id : {a b : Level} {A : Set a} {B : Set b} → id ⊎₁ id ≐ id {A = A ⊎ B}
⊎-id = [ ≐-refl , ≐-refl ]

⊎-∘ : {a b c a' b' c' : Level}
        {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} {C' : Set c} {C : Set c'}
        {f  : A → A'} {g : B → B'} {f' : A' → C} {g' : B' → C'}
      → (f' ∘ f) ⊎₁ (g' ∘ g) ≐ (f' ⊎₁ g') ∘ (f ⊎₁ g) --- aka “the exchange rule for sums”
⊎-∘ = [ ≐-refl , ≐-refl ]

⊎-cong : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {f f' : A → C} {g g' : B → D}
       → f ≐ f' → g ≐ g' → f ⊎₁ g ≐ f' ⊎₁ g'
⊎-cong f≈f' g≈g' = [ ∘-≐-cong₂ inj₁ f≈f' , ∘-≐-cong₂ inj₂ g≈g' ]
\end{code}
%}}}

   %{{{ ∘-[,] : fusion property for casing

Composition post-distributes into casing,

\begin{code}
∘-[,] : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {f : A → C} {g : B → C} {h : C → D}
     → h ∘ [ f , g ] ≐ [ h ∘ f , h ∘ g ]   -- aka “fusion”
∘-[,] = [ ≐-refl , ≐-refl ]
\end{code}

%}}}

   %{{{ from⊎ : the dual to |diag|

It is common that a data-type constructor |D : Set → Set| allows us to extract
elements of the underlying type and so we have a natural transfomation |D ⟶ 𝑰|,
where |𝑰| is the identity functor.
These kind of results will occur for our other simple data-strcutres as well.
In particular, this is the case for |D A = 2× A = A ⊎ A|:

\begin{code}
from⊎ : {ℓ : Level} {A : Set ℓ} → A ⊎ A → A
from⊎ = [ id , id ]

-- |from⊎| is a natural transformation
--
from⊎-nat : {a b : Level} {A : Set a} {B : Set b}{f : A → B} → f ∘ from⊎  ≐ from⊎ ∘ (f ⊎₁ f)
from⊎-nat = [ ≐-refl , ≐-refl ]

-- |from⊎| is injective and so is pre-invertible,
--
from⊎-preInverse : {a b : Level} {A : Set a} {B : Set b} → id ≐ from⊎ {A = A ⊎ B} ∘ (inj₁ ⊎₁ inj₂)
from⊎-preInverse = [ ≐-refl , ≐-refl ]
\end{code}

\edinsert{MA}{A brief mention about co-monads?}

%}}}

%}}}

%{{{ products: diag
\subsection{Products}
Dual to |from⊎|, a natural transformation |2×_ ⟶ 𝑰|, is |diag|, the transformation |𝑰 ⟶ _²|.

\begin{code}
diag : {ℓ : Level} {A : Set ℓ} (a : A) → A × A
diag a = a , a
\end{code}

\edinsert{MA}{ A brief mention of Haskell's |const|, which is |diag| curried. Also something about |K| combinator? }

Z-style notation for sums,
\begin{code}
Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Σ∶• = Data.Product.Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B
\end{code}

%}}}

%{{{ suc is injective
\begin{code}
open import Data.Nat.Properties
suc-inj : ∀ {i j} → ℕ.suc i ≡ ℕ.suc j → i ≡ j
suc-inj = cancel-+-left (ℕ.suc ℕ.zero)
\end{code}
or
\begin{spec}
suc-inj {0} _≡_.refl = _≡_.refl
suc-inj {ℕ.suc i} _≡_.refl = _≡_.refl
\end{spec}

%}}}

%{{{ vectors: _‼_

\begin{code}
open import Data.Fin using (Fin)
open import Data.Vec using (Vec ; lookup)

_‼_ : {a : Level} {A : Set a} {n : ℕ} → Vec A n → Fin n → A
_‼_ = λ xs i → lookup i xs
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
