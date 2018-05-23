\section{|OneCat|: Constant Functions}

Working out the details of an adjunction between sets and
a one-object one-arrow category yields us with the notion
of \emph{constant functions}: Those operations that completely
ignore their input and always yield the same output.

(
  That is, when proving the adjunction, the pattern of constant
  functions --i.e., ignoring arguments in-preference of pre-determined
  or only possible output-- keeps occuring.
)

...Examples of such operations in the wild (i.e., ``real programming'')?...

%{{{ Imports
\begin{code}
module Structures.OneCat where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category     using   (Category)
open import Categories.Functor      using   (Functor)
open import Categories.Adjunction   using   (Adjunction)
open import Categories.Agda         using   (Sets)
open import Function                using   (id ; _∘_ ; const)
open import Function2               using   (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties

𝑲 : {a b : Level} {A : Set a} {B : Set b} → A → B → A
𝑲 a _ = a

𝑲₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A → B → C → A
𝑲₂ a _ _ = a
\end{code}
%}}}

%{{{ |OneCat|
\begin{code}
-- The “formal” object and morphism names coincide; for brevity.
data One {ℓ : Level} : Set ℓ where
  ⋆ : One

-- The One-object One-arrow Category
OneCat : {ℓ : Level} → Category ℓ ℓ ℓ
OneCat {ℓ} = record
  { Obj        =  One {ℓ}
  ; _⇒_       =   𝑲₂ (One {ℓ})
  ; _≡_       =   𝑲₂ (One {ℓ})
  ; id         =  ⋆
  ; _∘_        =  𝑲₂ ⋆
  ; assoc      =  ⋆
  ; identityˡ  =  ⋆
  ; identityʳ  =  ⋆
  ; equiv     =  record
    { refl    =  ⋆
    ; sym     =  λ _ → ⋆
    ; trans   =  𝑲₂ ⋆
    }
  ; ∘-resp-≡ = 𝑲₂ ⋆
  }
\end{code}
%}}}

%{{{ Δ⊢Id

Arrows in the one-object one-arrow category correspond to the functions
to a singleton set.
( Both the former and latter collection of arrows have cardinality 1. )

\begin{code}
-- “forget that |One| is a syntactical item, and realise it as a set.”
Forget : {ℓ : Level} → Functor (OneCat {ℓ}) (Sets ℓ)
Forget {ℓ} = record
  { F₀             =  𝑲 One
  ; F₁             =  𝑲₂ ⋆
  ; identity       =  λ{ {_} {⋆} → ≡.refl }
  ; homomorphism   =  ≡.refl
  ; F-resp-≡      =   λ _ → ≡.refl
  }
--
-- Essentially an inclusion functor; i.e., the identity functor.
-- Might as well call this functor |Id|.

-- “freely adorn any set as a singleton syntactical item by replacing its elements with |⋆|.”
Free : {ℓ : Level} → Functor (Sets ℓ) (OneCat {ℓ}) 
Free {ℓ} = record
  { F₀             = 𝑲 ⋆
  ; F₁             = 𝑲 ⋆
  ; identity       = ⋆
  ; homomorphism   = ⋆
  ; F-resp-≡      = 𝑲 ⋆
  }
--
-- This' essentially a ``constant functor'' (!) and so might as well call it |Δ|.

Δ⊢Id : {ℓ : Level} → Adjunction (Free {ℓ}) (Forget {ℓ})
Δ⊢Id {ℓ} = record
  { unit   = record
    { η       =  λ _ _ → ⋆ -- the only function to a singleton set
    ; commute =  λ _ → ≡.refl
    }
  ; counit = record
    { η       =  id
    ; commute =  id
    }
  ; zig =  ⋆
  ; zag =  λ{ {⋆} {⋆} → ≡.refl }
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
