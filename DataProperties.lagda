
This module is for those domain-ubiquitous properties that, disappointingly,
I could not locate these in the standard library.

Moreover, this module also re-exports (some of) the contents of |Data.Product| and |Data.Sum|.

%{{{ Imports
\begin{code}
module DataProperties where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (id ; _∘_ ; const)
open import EqualityCombinators

open import Data.Product public using (_×_; proj₁; proj₂; Σ; _,_; swap ; uncurry) renaming (map to _×₁_ ; <_,_> to ⟨_,_⟩)
open import Data.Sum     public using (_⊎_; inj₁; inj₂; [_,_])  renaming (map to _⊎₁_)
\end{code}
%}}}

\begin{code}
-- The diagonal natural transformation
diag : {ℓ : Level} {A : Set ℓ} (a : A) → A × A
diag a = a , a
\end{code}

%{{{ the ⊎ operation on functions is a functorial congruence

\begin{code}
⊎-id : {a b : Level} {A : Set a} {B : Set b} → id ⊎₁ id ≐ id {A = A ⊎ B}
⊎-id = [ ≐-refl , ≐-refl ]

⊎-∘ : {a b c a' b' c' : Level}
        {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} {C' : Set c} {C : Set c'}
        {f  : A → A'} {g : B → B'} {f' : A' → C} {g' : B' → C'}
      → (f' ∘ f) ⊎₁ (g' ∘ g) ≐ (f' ⊎₁ g') ∘ (f ⊎₁ g) --- aka “the exchange rule for sums”
⊎-∘ = [ ≐-refl , ≐-refl ]

⊎-cong : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {f f' : A → C} {g g' : B → D}
       → f ≐ f' → g ≐ g' → f ⊎₁ g ≐ f' ⊎₁ g'
⊎-cong f≈f' g≈g' = [ ∘-≐-cong₂ inj₁ f≈f' , ∘-≐-cong₂ inj₂ g≈g' ]
\end{code}

%}}}

%{{{ ∘-[,] : fusion property for casing

\begin{code}
∘-[,] : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        {f : A → C} {g : B → C} {h : C → D}
     → h ∘ [ f , g ] ≐ [ h ∘ f , h ∘ g ]
∘-[,] = [ ≐-refl , ≐-refl ]
\end{code}

%}}}

%{{{ from⊎ : the dual to |diag|

|diag| is a natural transformation |𝑰 ⟶̇ _²|, where's
|from⊎| is it's dual, |2×_ ⟶̇ 𝑰|.

\begin{code}
from⊎ : ∀ {ℓ} {A : Set ℓ} → A ⊎ A → A
from⊎ = [ id , id ]

-- |from⊎| is a natural transformation
--
from⊎-nat : {a b : Level} {A : Set a} {B : Set b}
        {f : A → B} → f ∘ from⊎  ≐ from⊎ ∘ (f ⊎₁ f)
from⊎-nat = [ ≐-refl , ≐-refl ]

-- |from⊎| is injective and so is pre-invertible,
--
from⊎-preInverse : {a b : Level} {A : Set a} {B : Set b} → id ≐ from⊎ {A = A ⊎ B} ∘ (inj₁ ⊎₁ inj₂)
from⊎-preInverse = [ ≐-refl , ≐-refl ]
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
