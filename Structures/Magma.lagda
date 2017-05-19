%{{{ Imports
\begin{code}
module Structures.Magma where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (const ; id ; _∘_ ; _$_)
open import Data.Empty

open import Function2 using (_$ᵢ)
open import Forget

open import EqualityCombinators
\end{code}
%}}}

%{{{ Magma ; Hom

A Free Magma is a binary tree.
\begin{code}

record Magma {a} : Set (lsuc a) where
  constructor MkMagma
  field
    Carrier : Set a
    Op      : Carrier → Carrier → Carrier

open Magma
bop = Magma.Op
syntax bop M x y = x ⟨ M ⟩ y

record Hom {ℓ} (X Y : Magma {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor          : Carrier X → Carrier Y
    preservation : {x y : Carrier X} → mor (x ⟨ X ⟩ y) ≡ mor x ⟨ Y ⟩ mor y

open Hom
\end{code}

%}}}

%{{{ MagmaAlg ; MagmaCat ; Forget

\begin{code}
MagmaAlg : ∀ {ℓ} → OneSortedAlg ℓ
MagmaAlg = record
  { Alg         =   Magma
  ; Carrier     =   Carrier
  ; Hom         =   Hom
  ; mor         =   mor
  ; comp        =   λ F G → record
    { mor            =   mor F ∘ mor G
    ; preservation   =   ≡.trans (≡.cong (mor F) (preservation G)) (preservation F)
    }
  ; comp-is-∘   =   ≐-refl
  ; Id          =   MkHom id ≡.refl
  ; Id-is-id    =   ≐-refl
  }
   
MagmaCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MagmaCat ℓ = oneSortedCategory ℓ MagmaAlg

Forget : (ℓ : Level) → Functor (MagmaCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ MagmaAlg
\end{code}

%}}}

%{{{ Tree ; ⟦_,_⟧ ; mapT ; indT

\begin{code}
data Tree {a : Level} (A : Set a) : Set a where
 Leaf   : A → Tree A
 Branch : Tree A → Tree A → Tree A

rec : {ℓ ℓ′ : Level} {A : Set ℓ} {X : Tree A → Set ℓ′}
    → (leaf : (a : A) → X (Leaf a))
    → (branch : (l r : Tree A) → X l → X r → X (Branch l r))
    → (t : Tree A) → X t
rec lf br (Leaf x)     = lf x
rec lf br (Branch l r) = br l r (rec lf br l) (rec lf br r)

⟦_,_⟧ : {a b : Level} {A : Set a} {B : Set b} (𝓁 : A → B) (𝒷 : B → B → B) → Tree A → B
⟦ 𝓁 , 𝒷 ⟧ = rec 𝓁 (λ _ _ x y → 𝒷 x y)

mapT : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Tree A → Tree B
mapT f = ⟦ Leaf ∘ f , Branch ⟧  -- cf UnaryAlgebra's map for |Eventually|

-- implicits variant of |rec|
indT : ∀ {a c} {A : Set a} {P : Tree A → Set c}
  → (base : {x : A} → P (Leaf x))
  → (ind : {l r : Tree A} → P l → P r → P (Branch l r))
  → (t : Tree A) → P t
indT base ind = rec (λ a → base) (λ l r → ind)
\end{code}

%}}}

%{{{ TreeF ; TreeLeft

\begin{code}
TreeF : (ℓ : Level) → Functor (Sets ℓ) (MagmaCat ℓ)
TreeF ℓ = record
  { F₀             =   λ A → MkMagma(Tree A) Branch
  ; F₁             =   λ f → MkHom (mapT f) ≡.refl
  ; identity       =   indT ≡.refl (≡.cong₂ Branch)
  ; homomorphism   =   indT ≡.refl (≡.cong₂ Branch)
  ; F-resp-≡      =   λ F≈G → indT (≡.cong Leaf F≈G) (≡.cong₂ Branch)
  }

TreeLeft : (ℓ : Level) → Adjunction (TreeF ℓ) (Forget ℓ)
TreeLeft ℓ = record
  { unit    =  record { η = λ _ → Leaf ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ A → MkHom ⟦ id , Op A ⟧ ≡.refl
    ; commute  =  λ {_} {Y} F → indT ≡.refl $ λ pf₁ pf₂ → ≡.cong₂ (Op Y) pf₁ pf₂ ⟨≡≡˘⟩ preservation F
    } 
  ; zig   =   indT ≡.refl (≡.cong₂ Branch)
  ; zag   =   ≡.refl
  }
\end{code}


-- Looks like there is no right adjoint, because its binary constructor would have to anticipate
-- all magma _*_, so that "singleton (x * y)" has to be the same as "Binary x y".

How does this relate to the notion of ``co-trees'' ---infinitely long trees?
─similar to the lists vs streams view.

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
