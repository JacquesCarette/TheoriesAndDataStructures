\section{Magmas: Binary Trees}

Needless to say Binary Trees are a ubiquitous concept in programming.
We look at the associate theory and see that they are easy to use
since they are a free structure and their associate tool kit of
combinators are a result of the proof that they are indeed free.
\unfinished

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
\subsection{Definition}
A Free Magma is a binary tree.
\begin{code}

record Magma ℓ : Set (lsuc ℓ) where
  constructor MkMagma
  field
    Carrier : Set ℓ
    Op      : Carrier → Carrier → Carrier

open Magma
bop = Magma.Op
syntax bop M x y = x ⟨ M ⟩ y

record Hom {ℓ} (X Y : Magma ℓ) : Set ℓ where
  constructor MkHom
  field
    mor          : Carrier X → Carrier Y
    preservation : {x y : Carrier X} → mor (x ⟨ X ⟩ y) ≡ mor x ⟨ Y ⟩ mor y

open Hom
\end{code}

%}}}

%{{{ MagmaAlg ; MagmaCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
MagmaAlg : {ℓ : Level} → OneSortedAlg ℓ
MagmaAlg {ℓ} = record
  { Alg         =   Magma ℓ
  ; Carrier     =   Carrier
  ; Hom         =   Hom
  ; mor         =   mor
  ; comp        =   λ F G → record
    { mor            =   mor F ∘ mor G
    ; preservation   =   ≡.cong (mor F) (preservation G) ⟨≡≡⟩ preservation F
    }
  ; comp-is-∘   =   ≐-refl
  ; Id          =   MkHom id ≡.refl
  ; Id-is-id    =   ≐-refl
  }
   
Magmas : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Magmas ℓ = oneSortedCategory ℓ MagmaAlg

Forget : (ℓ : Level) → Functor (Magmas ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ MagmaAlg
\end{code}

%}}}

%{{{ Tree ; ⟦_,_⟧ ; mapT ; indT
\subsection{Syntax}
\edcomm{MA}{Mention free functor and free monads? Syntax.}
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

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Tree A → Tree B
map f = ⟦ Leaf ∘ f , Branch ⟧  -- cf UnaryAlgebra's map for |Eventually|

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
id-as-⟦⟧ : {ℓ : Level} {A : Set ℓ} → ⟦ Leaf , Branch ⟧  ≐ id {A = Tree A}
id-as-⟦⟧ = indT ≡.refl (≡.cong₂ Branch)

map-∘ : {ℓ : Level} {X Y Z : Set ℓ} {f : X → Y} {g : Y → Z} → map (g ∘ f) ≐ map g ∘ map f
map-∘ = indT ≡.refl (≡.cong₂ Branch)

map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
         → f ≐ᵢ g
         → map f ≐ map g
map-cong = λ F≈G → indT (≡.cong Leaf F≈G) (≡.cong₂ Branch)

TreeF : (ℓ : Level) → Functor (Sets ℓ) (Magmas ℓ)
TreeF ℓ = record
  { F₀             =   λ A → MkMagma(Tree A) Branch
  ; F₁             =   λ f → MkHom (map f) ≡.refl
  ; identity       =   id-as-⟦⟧
  ; homomorphism   =   map-∘
  ; F-resp-≡      =   map-cong
  }

eval : {ℓ : Level} (M : Magma ℓ) → Tree (Carrier M) → Carrier M
eval M = ⟦ id , Op M ⟧

eval-naturality : {ℓ : Level} {M N : Magma ℓ} (F : Hom M N)
                → eval N ∘ map (mor F) ≐ mor F ∘ eval M
eval-naturality {ℓ} {M} {N} F = indT ≡.refl $ λ pf₁ pf₂ → ≡.cong₂ (Op N) pf₁ pf₂ ⟨≡≡˘⟩ preservation F

-- `eval Trees' has a pre-inverse.
as-id : {ℓ : Level} {A : Set ℓ} → id {A = Tree A} ≐ ⟦ id , Branch ⟧ ∘ map Leaf
as-id = indT ≡.refl (≡.cong₂ Branch)

TreeLeft : (ℓ : Level) → Adjunction (TreeF ℓ) (Forget ℓ)
TreeLeft ℓ = record
  { unit    =  record { η = λ _ → Leaf ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ A → MkHom (eval A) ≡.refl
    ; commute  =  eval-naturality
    } 
  ; zig   =   as-id
  ; zag   =   ≡.refl
  }
\end{code}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item |id-as-⟦⟧|: \unfinished
\item |map|: usually functions can be packaged-up to work on trees.
\item |map-id|: the identity function leaves syntax alone; or: |map id| can be replaced with a constant
  time algorithm, namely, |id|.
\item |map-∘|: sequential substitutions on syntax can be efficiently replaced with a single substitution.
\item |map-cong|: observably indistinguishable substitutions can be used in place of one another, similar to the
      transparency principle of Haskell programs.      
\item |eval| : \unfinished
\item |eval-naturality| : \unfinished
\item |as-id| : \unfinished
\end{itemize}


Looks like there is no right adjoint, because its binary constructor would have to anticipate
all magma |_*_|, so that |singleton (x * y)| has to be the same as |Binary x y|.

How does this relate to the notion of ``co-trees'' ---infinitely long trees?
--similar to the lists vs streams view.
%}}}

%{{{ Zero object

Singleton sets form the terminal magma; while the empty type
forms the initial magma.

\begin{code}
open import Structures.OneCat hiding (initial ; terminal)
open import Categories.Object.Initial
open import Categories.Object.Terminal

One-Magma : {ℓ : Level} → Magma ℓ
One-Magma = MkMagma One (𝑲₂ ⋆)

terminal : {ℓ : Level} → Terminal (Magmas ℓ)
terminal = record
  { ⊤        =  One-Magma
  ; !         =  λ {X} → MkHom (𝑲 ⋆) ≡.refl
  ; !-unique  =  λ _ _ → uip-One
  }

open import Data.Empty
initial : {ℓ : Level} → Initial (Magmas ℓ)
initial = record
  { ⊥        =  MkMagma (Lift ⊥) λ{ (lift ()) }
  ; !         =  MkHom (λ{ (lift ()) }) λ{ {lift ()} }
  ; !-unique  =  λ{ _ ( lift() ) }
  }
\end{code}
%}}}

%{{{ 0-Ary version
\begin{code}
module ZeroAryAdjoint where

  Forget-0 : (ℓ : Level) → Functor (Magmas ℓ) (OneCat ℓ ℓ ℓ)
  Forget-0 ℓ = MakeForgetfulFunctor Carrier

  -- OneCat can be, itself, viewed as a Monoid
  Free-0 : (ℓ : Level) → Functor (OneCat ℓ ℓ ℓ) (Magmas ℓ)
  Free-0 ℓ = MakeFreeFunctor One-Magma

  -- MA: Compare with the case of Set in OneCat.lagda.
  -- c.f. NoLeftAdjoint and YesLeftAdjoint.
  Left : {ℓ : Level} → Adjunction (MakeFreeFunctor _) (Forget-0 ℓ)
  Left = Make-Free⊢Forget Carrier initial

  Right : {ℓ : Level} → Adjunction (Forget-0 ℓ) (Free-0 ℓ)
  Right = Make-Forget⊢CoFree Carrier terminal
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
