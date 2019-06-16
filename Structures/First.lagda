\section{First}

JC: Just made the Agda work, this needs massively cleaned up (names, etc).

"left zero magma". The free one basically has a single location, and just remembers the left part.
As usual, it is the co-unit which 'reveals' what needs to be done.

Note that Wikipedia talks about "left zero semigroup", which are, as algebraic structures,
different. It turns out that the Free version isn't, as associativity does not enter
into the picture; more precisely, it is proveable.
%{{{ Imports
\begin{code}
module Structures.First where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (const ; id ; _∘_ ; _$_)
open import Data.Empty

open import Helpers.Categorical
open import Helpers.Function2 using (_$ᵢ)
open import Helpers.Forget
open import Helpers.EqualityCombinators
\end{code}
%}}}

%{{{ First ; Hom
\subsection{Definition}
A Free Left-Biased Magma is a singleton.
\begin{code}

record LeftMagma ℓ : Set (lsuc ℓ) where
  constructor First
  field
    Carrier : Set ℓ
    _*_      : Carrier → Carrier → Carrier
    left    : ∀ x y → x ≡ x * y

open LeftMagma

record Hom {ℓ} (X Y : LeftMagma ℓ) : Set ℓ where
  constructor hom
  open LeftMagma X using () renaming (_*_ to _*₁_)
  open LeftMagma Y using () renaming (_*_ to _*₂_)
  field
    mor          : Carrier X → Carrier Y
    pres-* : {x y : Carrier X} → mor (x *₁ y) ≡ mor x *₂ mor y

open Hom
\end{code}

%}}}

All \AgdaRecord{LeftMagma} are in fact left zero semigroups. The missing part
is associativity:
\begin{code}
LeftMagmas-associative : {ℓ : Level} → (A : LeftMagma ℓ) →
  let _+_ = _*_ A in ∀ x y z → x + (y + z) ≡ (x + y) + z
LeftMagmas-associative A x y z = ≡.trans (≡.sym $ l x _) (≡.trans (l x y) (l (x + y) z))
  where l = left A
        _+_ = _*_ A
\end{code}

%{{{ MagmaAlg ; MagmaCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
MagmaAlg : {ℓ : Level} → OneSortedAlg ℓ
MagmaAlg {ℓ} = record
  { Alg         =   LeftMagma ℓ
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

Magmas : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Magmas ℓ = oneSortedCategory ℓ MagmaAlg

Forget : (ℓ : Level) → Functor (Magmas ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ MagmaAlg
\end{code}

%}}}

%{{{ Singleton
\subsection{Syntax}
\begin{code}
data Left {a : Level} (A : Set a) : Set a where
  Leaf : A → Left A

open Left

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Left A → Left B
map f (Leaf a) = Leaf (f a)

\end{code}

%}}}

%{{{ TreeF ; TreeLeft
\begin{code}

map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
         → f ≐ᵢ g
         → map f ≐ map g
map-cong f≡g (Leaf _) = ≡.cong Leaf f≡g

LeftF : (ℓ : Level) → Functor (Sets ℓ) (Magmas ℓ)
LeftF ℓ = record
  { F₀             =   λ A → First (Left A) (λ x _ → x) λ _ _ → ≡.refl
  ; F₁             =   λ f → hom (map f) ≡.refl
  ; identity       =   λ { (Leaf _) → ≡.refl }
  ; homomorphism   =   λ { (Leaf _) → ≡.refl }
  ; F-resp-≡      =   map-cong
  }

eval : {ℓ : Level} (M : LeftMagma ℓ) → Left (Carrier M) → Carrier M
eval M (Leaf x) = x

eval-naturality : {ℓ : Level} {M N : LeftMagma ℓ} (F : Hom M N)
                → eval N ∘ map (mor F) ≐ mor F ∘ eval M
eval-naturality {ℓ} {M} {N} F (Leaf x) = ≡.refl

LeftLeft : (ℓ : Level) → Adjunction (LeftF ℓ) (Forget ℓ)
LeftLeft ℓ = record
  { unit    =  record { η = λ _ → Leaf ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  λ A → hom (eval A) λ { {Leaf x} {Leaf y} → left A x y}
    ; commute  =  eval-naturality
    }
  ; zig   =   λ {(Leaf _) → ≡.refl}
  ; zag   =   ≡.refl
  }
\end{code}

%}}}

%{{{ Zero object

\begin{code}
open import Structures.OneCat hiding (initial ; terminal)

One-Magma : {ℓ : Level} → LeftMagma ℓ
One-Magma = First One (𝑲₂ ⋆) λ { ⋆ _ → ≡.refl}

terminal : {ℓ : Level} → Terminal (Magmas ℓ)
terminal = record
  { ⊤        =  One-Magma
  ; !         =  λ {X} → hom (𝑲 ⋆) ≡.refl
  ; !-unique  =  λ _ _ → uip-One
  }

{-
open import Data.Empty
initial : {ℓ : Level} → Initial (Magmas ℓ)
initial {ℓ} = ?
-}
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
