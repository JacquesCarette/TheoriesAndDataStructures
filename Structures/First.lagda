\section{First ---“Left-zero Magmas”}

The free one basically has a single location, and just remembers the left part.
As usual, it is the co-unit which \emph{reveals} what needs to be done.

Note that Wikipedia talks about "left zero semigroup", which are, as algebraic structures,
different. It turns out that the Free version isn't, as associativity does not enter
into the picture; more precisely, it is proveable.
%{{{ Imports
\begin{code}
module Structures.First where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (const ; id ; _∘_ ; _$_)

open import Helpers.Categorical
open import Helpers.Function2 using (_$ᵢ)
open import Helpers.Forget
open import Helpers.EqualityCombinators

open ≡
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
    _*_     : Carrier → Carrier → Carrier
    left    : ∀ {x y} → x * y ≡ x
\end{code}

In the presence of left-units, left-zero magmas collapse to the unit.
\begin{code}
  collopase : {Id : Carrier} → (∀ {y} → y ≡ Id * y) → ∀ {y} → y ≡ Id
  collopase {Id} unit {y} = let open ≡.≡-Reasoning in begin
       y
    ≡⟨ unit ⟩
       Id * y
    ≡⟨ left ⟩
       Id
    ∎
\end{code}

All \AgdaRecord{LeftMagma} are in fact left zero semigroups. The missing part
is associativity:
\begin{code}
  associative : ∀ {x y z} → x * (y * z) ≡ (x * y) * z
  associative = left ⟨≡≡˘⟩ left ⟨≡≡⟩ left
\end{code}

More generally, folding along such an operation is tantamount to obtaining the head of
a list.
\begin{code}
  open import Data.Vec
  open import Data.Nat hiding (_*_)

  fold-is-head : ∀ {n} {xs : Vec Carrier (suc n)} → foldr₁ _*_ xs  ≡  head xs
  fold-is-head {xs = y ∷ []} = refl
  fold-is-head {xs = x ∷ y ∷ ys} = let open ≡-Reasoning in begin
      foldr₁ _*_ (x ∷ y ∷ ys)
    ≡⟨ refl ⟩
      x * foldr₁ _*_ (y ∷ ys)
    ≡⟨ left ⟩
      x
    ≡⟨ refl ⟩
      head (x ∷ y ∷ ys)
    ∎
\end{code}

% Hom ≈ Func (•̀ᴗ•́)و
%
\begin{code}
open LeftMagma

Hom : {ℓ : Level} (X Y : LeftMagma ℓ) → Set ℓ
Hom X Y = Carrier X → Carrier Y
\end{code}

One would intutitively think that our definition of homomorphism is erroenous.
since no structure presevation is considered. This is acceptable since we obtain
structure preservation \emph{for free}!

\begin{code}
module _ {ℓ} {X Y : LeftMagma ℓ} {mor : Hom X Y} where

  private
    _*₁_ = LeftMagma._*_ X
    _*₂_ = LeftMagma._*_ Y

  hom-preservation : ∀ {a b} → mor (a *₁ b) ≡ mor a *₂ mor b
  hom-preservation {a} {b} = let open ≡-Reasoning in begin
      mor (a *₁ b)
    ≡⟨ cong mor (LeftMagma.left X)  ⟩
      mor a
    ≡˘⟨ LeftMagma.left Y ⟩
      mor a *₂ mor b
    ∎
\end{code}

%}}}

%{{{ MagmaAlg ; MagmaCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
MagmaAlg : {ℓ : Level} → OneSortedAlg ℓ
MagmaAlg {ℓ} = record
  { Alg         =   LeftMagma ℓ
  ; Carrier     =   Carrier
  ; Hom         =   Hom
  ; mor         =   id
  ; comp        =   λ F G → F ∘ G
  ; comp-is-∘   =   ≐-refl
  ; Id          =   id
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

Terms over left-zero magmas are either variables ---via \texttt{Embed} below---
or the operation applied to existing terms. Since the left-zero law ensures
that any such expression is tantamount to the first element ---c.f., \texttt{fold-is-head}
above--- we know all such expressions are characterised by the left-most element
and so there is no need to even account for the operation ---which can just be taken
to be the ubiquitous \texttt{const} combinator.
Whence:

\begin{spec}
{-
data Term {ℓ : Level} (A : Set ℓ) : Set ℓ where
  Embed : A → Term A
-}
\end{spec}

An entire new data-type that is isomorphic to its parameter is redundant
that burdens us with needless bookkeeping via its isomorphism-witnessing constructor.
As such, we take a simpler route:
\begin{code}
Term : {ℓ : Level} → Set ℓ → Set ℓ
Term = id
\end{code}

%}}}

%{{{ TreeF ; TreeTerm
\begin{code}
make-left-magma : {ℓ : Level} → Set ℓ → LeftMagma ℓ
make-left-magma A = First (Term A) const refl

LeftF : (ℓ : Level) → Functor (Sets ℓ) (Magmas ℓ)
LeftF ℓ = record
  { F₀           =   make-left-magma
  ; F₁           =   id
  ; identity     =   λ _ → refl
  ; homomorphism =   λ _ → refl
  ; F-resp-≡     =   λ eq _ → eq
  }
\end{code}

Evlauation is thus now tantamount to the identity function, which is clearly
natural.
\begin{code}
eval : {ℓ : Level} (M : LeftMagma ℓ) → Term (Carrier M) → Carrier M
eval M = id

eval-naturality : {ℓ : Level} {M N : LeftMagma ℓ} (F : Hom M N)
                → eval N ∘ F ≐ F ∘ eval M
eval-naturality {ℓ} {M} {N} F _ = ≡.refl
\end{code}

Putting things together yields the expected adjunction.
\begin{code}
LeftLeft : (ℓ : Level) → Adjunction (LeftF ℓ) (Forget ℓ)
LeftLeft ℓ = record
  { unit    =  record { η = λ X → id ; commute = λ _ → ≡.refl }
  ; counit  =  record
    { η        =  eval
    ; commute  =  λ _ _ → refl
    }
  ; zig   =   λ _ → refl
  ; zag   =   refl
  }
\end{code}
%}}}

%{{{ Terminal and Initial Objects

Since a left-zero magma is just a type with an operation,
that type could be empty or not and so we have an initial object
in the former case and a terminal object in the latter case.

\begin{code}
open import Structures.OneCat hiding (initial ; terminal)

terminal : {ℓ : Level} → Terminal (Magmas ℓ)
terminal = record
  { ⊤        =  make-left-magma One
  ; !        =  λ {X} → 𝑲 ⋆
  ; !-unique =  λ _ _ → uip-One
  }

open import Helpers.DataProperties using (⊥ ; ⊥-elim)

initial : {ℓ : Level} → Initial (Magmas ℓ)
initial {ℓ} = record
  { ⊥        = make-left-magma ⊥
  ; !        = ⊥-elim
  ; !-unique = λ{ _ () }
  }
\end{code}
%}}}

JC: All in all left-zero magmas corresponds to Data.Semigroup.First
(but not the same-named data type from Data.Monoid).

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
