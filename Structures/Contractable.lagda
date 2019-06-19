\DeclareUnicodeCharacter{7472}{\ensuremath{7472}}

\section{Contractable Algebras: Working with Pointed Types}

We consider the theory of \emph{pointed algebras} which consist of a type
along with an elected value of that type along with the only law that makes use
of the point and the carrier: $\forall x \;\bullet\; x = \texttt{thePoint}$.

At a first glance, this algebra seems useless. However, the aim of this work
is to explore simple elementary algebras and see where they arise in software
engineering. Lest the reader abandon us now, we cut to the chase: This algebra
arises when proxy datatypes are required; i.e., when a \emph{type parameter} is
utilised to convey information, but the actual value is completely irrelevant.

JC: Examples from Haskell?

%{{{ Imports
\begin{code}
module Structures.Contractable where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (id ; _∘_)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)

open import Helpers.Categorical
open import Helpers.Forget
open import Helpers.EqualityCombinators

open ≡
\end{code}
%}}}

%{{{ Contractable ; Hom

\subsection{Definition}

\begin{code}
record Contractable {a} : Set (lsuc a) where
  constructor MkContractable
  field
    Carrier   :  Set a
    Id        :  Carrier  {- The “Id”entified point -}
    collapse  :  ∀ {x} → x ≡ Id

open Contractable
\end{code}

One would expect a ``structure preserving operation'' on such structures to be a function
between the underlying carriers that takes the source's point to the target's point.
This is the case in the brute theory of pointed algebras, whereas contractable algebras
are so refined that the point-preservation property is provided for free.

\begin{code}
Hom : {ℓ : Level} (X Y : Contractable {ℓ}) → Set ℓ
Hom X Y = Carrier X → Carrier Y

preservation : {ℓ : Level} {X Y : Contractable {ℓ}}
             → {mor : Hom X Y} →  mor (Id X) ≡ Id Y
preservation {Y = Y} = collapse Y
\end{code}
%}}}

%{{{ PointedAlg ; PointedCat ; Forget
\subsection{Category and Forgetful Functors}

Since there is only one type, or sort, involved in the definition,
we may hazard these structures as ``one sorted algebras'':

\begin{code}
oneSortedAlg : ∀ {ℓ} → OneSortedAlg ℓ
oneSortedAlg = record
   { Alg         =   Contractable
   ; Carrier     =   Carrier
   ; Hom         =   Hom
   ; mor         =   id
   ; comp        =   λ f g → f ∘ g
   ; comp-is-∘   =   ≐-refl
   ; Id          =   id
   ; Id-is-id    =   ≐-refl
   }
\end{code}

From which we immediately obtain a category and a forgetful functor.

\begin{code}
Contractables : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Contractables ℓ = oneSortedCategory ℓ oneSortedAlg

Forget : (ℓ : Level) → Functor (Contractables ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ oneSortedAlg
\end{code}

%}}}

%{{{ Free ; MaybeLeft ; NoRight
\subsection{A Free Construction}

As discussed earlier, the prime example of pointed algebras are the optional types,
and this claim can be realised as a functor:
\begin{code}
open import Structures.OneCat hiding (initial ; Free ; Forget)

One𝒞 : {ℓ : Level} → Contractable {ℓ}
One𝒞 = MkContractable One ⋆ (sym uip-One)

Free : (ℓ : Level) → Functor (Sets ℓ) (Contractables ℓ)
Free ℓ = record
  { F₀            =  λ _ → One𝒞
  ; F₁            =  λ _ → id
  ; identity      =  λ _ → refl
  ; homomorphism  =  λ _ → refl
  ; F-resp-≡      =  λ _ _ → refl
  }
\end{code}

Which is indeed deserving of its name:

\begin{code}
Left : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
Left ℓ = record
  { unit        =   record { η = λ _  _ → ⋆ ; commute = λ _ → ≡.refl }
  ; counit      =   record
    { η         =    λ X _ → Id X
    ; commute   =    λ {X} {Y} _ _ → sym (collapse Y)
    }
  ; zig         =    λ _ → sym uip-One
  ; zag         =    λ {X} → collapse X
  }
\end{code}

Note that we could have used the isomorphic type Proxy, below, instead of One
but we do not want to increase the amount of new types needlessly.
\begin{code}
data Proxy {ℓ} (A : Set ℓ) : Set ℓ where
  MkProxy : Proxy A
\end{code}

While there is a ``least'' contractable object for any given set, there is,
in-general, no ``largest'' contractable object corresponding to any given set.
That is, there is no co-free functor.

\begin{code}
open import Helpers.DataProperties

NoRight : {ℓ : Level} → (CoFree : Functor (Sets ℓ) (Contractables ℓ)) → Adjunction (Forget ℓ) CoFree → ⊥
NoRight {ℓ} (record { F₀ = f }) Adjunct = η (counit Adjunct) ⊥ (Id (f ⊥))
  where open Adjunction
        open NaturalTransformation
\end{code}
%}}}

%{{{ Initial object

A singleton set with its only point determines an initial object in this category.
That is, One is not only the free object on a set but is special that way.

\begin{code}

initial : {ℓ : Level} → Initial (Contractables ℓ)
initial = record
  { ⊥         =   One𝒞
  ; !         =   λ{ {MkContractable X x p} → (𝑲 x) }
  ; !-unique  =   λ {A} _ _ → sym (collapse A)
  }
\end{code}

%}}}

%{{{ 0-ary adjoint
\begin{code}
module ZeroAryAdjoint where

  Forget-0 : (ℓ : Level) → Functor (Contractables ℓ) (OneCat ℓ ℓ ℓ)
  Forget-0 ℓ = MakeForgetfulFunctor Carrier

  -- OneCat can be, itself, viewed as a pointed set; i.e., an object of Contractables.
  Free-0 : (ℓ : Level) → Functor (OneCat ℓ ℓ ℓ) (Contractables ℓ)
  Free-0 ℓ = MakeFreeFunctor One𝒞

  Left′ : (ℓ : Level) → Adjunction (Free-0 ℓ) (Forget-0 ℓ)
  Left′ ℓ =  Make-Free⊢Forget {C = Contractables ℓ} Carrier initial
\end{code}
%}}}

So much for contractable structures.

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
