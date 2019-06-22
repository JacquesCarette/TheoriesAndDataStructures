\DeclareUnicodeCharacter{7472}{\ensuremath{7472}}

\section{Dynamical Systems: Seemingly Super Simple Automata}

We consider the theory of \emph{dynamical systems} which consist of a type
along with an elected value of that type and a way to obtain new elements.

Think of a box with a screen displaying the current state and a button that alters the state.

Sounds like a computer ;-)

%{{{ Imports
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Structures.DynamicalSystem where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (id ; _∘_)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)

open import Helpers.Categorical
open import Helpers.Forget
open import Helpers.EqualityCombinators
open ≡
\end{code}
%}}}

%{{{ Definition and Hom

\subsection{Definition}

\begin{code}
record DynamicalSystem {a} : Set (lsuc a) where
  constructor MkDS
  field
    States : Set a
    Start  : States
    Next   : States → States

open DynamicalSystem
\end{code}

Unsurprisingly, a ``structure preserving operation'' on such structures is a function
between the underlying carriers that takes the source's point to the target's point.

\begin{code}
record Hom {ℓ} (X Y : DynamicalSystem {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor           :  States X → States Y
    preservation  :  mor (Start X) ≡ Start Y
    respect       :  mor ∘ Next X ≐ᵢ Next Y ∘ mor

open Hom
\end{code}
%}}}

%{{{ category
\subsection{Category and Forgetful Functors}

Since there is only one type, or sort, involved in the definition,
we may hazard these structures as ``one sorted algebras'':

\begin{code}
Id : {ℓ : Level} {A : DynamicalSystem {ℓ}} → Hom A A
Id = MkHom id refl refl

oneSortedAlg : ∀ {ℓ} → OneSortedAlg ℓ
oneSortedAlg = record
   { Alg         =   DynamicalSystem
   ; Carrier     =   States
   ; Hom         =   Hom
   ; mor         =   mor
   ; comp        =   λ F G → MkHom (mor F ∘ mor G)
                             (cong (mor F) (preservation G) ⟨≡≡⟩ preservation F)
                             (cong (mor F) (respect G) ⟨≡≡⟩ respect F)
   ; comp-is-∘   =   ≐-refl
   ; Id          =   Id
   ; Id-is-id    =   ≐-refl
   }
\end{code}

From which we immediately obtain a category and a forgetful functor.

\begin{code}
DS : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
DS ℓ = oneSortedCategory ℓ oneSortedAlg

Forget : (ℓ : Level) → Functor (DS ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ oneSortedAlg
\end{code}

%}}}

%{{{ Free ; MaybeLeft ; NoRight
\subsection{A Free Construction}

As discussed earlier, the prime example of pointed algebras are the optional types,
and this claim can be realised as a functor:
\begin{code}

{-   DynamicalSystem ≈ Pushout of Pointed and Unary
  ⇒  Free DynamicalSystem ≈ Pushout of Free Pointed and Free Unary
  ⇒  Possibly ≈ Pushout of Maybe and Eventually (•̀ᴗ•́)و
-}
data Possibly {ℓ : Level} (A : Set ℓ) : Set ℓ where
  never  : Possibly A
  indeed : A → Possibly A
  later  : Possibly A → Possibly A

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Possibly A → Possibly B
map f never      = never
map f (indeed x) = indeed (f x)
map f (later x)  = later (map f x)

map-id : {ℓ : Level} {A : Set ℓ} → map id ≐ id {A = Possibly A}
map-id never      = refl
map-id (indeed x) = refl
map-id (later x)  = cong later (map-id x)

map-∘ : {ℓ : Level} {A B C : Set ℓ} {f : B → C} {g : A → B} → map (f ∘ g) ≐ map f ∘ map g
map-∘ never      = refl
map-∘ (indeed x) = refl
map-∘ (later x)  = cong later (map-∘ x)

map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B} → f ≐ᵢ g → map f ≐ map g
map-cong f≈g never      = refl
map-cong f≈g (indeed x) = cong indeed f≈g
map-cong f≈g (later x)  = cong later (map-cong f≈g x)

{- eliminator / induction -}
possibly : {a b : Level} {A : Set a} {B : Possibly A → Set b}
         → B never
         → (∀ ix → B (indeed ix))
         → (∀ {lx} → B lx → B (later lx))
         →
           (pa : Possibly A)  →  B pa
possibly bn bi bl never      = bn
possibly bn bi bl (indeed x) = bi x
possibly {B = B} bn bi bl (later x)  = bl (possibly {B = B} bn bi bl x)

Free : (ℓ : Level) → Functor (Sets ℓ) (DS ℓ)
Free ℓ = record
  { F₀             =   λ A → MkDS (Possibly A) never later
  ; F₁             =   λ f → MkHom (map f) refl refl
  ; identity       =   map-id
  ; homomorphism   =   map-∘
  ; F-resp-≡      =   map-cong
  }
\end{code}

Which is indeed deserving of its name:

\begin{code}
AdjLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
AdjLeft ℓ = record
  { unit        =   record { η = λ X x → indeed x ; commute = λ _ → refl }
  ; counit      =   record
    { η         =    λ X → MkHom (possibly (Start X) id (Next X)) refl refl
    ; commute   =    λ {X} {Y} f → sym ∘ possibly (preservation f) (λ _ → refl) λ ind → respect f ⟨≡≡⟩ cong (Next Y) ind
    }
  ; zig         =    possibly refl (λ _ → refl) (cong later)
  ; zag         =    refl
  }
\end{code}

While there is a ``least'' dynamical system for any given set, there is, in-general, no ``largest'' dynamical system
corresponding to any given set. That is, there is no co-free functor. Indeed, what is the starting state assigned to the empty state space?

\begin{code}
open import Helpers.DataProperties

NoRight : {ℓ : Level} → (CoFree : Functor (Sets ℓ) (DS ℓ)) → Adjunction (Forget ℓ) CoFree → ⊥
NoRight {ℓ} (record { F₀ = f }) Adjunct = η (counit Adjunct) ⊥ (Start (f ⊥))
  where open Adjunction
        open NaturalTransformation
\end{code}
%}}}

%{{{ Initial object

Suppose there were an inital object 𝑰, then we can find maps “! : 𝑰 → X”
with ! (Start 𝑰)  = Start X
and  ! (Next 𝑰 e) = Next X (! e)

Together these two homomorphism constraints seem to define a function “!”
which quickly leads to consider 𝑰 = ℕ.
Indeed, the intial object is just the free object on the singleton set (─‿‿─)

\begin{code}
open import Data.Nat

open import Helpers.DataProperties

initial : Initial (DS lzero)
initial = record
  { ⊥         =   MkDS ℕ zero suc
  ; !         =   λ{ {MkDS X start next} → MkHom (foldn start next) refl refl}
  ; !-unique  =   λ {A} f → sym ∘ foldn (preservation f) λ ind → respect f ⟨≡≡⟩ cong (Next A) ind
  }
\end{code}

%}}}

Super neat stuffs ^_^

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
