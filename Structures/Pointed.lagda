\DeclareUnicodeCharacter{7472}{\ensuremath{7472}}

\section{Pointed Algebras: Nullable Types}

We consider the theory of \emph{pointed algebras} which consist of a type
along with an elected value of that type.\footnote{Note that this definition
is phrased as a ``dependent product''!}
Software engineers encounter such
scenarios all the time in the case of an object-type and a default value of
a ``null'', or undefined, object. In the more explicit setting of pure functional
programming, this concept arises in the form of |Maybe|, or |Option| types.

\verb+Some programming languages, such as |C#| for example, provide a |default| keyword to access a default value of a given data type.+

edinsert{MA}{Haskell's typeclass analogue of |default|?}

edcomm{MA}{Perhaps discuss ``types as values'' and the subtle issue of how pointed algebras
are completely different than classes in an imperative setting. }

%{{{ Imports
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Structures.Pointed where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)

open import Forget

open import Data.Empty
open import Relation.Nullary

open import EqualityCombinators
\end{code}
%}}}

%{{{ Pointed ; Hom

\subsection{Definition}

As mentioned before, a |Pointed| algebra is a type, which we will refer to by |Carrier|,
along with a value, or |point|, of that type.

\begin{code}
record Pointed {a} : Set (lsuc a) where
  constructor MkPointed
  field
    Carrier   :   Set a
    point     :   Carrier

open Pointed
\end{code}

Unsurprisingly, a ``structure preserving operation'' on such structures is a function
between the underlying carriers that takes the source's point to the target's point.

\begin{code}
record Hom {ℓ} (X Y : Pointed {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor           :  Carrier X → Carrier Y
    preservation  :  mor (point X) ≡ point Y

open Hom
\end{code}
%}}}

%{{{ PointedAlg ; PointedCat ; Forget
\subsection{Category and Forgetful Functors}

Since there is only one type, or sort, involved in the definition,
we may hazard these structures as ``one sorted algebras'':

\begin{code}
oneSortedAlg : ∀ {ℓ} → OneSortedAlg ℓ
oneSortedAlg = record
   { Alg         =   Pointed
   ; Carrier     =   Carrier
   ; Hom         =   Hom
   ; mor         =   mor
   ; comp        =   λ F G → MkHom (mor F ∘ mor G) (≡.cong (mor F) (preservation G) ⟨≡≡⟩ preservation F)
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl
   ; Id-is-id    =   ≐-refl
   }
\end{code}

From which we immediately obtain a category and a forgetful functor.

\begin{code}
Pointeds : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Pointeds ℓ = oneSortedCategory ℓ oneSortedAlg

Forget : (ℓ : Level) → Functor (Pointeds ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ oneSortedAlg
\end{code}

The naming |Pointeds| is to be consistent with the category theory library we are using, which
names the category of sets and functions by |Sets|. That is, the category name is the objects'
name suffixed with an `s'.

Of-course, as hinted in the introduction, this structure ---as are many--- is defined in a
dependent fashion and so we have another forgetful functor:

\begin{code}
open import Data.Product
Forgetᴰ : (ℓ : Level) → Functor (Pointeds ℓ) (Sets ℓ)
Forgetᴰ ℓ = record { F₀ = λ P → Σ (Carrier P) (λ x → x ≡ point P)
    ; F₁ = λ {P} {Q} F → λ{ (val , val≡ptP) → mor F val , (≡.cong (mor F) val≡ptP ⟨≡≡⟩ preservation F) }
    ; identity = λ {P} → λ{ {val , val≡ptP} → ≡.cong (λ x → val , x) (≡.proof-irrelevance _ _) }
    ; homomorphism = λ {P} {Q} {R} {F} {G} → λ{ {val , val≡ptP} → ≡.cong (λ x → mor G (mor F val) , x) (≡.proof-irrelevance _ _) }
    ; F-resp-≡ = λ {P} {Q} {F} {G} F≈G → λ{ {val , val≡ptP} → {!≡.cong₂ _,_ (F≈G val) ?!} }
    }
\end{code}

That is, we ``only remember the point''.

edinsert{MA}{An adjoint to this functor?}

%}}}

%{{{ Free ; MaybeLeft ; NoRight
\subsection{A Free Construction}

As discussed earlier, the prime example of pointed algebras are the optional types,
and this claim can be realised as a functor:
\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (Pointeds ℓ)
Free ℓ = record
  { F₀             =   λ A → MkPointed (Maybe A) nothing
  ; F₁             =   λ f → MkHom (maybe (just ∘ f) nothing) ≡.refl
  ; identity       =   maybe ≐-refl ≡.refl
  ; homomorphism   =   maybe ≐-refl ≡.refl
  ; F-resp-≡      =   λ F≡G → maybe (∘-resp-≐ (≐-refl {x = just}) (λ x → F≡G {x})) ≡.refl
  }
\end{code}

Which is indeed deserving of its name:

\begin{code}
MaybeLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
MaybeLeft ℓ = record
  { unit        =   record { η = λ _ → just ; commute = λ _ → ≡.refl }
  ; counit      =   record
    { η         =    λ X → MkHom (maybe id (point X)) ≡.refl
    ; commute   =    maybe ≐-refl ∘ ≡.sym ∘ preservation
    }          
  ; zig         =    maybe ≐-refl ≡.refl
  ; zag         =    ≡.refl
  }
\end{code}

edcomm{MA}{Develop |Maybe| explicitly so we can ``see'' how the utility |maybe| ``pops up naturally''.}

While there is a ``least'' pointed object for any given set, there is, in-general, no ``largest'' pointed object
corresponding to any given set. That is, there is no co-free functor.

\begin{code}
NoRight : {ℓ : Level} → (CoFree : Functor (Sets ℓ) (Pointeds ℓ)) → ¬ (Adjunction (Forget ℓ) CoFree)
NoRight (record { F₀ = f }) Adjunct = lower (η (counit Adjunct) (Lift ⊥) (point (f (Lift ⊥))))
  where open Adjunction
        open NaturalTransformation
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
