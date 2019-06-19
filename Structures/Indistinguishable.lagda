MA: Messy, but have essentially demonstrated that no faithful left adjoint exists.
    I was unable to produce any left adjoints at all nor disprove their existence altogether.

\section{IndistinguishableAlgebras: much ado about the identity}

When you have a type in hand, there is not many terms you can form.
The formulae one can form would require quantifiers.
If we use existential quantifiers then we obtain variations on pointed theories;
whereas if we use universal quantifiers then we obtain variations on contractable theories.

We investigate the latter and hope some useful datatypes for software engineering pop-out!

%{{{ Imports
\begin{code}
{-# OPTIONS  --irrelevant-projections #-}

module Structures.Indistinguishable where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function

open import Helpers.Categorical
open import Helpers.Function2    using (_$ᵢ; _$ₑ_)
open import Helpers.DataProperties
open import Helpers.EqualityCombinators

open ≡
\end{code}
%}}}

%{{{ Carrier and Hom
\subsection{Definition}
\begin{code}
record Indistinguishable {ℓ} : Set (lsuc ℓ) where
  constructor MkInd
  field
    Carrier : Set ℓ
    blind   : ∀ {x y : Carrier} → x ≡ y

open Indistinguishable

Hom : {ℓ : Level} (X Y : Indistinguishable {ℓ}) → Set ℓ
Hom X Y = Carrier X → Carrier Y
\end{code}
%}}}

%{{{ Category and forgetful functor U
\subsection{Category and Forgetful Functor}

\begin{code}
Indistinguishables : (ℓ : Level) → Category _ ℓ ℓ
Indistinguishables ℓ = record
   { Obj         =   Indistinguishable
   ; _⇒_         =   Hom
   ; _≡_         =   λ f g → f ≐ g
   ; id          =   id
   ; _∘_         =   λ f g → f ∘ g
   ; assoc       =   ≐-refl
   ; identityˡ   =   ≐-refl
   ; identityʳ   =   ≐-refl
   ; equiv       =   record { IsEquivalence ≐-isEquivalence }
   ; ∘-resp-≡    =   ∘-resp-≐
   }
   where open import Relation.Binary using (IsEquivalence)

Forget : (o : Level) → Functor (Indistinguishables o) (Sets o)
Forget  _ = record
  { F₀            =   Carrier
  ; F₁            =   id
  ; identity      =   ≡.refl
  ; homomorphism  =   ≡.refl
  ; F-resp-≡     =   _$ᵢ
  }
\end{code}
%}}}

%{{{ Left and AdjLeft
\subsection{Free Adjunction: Part 1 of a toolkit}

MA: I've tried yielding 𝟙 and 𝟘 as the free algebra and have also tried “Ind” with
irrelevance, below.

\begin{code}
open import Structures.OneCat hiding (Forget)

𝟙 : {ℓ : Level} → Indistinguishable {ℓ}
𝟙 = MkInd One λ{ {⋆} {⋆} → refl}

open import Helpers.DataProperties using (⊥ ; ⊥-elim)

𝟘 : {ℓ : Level} → Indistinguishable {ℓ}
𝟘 = MkInd ⊥ λ{ { () } }

open import Data.Maybe

record Ind {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor MkInd
  field .try : Maybe A
  {- It may appear that “Ind A ≅ Maybe A”, however this is not strictly true
     since the irrelevance declaration implies that we *cannot* actually use
     the element of type Maybe A, only that it exists.

     Whence, this type says either there is no element in A, or if there are any
     we cannot actually use them directly.

     That is, “try” can never be utilised in computational contexts, where
     evaluation happens.
  -}

uip-Ind : {ℓ : Level} {A : Set ℓ} {x y : Ind A} → x ≡ y
uip-Ind {ℓ} {A} {MkInd try} {MkInd catch} = refl

Left : (ℓ : Level) → Functor (Sets ℓ) (Indistinguishables ℓ)
Left ℓ = record
  { F₀             =   λ A → MkInd (Ind A) uip-Ind
  ; F₁             =   λ f → λ{ (MkInd try) → MkInd (map f try) }
  ; identity       =   λ _ → uip-Ind
  ; homomorphism   =   λ _ → uip-Ind
  ; F-resp-≡       =   λ _ _ → refl
  }
\end{code}

\begin{spec}
AdjLeft : (ℓ : Level) → Adjunction (Left ℓ) (Forget ℓ)
AdjLeft ℓ = record
  { unit   = record { η = λ X did → MkInd (just did) ; commute = λ _ → refl }
  ; counit = record { η =  λ{ X (MkInd x) → {! NOOOOOOOOOOOOOOOOOOO, third time :'(!} }
                    ; commute = {!!} }
  ; zig = {!!} ; zag = {!!} }
-- record { unit = idT ; counit = idT ; zig = ≐-refl ; zag = ≡.refl }
\end{spec}

While there is a ``least'' contractable object for any given set, there is,
in-general, no ``largest'' contractable object corresponding to any given set.
That is, there is no co-free functor.

\begin{code}
open import Helpers.DataProperties

NoLeft : let ℓ = lzero in (Free : Functor (Sets ℓ) (Indistinguishables ℓ))
        → Adjunction Free (Forget ℓ) → ⊥ {ℓ}
NoLeft (record { F₀ = F₀ }) Adjunct = shaka-when-the-walls-fell
  where open Adjunction Adjunct
        open NaturalTransformation

        open import Data.Bool renaming (Bool to 𝔹)

        𝑩 : Indistinguishable
        𝑩 = F₀ 𝔹

        inj : 𝔹 → Carrier 𝑩
        inj = η unit 𝔹

        {- The components of the unit are monic
           precisely when the left adjoint is faithful -}

        postulate inj-is-injective : ∀ {x y} → inj x ≡ inj y → x ≡ y

        shaka-when-the-walls-fell : ⊥ {lzero}
        shaka-when-the-walls-fell
          with inj-is-injective (blind 𝑩 {inj true} {inj false})
        ...| ()
\end{code}
%}}}

%{{{ Initial object

A singleton set with its only point determines an initial object in this category.
That is, One is not only the free object on a set but is special that way.

\begin{spec}

initial : {ℓ : Level} → Initial (Contractables ℓ)
initial = record
  { ⊥         =   One𝒞
  ; !         =   λ{ {MkContractable X x p} → (𝑲 x) }
  ; !-unique  =   λ {A} _ _ → sym (collapse A)
  }
\end{spec}

%}}}
%}}}

%{{{ Right, diag, AdjRight
\subsection{CoFree Adjunction}

\begin{spec}
Right : (ℓ : Level) → Functor (Sets ℓ) (Carriers ℓ)
Right ℓ = Left ℓ

AdjRight : (ℓ : Level) → Adjunction (Forget ℓ) (Right ℓ)
AdjRight ℓ = record { unit = idT ; counit = idT ; zig = ≡.refl ; zag = ≐-refl }

\end{spec}

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
