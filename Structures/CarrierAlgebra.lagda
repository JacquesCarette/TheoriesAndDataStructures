\section{CarrierAlgebras: much ado about the identity}

Since the forgetful functor is the identity functor, left and right are
trivial.

%{{{ Imports
\begin{code}
module Structures.CarrierAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function

open import Categories.Category   using (Category; module Category)
open import Categories.Functor    using (Functor; Contravariant)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Categories.NaturalTransformation using () renaming (id to idT)

open import Helpers.Function2    using (_$ᵢ; _$ₑ_)
open import Helpers.DataProperties
open import Helpers.EqualityCombinators
\end{code}
%}}}

%{{{ Carrier and Hom
\subsection{Definition}
\begin{code}
record Carrier {ℓ} : Set (lsuc ℓ) where
  constructor car
  field
    carrier : Set ℓ

open Carrier

record Hom {ℓ} (X Y : Carrier {ℓ}) : Set ℓ where
  constructor car-hom
  field
    mor       :  carrier X → carrier Y

open Hom
\end{code}
%}}}

%{{{ Category and forgetful functor U
\subsection{Category and Forgetful Functor}

\begin{code}
Carriers : (ℓ : Level) → Category _ ℓ ℓ
Carriers ℓ = record
   { Obj         =   Carrier
   ; _⇒_         =   Hom
   ; _≡_         =   λ F G → mor F ≐ mor G
   ; id          =   record { mor = id }
   ; _∘_         =   λ F G → record { mor =   mor F ∘ mor G }
   ; assoc       =   ≐-refl
   ; identityˡ   =   ≐-refl
   ; identityʳ   =   ≐-refl
   ; equiv       =   record { IsEquivalence ≐-isEquivalence }
   ; ∘-resp-≡    =   ∘-resp-≐
   }
   where open Hom ; open import Relation.Binary using (IsEquivalence)

Forget : (o : Level) → Functor (Carriers o) (Sets o)
Forget  _ = record
  { F₀            =   carrier
  ; F₁            =   mor
  ; identity      =   ≡.refl
  ; homomorphism  =   ≡.refl
  ; F-resp-≡     =   _$ᵢ
  }
\end{code}
%}}}

%{{{ Left and AdjLeft
\subsection{Free Adjunction: Part 1 of a toolkit}


\begin{code}
Left : (ℓ : Level) → Functor (Sets ℓ) (Carriers ℓ)
Left ℓ = record
  { F₀             =   car
  ; F₁             =   car-hom
  ; identity       =   ≐-refl
  ; homomorphism   =   ≐-refl
  ; F-resp-≡       =   _$ₑ_
  }
\end{code}

\begin{code}
AdjLeft : (ℓ : Level) → Adjunction (Left ℓ) (Forget ℓ)
AdjLeft ℓ = record { unit = idT ; counit = idT ; zig = ≐-refl ; zag = ≡.refl }
\end{code}
%}}}

%{{{ Right, diag, AdjRight
\subsection{CoFree Adjunction}

\begin{code}
Right : (ℓ : Level) → Functor (Sets ℓ) (Carriers ℓ)
Right ℓ = Left ℓ

AdjRight : (ℓ : Level) → Adjunction (Forget ℓ) (Right ℓ)
AdjRight ℓ = record { unit = idT ; counit = idT ; zig = ≡.refl ; zag = ≐-refl }

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
