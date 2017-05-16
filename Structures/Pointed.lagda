%{{{ Imports
\begin{code}
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

%{{{ Pointed ; Hom ; PointedAlg ; PointedCat ; Forget

Pointed.  This ``creates'' Maybe.

\begin{code}
record Pointed {a} : Set (lsuc a) where
  constructor MkPointed
  field
    Carrier : Set a
    point   : Carrier

open Pointed

record Hom {ℓ} (X Y : Pointed {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor           :  Carrier X → Carrier Y
    preservation  :  mor (point X) ≡ point Y

open Hom

PointedAlg : ∀ {ℓ} → OneSortedAlg ℓ
PointedAlg = record
   { Alg         =   Pointed
   ; Carrier     =   Carrier
   ; Hom         =   Hom
   ; mor         =   mor
   ; comp        =   λ F G → MkHom (mor F ∘ mor G) (≡.cong (mor F) (preservation G) ⟨≡≡⟩ preservation F)
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl
   ; Id-is-id    =   ≐-refl
   }
  
PointedCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
PointedCat ℓ = oneSortedCategory ℓ PointedAlg

Forget : (ℓ : Level) → Functor (PointedCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ PointedAlg
\end{code}

%}}}

%{{{ Free ; MaybeLeft ; NoRight

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (PointedCat ℓ)
Free ℓ = record
  { F₀             =   λ A → MkPointed (Maybe A) nothing
  ; F₁             =   λ f → MkHom (maybe (just ∘ f) nothing) ≡.refl
  ; identity       =   maybe ≐-refl ≡.refl
  ; homomorphism   =   maybe ≐-refl ≡.refl
  ; F-resp-≡      =   λ F≡G → maybe (∘-resp-≐ (≐-refl {x = just}) (λ x → F≡G {x})) ≡.refl
  }

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

NoRight : ∀ o → (CoFree : Functor (Sets o) (PointedCat o)) → ¬ (Adjunction (Forget o) CoFree)
NoRight o (record { F₀ = f }) Adjunct = lower (η (counit Adjunct) (Lift ⊥) (point (f (Lift ⊥))))
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
