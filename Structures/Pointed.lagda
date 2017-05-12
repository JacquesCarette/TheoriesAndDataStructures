\begin{code}
module Structures.Pointed where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Agda using (Sets)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)

open import Function2 using (_$ᵢ)
open import Equiv hiding (_●_)
open import Forget

open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≣_; refl to ≣-refl; sym to ≣-sym; cong to ≣-cong;
            trans to ≣-trans; cong₂ to ≣-cong₂)

-------------------------------------
-- Pointed.  This ``creates'' Maybe.

record Pointed {a} : Set (lsuc a) where
  constructor _●_
  field
    A : Set a
    pt : A

open Pointed renaming (A to Carrier)

record Hom {ℓ} (X Y : Pointed {ℓ}) : Set ℓ where
  constructor MkHom
  field
    h        :  Carrier X → Carrier Y
    pres-pt  :  h (pt X) ≣ pt Y

open Hom renaming (h to mor)

private
  Alg : ∀ {ℓ} → OneSortedAlg ℓ
  Alg = record
    { Alg       =   Pointed
    ; Carrier       =   Carrier
    ; Hom       =   Hom
    ; mor      =   mor
    ; comp      =   λ F G → MkHom (mor F ◎ mor G) (≣-trans (≣-cong (mor F) (pres-pt G)) (pres-pt F))
    ; comp-is-∘    =   ≐-refl
    ; Id       =   MkHom idF ≣-refl
    ; Id-is-id =   ≐-refl
    }
  
PointedCat : ∀ o → Category _ o o
PointedCat o = oneSortedCategory o Alg

Forget : ∀ o → Functor (PointedCat o) (Sets o)
Forget o = mkForgetful o Alg

Free : ∀ o → Functor (Sets o) (PointedCat o)
Free o = record
  { F₀           = λ A → Maybe A ● nothing
  ; F₁           = λ f → MkHom (maybe′ (just ◎ f) nothing) ≣-refl
  ; identity     = maybe ≐-refl ≣-refl
  ; homomorphism = maybe ≐-refl ≣-refl
  ; F-resp-≡     = λ F≡G → maybe (∘-resp-≐ (≐-refl {f = just}) (λ x → F≡G {x})) ≣-refl
  }

MaybeLeft : ∀ o → Adjunction (Free o) (Forget o)
MaybeLeft o = record
  { unit   = record { η = λ _ → just ; commute = λ _ → ≣-refl }
  ; counit = record
    { η        =  λ X → MkHom (maybe idF (pt X)) ≣-refl
    ; commute  =  maybe ≐-refl ◎ ≣-sym ◎ pres-pt
    }
  ; zig  =  maybe ≐-refl ≣-refl
  ; zag  =  ≣-refl
  }

open import Data.Empty
open import Relation.Nullary

NoRight : ∀ o → (CoFree : Functor (Sets o) (PointedCat o)) → ¬ (Adjunction (Forget o) CoFree)
NoRight o (record { F₀ = f }) Adjunct = lower (η (counit Adjunct) (Lift ⊥) (Pointed.pt (f (Lift ⊥))))
  where open Adjunction
        open NaturalTransformation

\end{code}

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
