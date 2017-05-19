
%{{{ Imports
\begin{code}
module Structures.Monoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List using (List; _∷_ ; []; _++_; foldr; map)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (id ; _∘_ ; const)
open import Function2             using (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties
\end{code}
%}}}

%{{{ Monoid ; Hom

\begin{code}
record Monoid ℓ : Set (lsuc ℓ) where
  field 
    Carrier   :   Set ℓ
    Id        :   Carrier
    _*_       :   Carrier → Carrier → Carrier
    leftId    :   {x : Carrier} → Id * x ≡ x
    rightId   :   {x : Carrier} → x * Id ≡ x
    assoc     :   {x y z : Carrier} → (x * y) * z ≡ x * (y * z)

open Monoid

record Hom {ℓ} (Src Tgt : Monoid ℓ) : Set ℓ where
  constructor MkHom
  open Monoid Src renaming (_*_ to _*₁_)
  open Monoid Tgt renaming (_*_ to _*₂_) 
  field
    mor     :  Carrier Src → Carrier Tgt
    pres-Id : mor (Id Src) ≡ Id Tgt 
    pres-Op : {x y : Carrier Src} → mor (x *₁ y)  ≡  mor x *₂ mor y

open Hom
\end{code}

%}}}

%{{{ MonoidAlg ; MonoidCat
\begin{code}
MonoidAlg : {ℓ : Level} → OneSortedAlg ℓ
MonoidAlg {ℓ} = record
   { Alg         =   Monoid ℓ
   ; Carrier     =   Carrier
   ; Hom         =   Hom {ℓ}
   ; mor         =   mor
   ; comp        =   λ F G → record
     { mor       =   mor F ∘ mor G
     ; pres-Id   =   ≡.cong (mor F) (pres-Id G) ⟨≡≡⟩ pres-Id F
     ; pres-Op   =   ≡.cong (mor F) (pres-Op G) ⟨≡≡⟩ pres-Op F
     }
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl ≡.refl
   ; Id-is-id    =   ≐-refl
   }

MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat ℓ = oneSortedCategory ℓ MonoidAlg
\end{code}
%}}}

%{{{ forgetful functorS
\begin{code}
-- Forget all structure, and maintain only the underlying carrier
Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ MonoidAlg

-- ToDo ∷ forget to the underlying semigroup

-- ToDo ∷ forget to the underlying pointed

-- ToDo ∷ forget to the underlying magma

-- ToDo ∷ forget to the underlying binary relation, with x ∼ y ∶≡ (∀ z → x * z ≡ y * z)
          -- the monoid-indistuighability equivalence relation
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
