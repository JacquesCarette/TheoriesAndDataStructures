%{{{ Imports
\begin{code}
module Structures.TwoSorted where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (const) renaming (id to idF; _∘_ to _◎_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; [_,_]) renaming (map to map⊎)

open import Function2 using (_$ᵢ)

open import Forget
open import EqualityCombinators
\end{code}
%}}}

%{{{ TwoSorted ; Hom

A Free TwoSorted container is a ???. Let's formalise it and find out.

A |TwoSorted| type is just a pair of sets in the same universe
---in the future, we may consider those in different levels.

\begin{code}
record TwoSorted ℓ : Set (lsuc ℓ) where
  constructor MkTwo
  field
    One : Set ℓ
    Two : Set ℓ

open TwoSorted
\end{code}

Unastionishngly, a morphism between such types is a pair of functions
between the \emph{multiple} underlying carriers.
\begin{code}
record Hom {ℓ} (Src Tgt : TwoSorted ℓ) : Set ℓ where
  constructor MkHom
  field
    one : One Src → One Tgt
    two : Two Src → Two Tgt

open Hom
\end{code}

%}}}

%{{{ TwoCat ; Forget
\begin{code}
TwoCat : ∀ o → Category (lsuc o) o o
TwoCat o = record
  { Obj = TwoSorted o
  ; _⇒_ = Hom
  ; _≡_ = λ { {A} {B} (MkHom g₁ g₂) (MkHom one h₂) → (g₁ ≐ one) × (g₂ ≐ h₂)}
  ; id = MkHom idF idF
  ; _∘_ = λ { (MkHom one two) (MkHom g₁ g₂) → MkHom(one ◎ g₁) (two ◎ g₂)}
  ; assoc = ≐-refl , ≐-refl
  ; identityˡ = ≐-refl , ≐-refl
  ; identityʳ = ≐-refl , ≐-refl
  ; equiv = record { refl = ≐-refl , ≐-refl
                   ; sym = λ { (i≡j₁ , i≡j₂)  → ≐-sym i≡j₁ , ≐-sym i≡j₂ }
                   ; trans = λ { (i≡j₁ , i≡j₂) (j≡k₁ , j≡k₂) → (≐-trans i≡j₁ j≡k₁) , (≐-trans i≡j₂ j≡k₂)} }
  ; ∘-resp-≡ = λ g≡i f≡h → ∘-resp-≐ (proj₁ g≡i) (proj₁ f≡h) , ∘-resp-≐ (proj₂ g≡i) (proj₂ f≡h)
  }

Forget : ∀ o → Functor (TwoCat o) (Sets o)
Forget o = record
  { F₀ = TwoSorted.One
  ; F₁ = Hom.one
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≡ = λ x {y} → proj₁ x y
  }
\end{code}
%}}}

%{{{ Free and CoFree

\begin{code}
open import Data.Empty
open import Data.Unit

Free : ∀ o → Functor (Sets o) (TwoCat o)
Free o = record
  { F₀ = λ One → MkTwo One (Lift ⊥)
  ; F₁ = λ f → MkHom f idF
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → ( λ x → F≡G {x}) , ≐-refl
  }

Cofree : ∀ o → Functor (Sets o) (TwoCat o)
Cofree o = record
  { F₀ = λ One → MkTwo One (Lift ⊤)
  ; F₁ = λ f → MkHom f idF
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → ( λ x → F≡G {x}) , ≐-refl
  }
\end{code}
%}}}

%{{{ Left and Right adjunctions
\begin{code}
Left : ∀ o → Adjunction (Free o) (Forget o)
Left o = record
  { unit   = record { η = λ X x → x ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ { (MkTwo One B) → MkHom idF (λ { (lift ()) }) }
                    ; commute = λ f → ≐-refl , (λ { (lift ())}) }
  ; zig = ≐-refl , (λ { (lift ()) })
  ; zag = ≡.refl }

Right :  ∀ o → Adjunction (Forget o) (Cofree o)
Right o = record
  { unit = record { η = λ { (MkTwo One B) → MkHom idF (λ _ → lift tt) }
                  ; commute = λ f → ≐-refl , ≐-refl }
  ; counit = record { η = λ _ → idF ; commute = λ _ → ≡.refl }
  ; zig = ≡.refl
  ; zag = ≐-refl , (λ {(lift tt) → ≡.refl }) }
\end{code}
%}}}

%{{{ Merge and Dup functors ; Right₂ adjunction
\begin{code}
Merge : ∀ o → Functor (TwoCat o) (Sets o)
Merge o = record
  { F₀ = λ S → One S × Two S
  ; F₁ = λ {(MkHom one two) (a₁ , b₁) → (one a₁) , (two b₁)}
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≡ = λ {(F≡G₁ , F≡G₂) {x} → ≡.cong₂ _,_ (F≡G₁ (proj₁ x)) (F≡G₂ (proj₂ x))}
  }
  where open TwoSorted

Dup : ∀ o → Functor (Sets o) (TwoCat o)
Dup o = record
  { F₀ = λ One → MkTwo One One
  ; F₁ = λ f → MkHom f f
  ; identity = ≐-refl , ≐-refl
  ; homomorphism = ≐-refl , ≐-refl
  ; F-resp-≡ = λ F≡G → (λ x → F≡G {x}) , λ _ → F≡G
  }

Right₂ : ∀ o → Adjunction (Dup o) (Merge o)
Right₂ o = record
  { unit = record { η = λ X x → x , x ; commute = λ f → ≡.refl }
  ; counit = record { η = λ {(MkTwo One B) → MkHom proj₁ proj₂} ; commute = λ {(MkHom f g) → ≐-refl , ≐-refl} }
  ; zig = ≐-refl , ≐-refl
  ; zag = ≡.refl }
\end{code}
%}}}

%{{{ Choice ; from⊎ ; Left₂ adjunction
\begin{code}
Choice : ∀ o → Functor (TwoCat o) (Sets o)
Choice o = record
  { F₀ = λ S → One S ⊎ Two S
  ; F₁ = λ { (MkHom f g) → map⊎ f g}
  ; identity = λ {_} → λ { {(inj₁ x)} → ≡.refl ; {(inj₂ x)} → ≡.refl}
  ; homomorphism = λ { {x = (inj₁ x)} → ≡.refl ; {x = (inj₂ x)} → ≡.refl}
  ; F-resp-≡ = {!!} -- λ { ( F≡G₁ , F≡G₂ ) → λ { {(inj₁ x)} → ≡.cong inj₁ (F≡G₁ x) ; {(inj₂ x)} → ≡.cong inj₂ (F≡G₂ x)}}
  }
  where open TwoSorted

from⊎ : ∀ {ℓ} {One : Set ℓ} → One ⊎ One → One
from⊎ = [ idF , idF ]′

Left₂ : ∀ o → Adjunction (Choice o) (Dup o)
Left₂ o = record
  { unit   = record { η = λ {(MkTwo One B) → MkHom inj₁ inj₂} ; commute = λ f → ≐-refl , ≐-refl }
           ; counit = record { η = λ _ → from⊎ ; commute = λ f → λ { { (inj₁ x) } → ≡.refl ; {(inj₂ x)} → ≡.refl}}
  ; zig = λ {_} → λ { {(inj₁ x)} → ≡.refl ; {(inj₂ x)} → ≡.refl}
  ; zag = ≐-refl , ≐-refl }
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
