%{{{ Imports
\begin{code}
module Structures.TwoSorted where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_ ; const)
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

We are using pairs of object and pairs of morphisms which is known to form a category:

\begin{code}
TwoCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
TwoCat ℓ = record
  { Obj        =   TwoSorted ℓ
  ; _⇒_       =   Hom
  ; _≡_       =   λ F G → one F ≐ one G   ×  two F ≐ two G
  ; id         =   MkHom id id
  ; _∘_        =   λ F G → MkHom (one F ∘ one G) (two F ∘ two G)
  ; assoc      =   ≐-refl , ≐-refl
  ; identityˡ  =   ≐-refl , ≐-refl
  ; identityʳ  =   ≐-refl , ≐-refl
  ; equiv     =  record
    { refl    =  ≐-refl , ≐-refl
    ; sym     =  λ { (oneEq , twoEq)  → ≐-sym oneEq , ≐-sym twoEq }
    ; trans   =  λ { (oneEq₁ , twoEq₁) (oneEq₂ , twoEq₂) → ≐-trans oneEq₁ oneEq₂ , ≐-trans twoEq₁ twoEq₂}
    }
  ; ∘-resp-≡ = λ{ (g≈₁k , g≈₂k) (f≈₁h , f≈₂h) → ∘-resp-≐ g≈₁k f≈₁h , ∘-resp-≐ g≈₂k f≈₂h }
  }
\end{code}

We can forget about the first sort or the second to arrive at our starting
category and so we have two forgetful functors.

\begin{code}
Forget : (ℓ : Level) → Functor (TwoCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀             =   TwoSorted.One
  ; F₁             =   Hom.one
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₁G x }
  }


Forget² : (ℓ : Level) → Functor (TwoCat ℓ) (Sets ℓ)
Forget² ℓ = record
  { F₀             =   TwoSorted.Two
  ; F₁             =   Hom.two
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₂G x }
  }
\end{code}
%}}}

%{{{ Free and CoFree

Given a type, we can pair it with the empty type or the singelton type
and so we have a free and a co-free constructions. 

\begin{code}
-- Generalised Empty and Unit, to avoid a flurry of |lift|'s.
--
data ⊥ {ℓ : Level} : Set ℓ where
record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

Free : (ℓ : Level) → Functor (Sets ℓ) (TwoCat ℓ)
Free ℓ = record
  { F₀             =   λ A → MkTwo A ⊥
  ; F₁             =   λ f → MkHom f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }

Cofree : (ℓ : Level) → Functor (Sets ℓ) (TwoCat ℓ)
Cofree ℓ = record
  { F₀             =   λ A → MkTwo A ⊤
  ; F₁             =   λ f → MkHom f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }

-- Dually,  ( also shorter due to eta reduction )

Free² : (ℓ : Level) → Functor (Sets ℓ) (TwoCat ℓ)
Free² ℓ = record
  { F₀             =   MkTwo ⊥
  ; F₁             =   MkHom id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → ≐-refl , λ x → f≈g {x}
  }

Cofree² : (ℓ : Level) → Functor (Sets ℓ) (TwoCat ℓ)
Cofree² ℓ = record
  { F₀             =   MkTwo ⊤
  ; F₁             =   MkHom id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → ≐-refl , λ x → f≈g {x}
  }
\end{code}
%}}}

%{{{ Left and Right adjunctions
\begin{code}
Left : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
Left ℓ = record
  { unit   = record
    { η       = λ A a → a
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ _ → MkHom id (λ {()})
    ; commute = λ f → ≐-refl , (λ {()})
    }
  ; zig = ≐-refl , (λ { () })
  ; zag = ≡.refl
  }

Right :  (ℓ : Level) → Adjunction (Forget ℓ) (Cofree ℓ)
Right ℓ = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) 
    ; commute = λ _ → ≐-refl , ≐-refl
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl , λ {tt → ≡.refl }
  }

-- Dually,

Left² : (ℓ : Level) → Adjunction (Free² ℓ) (Forget² ℓ)
Left² ℓ = record
  { unit   = record
    { η       = λ A a → a
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ _ → MkHom (λ {()}) id
    ; commute = λ f →  (λ {()}) , ≐-refl
    }
  ; zig = (λ { () }) , ≐-refl
  ; zag = ≡.refl
  }

Right² :  (ℓ : Level) → Adjunction (Forget² ℓ) (Cofree² ℓ)
Right² ℓ = record
  { unit = record
    { η = λ _ → MkHom (λ _ → tt) id
    ; commute = λ _ → ≐-refl , ≐-refl
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   (λ {tt → ≡.refl }) , ≐-refl
  }
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
  ; F-resp-≡ = λ{ (F≈₁G , F≈₂G) {inj₁ x} → ≡.cong inj₁ (F≈₁G x) ; (F≈₁G , F≈₂G) {inj₂ x} → ≡.cong inj₂ (F≈₂G x)}
  }
  where open TwoSorted

from⊎ : ∀ {ℓ} {One : Set ℓ} → One ⊎ One → One
from⊎ = [ id , id ]′

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
