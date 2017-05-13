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

Now for the actual proofs that the |Free| and |Cofree| functors
are deserving of their names.

\begin{code}
Left : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
Left ℓ = record
  { unit   = record
    { η       = λ _ → id
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
    { η       = λ _ → id
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

The category of sets contains products and so |TwoSorted| algebras can be represented there
and, moreover, this is adjoint to duplicating a type to obtain a |TwoSorted| algebra.

\begin{code}
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; swap ; uncurry ; curry) renaming (map to _×₁_ ; <_,_> to ⟨_,_⟩)

-- This' also defined in |Involutive|; perhaps extract elsewhere to avoid duplicity.
diag : {ℓ : Level} {A : Set ℓ} (a : A) → A × A
diag a = a , a

-- The category of Sets has products and so the |TwoSorted| type can be reified there.
Merge : (ℓ : Level) → Functor (TwoCat ℓ) (Sets ℓ)
Merge ℓ = record
  { F₀             =   λ S → One S ×  Two S
  ; F₁             =   λ F → one F ×₁ two F
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ { (F≈₁G , F≈₂G) {x , y} → ≡.cong₂ _,_ (F≈₁G x) (F≈₂G y) }
  }

-- Every set gives rise to its square as a |TwoSorted| type.
Dup : (ℓ : Level) → Functor (Sets ℓ) (TwoCat ℓ)
Dup ℓ = record
  { F₀             =   λ A → MkTwo A A
  ; F₁             =   λ f → MkHom f f
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → diag (λ _ → F≈G)
  }
\end{code}

Then the proof that these two form the desired adjunction

\begin{code}
Right₂ : (ℓ : Level) → Adjunction (Dup ℓ) (Merge ℓ)
Right₂ ℓ = record
  { unit     =   record { η = λ _ → diag ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ _ → MkHom proj₁ proj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; zig      =   ≐-refl , ≐-refl
  ; zag      =   ≡.refl
  }
\end{code}
%}}}

%{{{ Choice ; from⊎ ; Left₂ adjunction

The category of sets admits sums and so an alternative is to represet a |TwoSorted|
algebra as a sum, and moreover this is adjoint to the aforementioned duplication functor.

\begin{code}
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])  renaming (map to _⊎₁_)

-- Disappoingly, I could not locate these in the standard library.

⊎-id : {a b : Level} {A : Set a} {B : Set b} → id ⊎₁ id ≐ id {A = A ⊎ B}
⊎-id (inj₁ _) = ≡.refl
⊎-id (inj₂ _) = ≡.refl

⊎-∘ : {a b c a' b' c' : Level}
        {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} {C' : Set c} {C : Set c'}
        {f  : A → A'} {g : B → B'} {f' : A' → C} {g' : B' → C'}
      → (f' ∘ f) ⊎₁ (g' ∘ g) ≐ (f' ⊎₁ g') ∘ (f ⊎₁ g) --- aka “the exchange rule for sums”
⊎-∘ (inj₁ _) = ≡.refl
⊎-∘ (inj₂ _) = ≡.refl

⊎-cong : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {f f' : A → C} {g g' : B → D}
       → f ≐ f' → g ≐ g' → f ⊎₁ g ≐ f' ⊎₁ g'
⊎-cong f≈f' g≈g' (inj₁ x) = ≡.cong inj₁ (f≈f' x)
⊎-cong f≈f' g≈g' (inj₂ y) = ≡.cong inj₂ (g≈g' y)

Choice : (ℓ : Level) → Functor (TwoCat ℓ) (Sets ℓ)
Choice ℓ =   record
  { F₀             =   λ S → One S ⊎  Two S
  ; F₁             =   λ F → one F ⊎₁ two F
  ; identity       =   λ{S} → ⊎-id $ᵢ
  ; homomorphism   =   λ{ {x = x} → ⊎-∘ x }
  ; F-resp-≡      =   λ F≈G {x} → uncurry ⊎-cong F≈G x
  }

-- also defined in |InvolutiveAlgebra|; need to avoid such duplicity!
from⊎ : ∀ {ℓ} {A : Set ℓ} → A ⊎ A → A
from⊎ = [ id , id ]′

∘-[,] : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        {f : A → C} {g : B → C} {h : C → D}
     → h ∘ [ f , g ] ≐ [ h ∘ f , h ∘ g ]
∘-[,] (inj₁ _) = ≡.refl
∘-[,] (inj₂ _) = ≡.refl

-- |from⊎| is a natural transformation
from⊎-nat : {a b : Level} {A : Set a} {B : Set b}
        {f : A → B} → f ∘ from⊎  ≐ from⊎ ∘ (f ⊎₁ f)
from⊎-nat (inj₁ _) = ≡.refl
from⊎-nat (inj₂ _) = ≡.refl

-- |from⊎| is injective and so is pre-invertible,
from⊎-preInverse : {a b : Level} {A : Set a} {B : Set b} → id ≐ from⊎ {A = A ⊎ B} ∘ (inj₁ ⊎₁ inj₂)
from⊎-preInverse (inj₁ _) = ≡.refl
from⊎-preInverse (inj₂ _) = ≡.refl

Left₂ : (ℓ : Level) → Adjunction (Choice ℓ) (Dup ℓ)
Left₂ ℓ = record
  { unit     =   record { η = λ _ → MkHom inj₁ inj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; counit   =   record { η = λ _ → from⊎ ; commute = λ _ {x} → (≡.sym ∘ from⊎-nat) x }
  ; zig      =   λ{ {_} {x} → from⊎-preInverse x }
  ; zag      =   ≐-refl , ≐-refl
  }
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
