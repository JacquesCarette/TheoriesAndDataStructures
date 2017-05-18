We consider two sorted algebras endowed with a binary heterogeneous relation.

%{{{ Imports
\begin{code}
module Structures.Rel where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function using (id ; _∘_ ; const)
open import Function2 using (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties
open import Structures.TwoSorted using (TwoSorted; TwoCat ; MkTwo) renaming (Hom to TwoHom ; MkHom to MkTwoHom)
\end{code}
%}}}

%{{{ HetroRel ; Hom

\begin{code}
record HetroRel ℓ ℓ′ : Set (lsuc (ℓ ⊍ ℓ′)) where
  constructor MkHRel
  field
    One : Set ℓ
    Two : Set ℓ
    Rel : One → Two → Set ℓ′

open HetroRel
relOp = HetroRel.Rel
syntax relOp A x y = x ⟨ A ⟩ y
\end{code}

\begin{code}
record Hom {ℓ ℓ′} (Src Tgt : HetroRel ℓ ℓ′) : Set (ℓ ⊍ ℓ′) where
  constructor MkHom
  field
    one   : One Src → One Tgt
    two   : Two Src → Two Tgt
    shift : {x : One Src} {y : Two Src} → x ⟨ Src ⟩ y → one x  ⟨ Tgt ⟩  two y

open Hom
\end{code}

%}}}

%{{{ HRelCat ; Forget

\begin{code}
HRelCat : (ℓ ℓ′ : Level) → Category (lsuc (ℓ ⊍ ℓ′)) (ℓ ⊍ ℓ′) ℓ
HRelCat ℓ ℓ′ = record
  { Obj        =   HetroRel ℓ ℓ′
  ; _⇒_       =   Hom
  ; _≡_       =   λ F G → one F ≐ one G   ×  two F ≐ two G
  ; id         =   MkHom id id id
  ; _∘_        =   λ F G → MkHom (one F ∘ one G) (two F ∘ two G) (shift F ∘ shift G)
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
category and so we have two forgetful functors. Moreover, we can simply
forget about the relation to arrive at the two-sorted category :-)

\begin{code}
Forget : (ℓ ℓ′ : Level) → Functor (HRelCat ℓ ℓ′) (Sets ℓ)
Forget ℓ ℓ′ = record
  { F₀             =   HetroRel.One
  ; F₁             =   Hom.one
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₁G x }
  }

Forget² : (ℓ ℓ′ : Level) → Functor (HRelCat ℓ ℓ′) (Sets ℓ)
Forget² ℓ ℓ′ = record
  { F₀             =   HetroRel.Two
  ; F₁             =   Hom.two
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₂G x }
  }

-- Whence, HRelCat is a subcategory of TwoCat
Forget³ : (ℓ ℓ′ : Level) → Functor (HRelCat ℓ ℓ′) (TwoCat ℓ)
Forget³ ℓ ℓ′ = record
  { F₀             =   λ S → MkTwo (One S) (Two S)
  ; F₁             =   λ F → MkTwoHom (one F) (two F)
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  }
\end{code}
%}}}

%{{{ Free and CoFree

Given a type, we can pair it with the empty type or the singelton type
and so we have a free and a co-free constructions. 

\begin{code}
Free : (ℓ ℓ′ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ′)
Free ℓ ℓ′ = record
  { F₀             =   λ A → MkHRel A A (λ _ _ → ⊥)
  ; F₁             =   λ f → MkHom f f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , (λ x → f≈g {x})
  }

Cofree : (ℓ ℓ′ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ′)
Cofree ℓ ℓ′ = record
  { F₀             =   λ A → MkHRel A A (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom f f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , (λ x → f≈g {x})
  }

-- Dually,

Free² : (ℓ ℓ′ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ′)
Free² ℓ ℓ′ = record
  { F₀             =   λ A → MkHRel A ⊥ (λ{ _ ()})
  ; F₁             =   λ f → MkHom f id (λ{ {y = ()} })
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl  
  }

Cofree² : (ℓ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ)
Cofree² ℓ = record
  { F₀             =   λ A → MkHRel A ⊤ (λ _ _ → A)
  ; F₁             =   λ f → MkHom f id f 
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }
\end{code}

Note that we may form yet another free/cofree pair via
|F₀ = λ A → MkHRel ⊥ A …| and |F₀ = λ A → MkHRel ⊤ A …|.

\begin{code}
Cofree²′ : (ℓ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ)
Cofree²′ ℓ = record
  { F₀             =   λ A → MkHRel A ⊤ (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom f id id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }

Free³ : (ℓ : Level) → Functor (TwoCat ℓ) (HRelCat ℓ ℓ)
Free³ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → ⊥)
  ; F₁             =   λ F → MkHom (one F) (two F) id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom


Cofree³ : (ℓ : Level) → Functor (TwoCat ℓ) (HRelCat ℓ ℓ)
Cofree³ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → ⊤)
  ; F₁             =   λ F → MkHom (one F) (two F) id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom

Cofree³′ : (ℓ : Level) → Functor (TwoCat ℓ) (HRelCat ℓ ℓ)
Cofree³′ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → One S × Two S)
  ; F₁             =   λ F → MkHom (one F) (two F) (one F ×₁ two F)
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom
\end{code}

%}}}

%{{{ Left and Right adjunctions

Now for the actual proofs that the |Free| and |Cofree| functors
are deserving of their names.

\begin{code}
-- | (MkRel X ⊥ ⊥ ⟶ Alg) ≅ (X ⟶ One Alg)|
Left : (ℓ ℓ′ : Level) → Adjunction (Free² ℓ ℓ′) (Forget ℓ ℓ′)
Left ℓ ℓ′ = record
  { unit   = record
    { η       = λ _ → id
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ A → MkHom (λ z → z) (λ{()}) (λ {x} {})
    ; commute = λ f → ≐-refl , (λ ())
    }
  ; zig = ≐-refl , (λ ())
  ; zag = ≡.refl
  }

-- | (One Alg ⟶ X) ≅ (Alg ⟶ MkRel X ⊤ (λ _ _ → X)|
Right :  (ℓ : Level) → Adjunction (Forget ℓ ℓ) (Cofree² ℓ)
Right ℓ  = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) (λ {x} {y} _ → x)
    ; commute = λ _ → ≐-refl , (λ x → ≡.refl)
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl , λ{ tt → ≡.refl}
  }

-- Another cofree functor:
--
-- | (One Alg ⟶ X) ≅ (Alg ⟶ MkRel X ⊤ (λ _ _ → ⊤)|
Right′ :  (ℓ : Level) → Adjunction (Forget ℓ ℓ) (Cofree²′ ℓ)
Right′ ℓ  = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) (λ {x} {y} _ → tt)
    ; commute = λ _ → ≐-refl , (λ x → ≡.refl)
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl , λ{ tt → ≡.refl}
  }
\end{code}

But wait, adjoints are necessarily unique, up to isomorphism, whence
|Cofree² ≅ Cofree²′|.
Intuitively, the relation part is a ``subset'' of the given carriers
and when one of the carriers is a singleton then the largest relation
is the universal relation which can be seen as either the first non-singleton carrier
or the ``always-true'' relation which happens to be formalized by ignoring its arguments
and going to a singleton set.

\begin{code}
-- Dually,

Free²² : (ℓ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ)
Free²² ℓ = record
  { F₀             =   λ A → MkHRel ⊥ A (λ ())
  ; F₁             =   λ f → MkHom id f (λ {})
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → ≐-refl , (λ x → F≈G {x})
  }

-- | (MkRel ⊥ X ⊥ ⟶ Alg) ≅ (X ⟶ Two Alg)|
Left² : (ℓ : Level) → Adjunction (Free²² ℓ) (Forget² ℓ ℓ)
Left² ℓ = record
  { unit   = record
    { η       = λ _ → id
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ _ → MkHom (λ ()) id (λ {})
    ; commute = λ f →  (λ ()) , ≐-refl
    }
  ; zig = (λ ()) , ≐-refl
  ; zag = ≡.refl
  }

CoFree²² : (ℓ : Level) → Functor (Sets ℓ) (HRelCat ℓ ℓ)
CoFree²² ℓ = record
  { F₀             =   λ A → MkHRel ⊤ A (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom id f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → ≐-refl , (λ x → F≈G {x})
  }

-- |(Two Alg ⟶ X) ≅ (Alg ⟶ ⊤ X ⊤|
Right² : (ℓ : Level) → Adjunction (Forget² ℓ ℓ) (CoFree²² ℓ)
Right² ℓ = record
  { unit   = record
    { η       = λ _ → MkHom (λ _ → tt) id (λ _ → tt)
    ; commute = λ f → ≐-refl , ≐-refl
    }
  ; counit = record
    { η       = λ _ → id
    ; commute = λ _ →  ≡.refl
    }
  ; zig = ≡.refl
  ; zag = (λ{ tt → ≡.refl}) , ≐-refl
  }


\end{code}

Left² : (ℓ ℓ′ : Level) → Adjunction (Free² ℓ ℓ′) (Forget² ℓ ℓ′)
Left² ℓ ℓ′ = record
  { unit   = record
    { η       = λ _ → {!!}
    ; commute = {!!}
    }
  ; counit = record
    { η       = λ _ → MkHom {!!} {!!} {!!}
    ; commute = λ f →  {!!} , {!!}
    }
  ; zig = {!!} , {!!}
  ; zag = {!!}
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
\end{spec}
%}}}

%{{{ Merge and Dup functors ; Right₂ adjunction

The category of sets contains products and so |TwoSorted| algebras can be represented there
and, moreover, this is adjoint to duplicating a type to obtain a |TwoSorted| algebra.

\begin{spec}
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
\end{spec}

Then the proof that these two form the desired adjunction

\begin{spec}
Right₂ : (ℓ : Level) → Adjunction (Dup ℓ) (Merge ℓ)
Right₂ ℓ = record
  { unit     =   record { η = λ _ → diag ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ _ → MkHom proj₁ proj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; zig      =   ≐-refl , ≐-refl
  ; zag      =   ≡.refl
  }
\end{spec}
%}}}

%{{{ Choice ; from⊎ ; Left₂ adjunction

The category of sets admits sums and so an alternative is to represet a |TwoSorted|
algebra as a sum, and moreover this is adjoint to the aforementioned duplication functor.

\begin{spec}
Choice : (ℓ : Level) → Functor (TwoCat ℓ) (Sets ℓ)
Choice ℓ =   record
  { F₀             =   λ S → One S ⊎  Two S
  ; F₁             =   λ F → one F ⊎₁ two F
  ; identity       =   ⊎-id $ᵢ
  ; homomorphism   =   λ{ {x = x} → ⊎-∘ x }
  ; F-resp-≡      =   λ F≈G {x} → uncurry ⊎-cong F≈G x
  }
  
Left₂ : (ℓ : Level) → Adjunction (Choice ℓ) (Dup ℓ)
Left₂ ℓ = record
  { unit     =   record { η = λ _ → MkHom inj₁ inj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; counit   =   record { η = λ _ → from⊎ ; commute = λ _ {x} → (≡.sym ∘ from⊎-nat) x }
  ; zig      =   λ{ {_} {x} → from⊎-preInverse x }
  ; zag      =   ≐-refl , ≐-refl
  }
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
