%{{{ Imports
\begin{code}
module Structures.Dependent where

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
\end{code}
%}}}

%{{{ Dependent ; Hom

A |Dependent| algebra consists of a carrier acting as an index for another family of
functions. An array is an example of this with the index set being the valid indices.
Alternatively, the named fields of a class-object are the indices for that class-object.

\begin{code}
record Dependent a b : Set (lsuc (a ⊍ b)) where
  constructor MkDep
  field
    Index : Set a
    Field : Index → Set b

open Dependent
\end{code}

Alternatively, these can be construed as some universe |Index| furnished with a
constructive predicated |Field| :-)

That is to say, these may also be known as ``unary relational algebras''.

\begin{code}
record Hom {a b} (Src Tgt : Dependent a b) : Set (a ⊍ b) where
  constructor MkHom
  field
    mor   : Index Src → Index Tgt
    shift : {i : Index Src} → Field Src i → Field Tgt (mor i)

open Hom
\end{code}

The |shift| condition may be read, in the predicate case, as:
if |i| is in the predicate in the source, then its images is in the predicate of
the target.

Such categories have been studies before under the guide ``the category of sets
with an elected subset''.

%}}}

%{{{ TwoCat ; Forget

\begin{code}
DependentCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
DependentCat ℓ = record
  { Obj        =     Dependent ℓ ℓ
  ; _⇒_       =     Hom
  ; _≡_       =     λ F G → mor F ≐ mor G
  ; id         =    MkHom id id
  ; _∘_        =    λ F G → MkHom (mor F ∘ mor G) (shift F ∘ shift G)
  ; assoc      =    ≐-refl
  ; identityˡ   =    ≐-refl
  ; identityʳ   =    ≐-refl
  ; equiv       =    record { IsEquivalence ≐-isEquivalence } 
  ; ∘-resp-≡   =   ∘-resp-≐
  }
  where open import Relation.Binary
\end{code}

We can forget about the first sort or the second to arrive at our starting
category and so we have two forgetful functors.

\begin{code}
Forget : (ℓ : Level) → Functor (DependentCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀             =   Dependent.Index
  ; F₁             =   Hom.mor
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ F≈G {x} → F≈G x
  }

Forget² : (ℓ : Level) → Functor (DependentCat ℓ) {! ??? !}
Forget² ℓ = record
  { F₀             =   λ i → Dependent.Field i
  ; F₁             =   ?
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   ?
  }
\end{code}
%}}}

Generalised Empty and Unit, to avoid a flurry of |lift|'s.
\begin{spec}
data ⊥ {ℓ : Level} : Set ℓ where
record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt
\end{spec}

%{{{ Free and CoFree

Given a type, we can pair it with the empty type or the singelton type
and so we have a free and a co-free constructions. 

\begin{spec}
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
\end{spec}
%}}}

%{{{ Left and Right adjunctions

Now for the actual proofs that the |Free| and |Cofree| functors
are deserving of their names.

\begin{spec}
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
\end{spec         }
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
