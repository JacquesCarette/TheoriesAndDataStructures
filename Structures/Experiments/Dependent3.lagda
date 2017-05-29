We consider “dependent algebras” which consist of an index set and
a family of sets on it. Alternatively, in can be construed as a universe
of discourse along with an elected subset of interest. In the latter view
the free and cofree constructions products the empty and universal predicates.
In the former view, the we have an adjunction involving dependent products.

%{{{ Imports
\begin{code}
module Structures.Experiments.Dependent3 where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (id ; _∘_ ; const)
open import Function2             using (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Categories.Morphisms using (reverseⁱ ; _ⓘ_; idⁱ) renaming (_≅_ to Iso)
iso-notation = Iso
syntax iso-notation cat X Y  =  X ≅ Y ∶ cat   -- note the ghost colon
module _ {ℓ} where
  open import Categories.Arrow (Sets ℓ) public
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
constructively predicated |Field| :-)

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
DependentCat : (ℓ : Level) → Category (lsuc ℓ) ℓ (lsuc ℓ)
DependentCat ℓ = record
  { Obj        =     Dependent ℓ ℓ
  ; _⇒_       =     Hom
  ; _≡_       =     λ {A} {B} F G → ({x : Index A} → mor F x ≡ mor G x)
                                    × (∀ {i : Index A} → arrobj (shift F {i}) ≅ arrobj (shift G {i}) ∶ arrow)
  ; id         =    MkHom id id
  ; _∘_        =    λ F G → MkHom (mor F ∘ mor G) (shift F ∘ shift G)
  ; assoc      =    λ {A} {B} {C} {D} {F} {G} {H} → ≡.refl , record
    { f = arrarr {f = id} {g = id} (λ {x} → ≡.cong (shift H) ≡.refl)
    ; g = arrarr {f = id} {g = id} (≡.cong (shift H) ≡.refl)
    ; iso = record { isoˡ =  ≡.refl , ≡.refl ; isoʳ = ≡.refl , ≡.refl }
    }
  ; identityˡ   =  λ {A} {B} {F} → ≡.refl , record
    { f = arrarr {f = id} {g = id} (≡.cong (shift F) ≡.refl)
    ; g = arrarr {f = id} {g = id} (≡.cong (shift F) ≡.refl)
    ; iso = record { isoˡ = ≡.refl , ≡.refl ; isoʳ = ≡.refl , ≡.refl }
    }
  ; identityʳ   =   λ {A} {B} {F} → ≡.refl , record
    { f = arrarr {f = id} {id} (≡.cong (shift F) ≡.refl)
    ; g = arrarr {f = id} {id} (≡.cong (shift F) ≡.refl)
    ; iso = record { isoˡ = ≡.refl , ≡.refl ; isoʳ = ≡.refl , ≡.refl }
    }
  ; equiv       =    λ {A} {B} → record { refl = λ {F} → ≡.refl , record
       { f = arrarr {f = id} {id} (≡.cong (shift F) ≡.refl)
       ; g = arrarr {f = id} {id} (≡.cong (shift F) ≡.refl)
       ; iso = record { isoˡ = ≡.refl , ≡.refl ; isoʳ = ≡.refl , ≡.refl } }
    ; sym = λ {F} {G} → λ{ (F≈₁G , F≈₂G) → ≡.sym F≈₁G , (λ {i} → reverseⁱ arrow F≈₂G) }
    ; trans = λ {F G H} → λ{ (F≈₁G , F≈₂G) (G≈₁H , G≈₂H) → ≡.trans F≈₁G G≈₁H , _ⓘ_ arrow G≈₂H F≈₂G}
    }
  ; ∘-resp-≡   = λ {A} {B} {C} {F} {H} {G} {K} →
                 λ{ (F≈₁H , F≈₂H) (G≈₁K , G≈₂K) →
                    (≡.cong (mor F) G≈₁K  ⟨≡≡⟩ F≈₁H) , λ {i} → _ⓘ_ arrow {!!} {!!}
    }
  -- ∘-resp-≐
  }
  where open import Relation.Binary ; open Arrow⇒ ; open Iso renaming (f to To ; g to From)
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
  ; F-resp-≡      =   λ F≈G {x} → {!!} -- F≈G x
  }
\end{code}

ToDo ∷ construct another forgetful functor

%}}}

%{{{ Free and CoFree

Given a type, we can pair it with the empty type or the singelton type
and so we have a free and a co-free constructions. 

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (DependentCat ℓ)
Free ℓ = record
  { F₀               =   λ A → MkDep A (λ _ → ⊥)
  ; F₁               =   λ f → MkHom f id
  ; identity         =   {!!} -- ≐-refl
  ; homomorphism     =   {!!} -- ≐-refl
  ; F-resp-≡        =   λ F≈G → {!!} -- F≈G {x}
  }

Cofree : (ℓ : Level) → Functor (Sets ℓ) (DependentCat ℓ)
Cofree ℓ = record
  { F₀             =   λ A → MkDep A (λ _ → ⊤)
  ; F₁             =   λ f → MkHom f id
  ; identity       =   {!!} -- ≐-refl
  ; homomorphism   =   {!!} -- ≐-refl
  ; F-resp-≡      =   λ f≈g → {!!} -- f≈g {x}
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
    ; commute = λ f → ≡.refl , (λ {i} → record
      { f = arrarr (λ { {()} })
      ; g = arrarr (λ { {()} })
      ; iso = {!!} })
    }
  ; zig = {!!} -- ≐-refl
  ; zag = ≡.refl
  }
  
Right :  (ℓ : Level) → Adjunction (Forget ℓ) (Cofree ℓ)
Right ℓ = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) 
    ; commute = λ _ → {!!} -- ≐-refl
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   {!!} -- ≐-refl
  }
\end{code}
%}}}

%{{{ Merge and Dup functors ; Right₂ adjunction

The category of sets contains products and so |Dependent| algebras can be represented there
and, moreover, this is adjoint to duplicating a type to obtain a |TwoSorted| algebra.

\begin{code}
DepProd : (ℓ : Level) → Functor (DependentCat ℓ) (Sets ℓ)
DepProd ℓ = record
  { F₀             =   λ S → Σ (Index S) (Field S)
  ; F₁             =   λ F → mor F ×₁ shift F
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      = {!!}
--    λ {A} {B} F≈G → λ{ {x = (i , f)} → cong₂D {_} {_} {Index A} {Index B} _,_ (≡.sym (proj₁ F≈G))
--               (≡.sym (proj₂ F≈G))}
  }

-- Every set gives rise to an identity family on itself
ID : (ℓ : Level) → Functor (Sets ℓ) (DependentCat ℓ)
ID ℓ = record
  { F₀             =   λ A → MkDep A (λ _ → A)
  ; F₁             =   λ f → MkHom f f
  ; identity       =   {!!} -- ≐-refl
  ; homomorphism   =   {!!} -- ≐-refl
  ; F-resp-≡      =   λ F≈G → {!!} -- λ x → F≈G {x}
  }
\end{code}

Then the proof that these two form the desired adjunction

\begin{code}
Right₂ : (ℓ : Level) → Adjunction (ID ℓ) (DepProd ℓ)
Right₂ ℓ = record
  { unit     =   record { η = λ _ → diag ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ _ → MkHom proj₁ (λ{ {i , f} _ → f}) ; commute = λ _ → {!!} }
  ; zig      =   {!!} -- ≐-refl
  ; zag      =   ≡.refl
  }
\end{code}
%}}}

Note that since Σ encompasses both × and ⊎, it may not be that there is another functor
co-adjoint to ID ---not sure though.

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
