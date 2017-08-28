\section{Distinguished Subset Algebras}

%{{{ Imports
\begin{code}
module Structures.DistinguishedSubset where

open import Level renaming (suc to lsuc; zero to lzero)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (id ; _∘_ ; const)
open import Function2             using (_$ᵢ)
open import Data.Bool             using (Bool; true; false)
open import Relation.Nullary      using (¬_)

open import Forget
open import EqualityCombinators
open import DataProperties

\end{code}
%}}}

%{{{ Disting ; Hom

\begin{code}
record Disting a : Set (lsuc a) where
  constructor MkDist
  field
    Index : Set a
    Field : Index → Bool

open Disting
\end{code}

Alternatively, these can be construed as some universe |Index| furnished with a
constructive predicated |Field| :-)

That is to say, these may also be known as ``unary relational algebras''.

\begin{code}
record Hom {a} (Src Tgt : Disting a) : Set a where
  constructor MkHom
  field
    mor   : Index Src → Index Tgt
    shift : {i : Index Src} → Field Src i ≡ Field Tgt (mor i)

open Hom
\end{code}

The |shift| condition may be read, in the predicate case, as:
if |i| is in the predicate in the source, then its images is in the predicate of
the target.

Such categories have been studied before under the guide ``the category of sets
with a distinguished subset''.

%}}}

%{{{ TwoCat ; Forget

\begin{code}
DependentCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
DependentCat ℓ = record
  { Obj        =     Disting ℓ
  ; _⇒_       =     Hom
  ; _≡_       =     λ F G → (mor F ≐ mor G)
  ; id         =    MkHom id ≡.refl
  ; _∘_        =    λ F G → MkHom (mor F ∘ mor G) (shift G ⟨≡≡⟩ shift F)
  ; assoc      =    λ _ → ≡.refl
  ; identityˡ   =    λ _ → ≡.refl
  ; identityʳ   =    λ _ → ≡.refl
  ; equiv       =    λ {A} {B} → record
                       { refl = ≐-refl
                       ; sym = ≐-sym
                       ; trans = ≐-trans } -- record { IsEquivalence ≐-isEquivalence } 
  ; ∘-resp-≡   =   ∘-resp-≐
  }
  where open import Relation.Binary

\end{code}

We can forget about the first sort or the second to arrive at our starting
category and so we have two forgetful functors.

\begin{code}
Forget : (ℓ : Level) → Functor (DependentCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀             =   Disting.Index
  ; F₁             =   Hom.mor
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ F≈G {x} → F≈G x
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
  { F₀               =   λ A → MkDist (A × (A → Bool)) (λ { (a , R) → R a } )
  ; F₁               =   λ f → MkHom (λ { (a , R) → f a , (λ b → {!!})}) {!!}
  ; identity         =   {!!}
  ; homomorphism     =   {!!}
  ; F-resp-≡        =   λ F≈G → {!!}
  }

Cofree : (ℓ : Level) → Functor (Sets ℓ) (DependentCat ℓ)
Cofree ℓ = record
  { F₀             =   λ A → MkDist {!!} (λ a → {!!})
  ; F₁             =   λ f → MkHom {!!} {!!}
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
    { η       = λ _ → {!!}
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ { (MkDist A R) → MkHom (λ a → {!!}) {!!} }
    ; commute = λ f → {!!} -- ≐-refl
    }
  ; zig = {!!} -- ≐-refl
  ; zag = {!!}
  }
  
Right :  (ℓ : Level) → Adjunction (Forget ℓ) (Cofree ℓ)
Right ℓ = record
  { unit = record
    { η = λ { (MkDist A R) → MkHom {!!} {!!}}
    ; commute = λ _ → {!!} -- ≐-refl
    }
  ; counit   =   record { η = λ _ → {!!} ; commute = λ f → {!!} }
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
  { F₀             =   λ S → Σ (Index S) {!!}
  ; F₁             =   λ F → mor F ×₁ {!!}
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =
    λ {A} {B} F≈G → {!!}
  }

-- Every set gives rise to an identity family on itself
ID : (ℓ : Level) → Functor (Sets ℓ) (DependentCat ℓ)
ID ℓ = record
  { F₀             =   λ A → MkDist A (λ _ → {!!})
  ; F₁             =   λ f → MkHom f {!!}
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
  ; counit   =   record { η = λ _ → MkHom proj₁ {!!} ; commute = λ _ → {!!} }
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
