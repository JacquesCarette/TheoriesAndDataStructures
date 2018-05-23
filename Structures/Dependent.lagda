\section{Dependent Sums}

We consider “dependent algebras” which consist of an index set and
a family of sets on it. Alternatively, in can be construed as a universe
of discourse along with an elected subset of interest. In the latter view
the free and cofree constructions products the empty and universal predicates.
In the former view, the we have an adjunction involving dependent products.

%{{{ Imports
\begin{code}
module Structures.Dependent where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjunction using (Adjunction)

open import Function using (id ; _∘_ ; const)
open import Function2 using (_$ᵢ)

open import Forget
open import EqualityCombinators hiding (_≡_ ; module ≡)
open import DataProperties

import Relation.Binary.HeterogeneousEquality
module ≅ = Relation.Binary.HeterogeneousEquality
open ≅ using (_≅_)

-- category of sets with heterogenous equality
Sets : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ 
Sets ℓ = record
  { Obj       = Set ℓ
  ; _⇒_       = λ A B → A → B
  ; _≡_       = λ {A} {B} f g → {x : A} → f x ≅ g x

  ; _∘_       = λ f g x → f (g x)
  ; id        = λ x → x

  ; assoc     = ≅.refl
  ; identityˡ = ≅.refl
  ; identityʳ = ≅.refl
  ; equiv     = record { refl = ≅.refl; sym = λ eq → ≅.sym eq ; trans = λ p q → ≅.trans p q }
  ; ∘-resp-≡  = λ{ {f = f} f≅h g≅k → ≅.trans (≅.cong f g≅k) f≅h}
  }
\end{code}
%}}}

%{{{ Dependent ; Hom
\subsection{Definition}
A |Dependent| algebra consists of a carrier acting as an index for another family of
functions. An array is an example of this with the index set being the valid indices.
Alternatively, the named fields of a class-object are the indices for that class-object.

\begin{code}
record Dependent a b : Set (lsuc (a ⊍ b)) where
  constructor MkDep
  field
    Sort : Set a
    Carrier : Sort → Set b

open Dependent
\end{code}

Alternatively, these can be construed as some universe |Index| furnished with a
constructive predicated |Field| :-)
That is to say, these may also be known as ``unary relational algebras''.

Moreover, we can construe |Index| as sort symbols, that is ``uninterpreted types''
of some universe, and |Field| is then the interpretation of those symbols as a
reification in the ambient type system.

Again, we may name these “many sorted”.

\begin{code}
record Hom {a b} (Src Tgt : Dependent a b) : Set (a ⊍ b) where
  constructor MkHom
  field
    mor   : Sort Src → Sort Tgt
    shift : {i : Sort Src} → Carrier Src i → Carrier Tgt (mor i)

open Hom
\end{code}

The |shift| condition may be read, in the predicate case, as:
if |i| is in the predicate in the source, then its images is in the predicate of
the target.

Such categories have been studies before under the guide ``the category of sets
with an elected subset''.

%}}}

%{{{ TwoCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
Dependents : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Dependents ℓ = record
  { Obj        =     Dependent ℓ ℓ
  ; _⇒_       =     Hom
  ; _≡_       =     λ {A} {B} F G → ({x : Sort A} → mor F x ≅ mor G x)
                                    × ({s : Sort A} {f : Carrier A s} → shift F f ≅ shift G f)
  ; id         =    MkHom id id
  ; _∘_        =    λ F G → MkHom (mor F ∘ mor G) (shift F ∘ shift G)
  ; assoc      =    ≅.refl , ≅.refl
  ; identityˡ   =    ≅.refl , ≅.refl
  ; identityʳ   =    ≅.refl , ≅.refl
  ; equiv       =    record
    { refl = ≅.refl , ≅.refl
    ; sym = λ{ (eq , eq') → ≅.sym eq , ≅.sym eq'}
    ; trans = λ{ (peq , peq') (qeq , qeq') → ≅.trans peq qeq , ≅.trans peq' qeq' }
    }
  ; ∘-resp-≡   =   λ{ {A} {B} {C} {f} {h} {g} {k} (f≅h , f≅h') (g≅k , g≅k')
                   → ≅.trans (≅.cong (mor f) g≅k) f≅h , λ {s} {op} →  ≅.trans {x = shift f (shift g op)} {z = shift h (shift k op)} {!≅.cong {x = shift k op} {y = ?} (shift f) ?!} f≅h' }
  }
  where open import Relation.Binary
\end{code}

We can forget about the first sort or the second to arrive at our starting
category and so we have two forgetful functors.

\begin{code}
Forget : (ℓ : Level) → Functor (Dependents ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀             =   Dependent.Sort
  ; F₁             =   Hom.mor
  ; identity       =   ≅.refl
  ; homomorphism   =   ≅.refl
  ; F-resp-≡      =   λ{ (F≈G , _) → F≈G }
  }
\end{code}

\edcomm{MA}{ToDo ∷ Construct another forgetful functor}

%}}}

%{{{ Free and CoFree
\subsection{Free and CoFree}
Given a type, we can pair it with the empty type or the singelton type
and so we have a free and a co-free constructions. 

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (Dependents ℓ)
Free ℓ = record
  { F₀               =   λ A → MkDep A (λ _ → ⊥)
  ; F₁               =   λ f → MkHom f id
  ; identity         =   ≅.refl , ≅.refl
  ; homomorphism     =   ≅.refl , ≅.refl
  ; F-resp-≡        =   λ F≈G → F≈G , ≅.refl
  }

Cofree : (ℓ : Level) → Functor (Sets ℓ) (Dependents ℓ)
Cofree ℓ = record
  { F₀             =   λ A → MkDep A (λ _ → ⊤)
  ; F₁             =   λ f → MkHom f id
  ; identity       =   ≅.refl , ≅.refl
  ; homomorphism   =   ≅.refl , ≅.refl
  ; F-resp-≡      =   λ f≈g → f≈g , ≅.refl
  }
\end{code}

%}}}

%{{{ Left and Right adjunctions
\subsection{Left and Right adjunctions}
Now for the actual proofs that the |Free| and |Cofree| functors
are deserving of their names.

\begin{code}
Left : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
Left ℓ = record
  { unit   = record
    { η       = λ _ → id
    ; commute = λ _ → ≅.refl
    }
  ; counit = record
    { η       = λ _ → MkHom id (λ {()})
    ; commute = λ f → ≅.refl , (λ{ {_}{()} })
    }
  ; zig = ≅.refl , (λ{ {_}{()} })
  ; zag = ≅.refl
  }
  
Right :  (ℓ : Level) → Adjunction (Forget ℓ) (Cofree ℓ)
Right ℓ = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) 
    ; commute = λ _ → ≅.refl , ≅.refl
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≅.refl }
  ; zig      =   ≅.refl
  ; zag      =   ≅.refl , (λ{ {_} {tt} → ≅.refl})
  }
\end{code}
%}}}

%{{{ Merge and Dup functors ; Right₂ adjunction
\subsection{DepProd}

The category of sets contains products and so |Dependent| algebras can be represented there
and, moreover, this is adjoint to duplicating a type to obtain a |TwoSorted| algebra.

\begin{spec}
≡-cong-Σ  :  {a b : Level} {A : Set a} {B : A → Set b}
          →  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
          →  (x₁≡x₂ : x₁ ≡ x₂) → y₁ ≡ ≡.subst B (≡.sym x₁≡x₂) y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
≡-cong-Σ ≡.refl ≡.refl = ≡.refl
\end{spec}

\begin{code}
DepProd : (ℓ : Level) → Functor (Dependents ℓ) (Sets ℓ)
DepProd ℓ = record
  { F₀             =   λ S → Σ (Sort S) (Carrier S)
  ; F₁             =   λ F → mor F ×₁ shift F
  ; identity       =   λ{ {_} {fst , snd} → ≅.refl }
  ; homomorphism   =   ≅.refl
  ; F-resp-≡      =   λ{ (F≈G , eq) → ≅.cong₂ _,_ F≈G eq } -- This was the troublesome hole; now filled!
  }
\end{code}

\emph{Begin inactive material}

\begin{spec}
  where helper : {a b : Level} {S T : Dependent a b} {F G : Hom S T}
               → (F≈G : mor F ≐ mor G)
               → {i : Sort S} {f : Carrier S i} 
               → shift F f ≡  ≡.subst (Carrier T) (≡.sym (F≈G i)) (shift G f)
        helper {S = S} {T} {F} {G} F≈G {i} {f} with ≡.cong (Carrier T) (F≈G i)
        ...| r = {!see RATH's propeq utils, maybe something there helps!} 


-- |‼ consider using Relation.Binary.HeterogenousEquality …!|

-- Every set gives rise to an identity family on itself
ID : (ℓ : Level) → Functor (Sets ℓ) (Dependents ℓ)
ID ℓ = record
  { F₀             =   λ A → MkDep A (λ _ → A)
  ; F₁             =   λ f → MkHom f f
  ; identity       =   ≐-refl
  ; homomorphism   =   ≐-refl
  ; F-resp-≡      =   λ F≈G → λ x → F≈G {x}
  }


-- |look into having a free functor from TwoCat, then _×_ pops up!|
-- maybe not, what is the forgetful functor...!
f : {!\unfinished!}
f = {!\unfinished!}



Then the proof that these two form the desired adjunction


Right₂ : (ℓ : Level) → Adjunction (ID ℓ) (DepProd ℓ)
Right₂ ℓ = record
  { unit     =   record { η = λ _ → diag ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ _ → MkHom proj₁ (λ{ {i , f} _ → f}) ; commute = λ _ → ≐-refl }
  ; zig      =   ≐-refl
  ; zag      =   ≡.refl
  }
\end{spec}
%}}}

|Note that since Σ encompasses both × and ⊎, it may not be that there is another functor|
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
