\section{Obtaining Forgetful Functors}

We aim to realise a ``toolkit'' for an data-structure by considering a free
construction and proving it adjoint to a forgetful functor. Since the majority
of our theories are built on the category |Set|, we begin my making a helper
method to produce the forgetful functors from as little information as needed
about the mathematical structure being studied.

Indeed, it is a common scenario where we have an algebraic structure with a single
carrier set and we are interested in the categories of such structures along
with functions preserving the structure.

We consider a type of ``algebras'' built upon the category of |Sets|
---in that, every algebra has a carrier set and every homomorphism is a
essentially a function between carrier sets where the composition of
homomorphisms is essentially the composition of functions and the identity
homomorphism is essentially the identity function.

Such algebras consistute a category from which we obtain a method to
Forgetful functor builder for single-sorted algebras to Sets.

%{{{ Imports
\begin{ModuleHead}
\begin{code}
module Forget where

open import Level

open import Categories.Category  using  (Category)
open import Categories.Functor   using  (Functor)
open import Categories.Agda      using  (Sets)

open import Function2
open import Function
open import EqualityCombinators
\end{code}
\end{ModuleHead}
\edcomm{MA}{For one reason or another, the module head is not making the imports smaller.}
%}}}

%{{{ OneSortedAlg

A |OneSortedAlg| is essentially the details of a forgetful functor from
some category to |Sets|,

\begin{code}
record OneSortedAlg (ℓ : Level) : Set (suc (suc ℓ)) where
  field
    Alg          :   Set (suc ℓ)
    Carrier      :   Alg → Set ℓ
    Hom          :   Alg → Alg → Set ℓ
    mor          :   {A B : Alg} → Hom A B → (Carrier A → Carrier B)
    comp         :   {A B C : Alg} → Hom B C → Hom A B →  Hom A C
    .comp-is-∘   :   {A B C : Alg} {g : Hom B C} {f : Hom A B} → mor (comp g f) ≐ mor g ∘ mor f
    Id           :   {A : Alg} → Hom A A
    .Id-is-id    :   {A : Alg} → mor (Id {A}) ≐ id
\end{code}
%}}}

%{{{ oneSortedCategory

The aforementioned claim that algebras and their structure preserving morphisms
form a category can be realised due to the coherency conditions we requested viz
the morphism operation on homomorphisms is functorial.

\begin{code}
open import Relation.Binary.SetoidReasoning
oneSortedCategory : (ℓ : Level) → OneSortedAlg ℓ → Category (suc ℓ) ℓ ℓ
oneSortedCategory ℓ A = record
  { Obj     =   Alg
  ; _⇒_    =   Hom
  ; _≡_    =   λ F G → mor F ≐ mor G
  ; id      =   Id
  ; _∘_     =   comp
  ; assoc   =   λ {A B C D} {F} {G} {H} → begin⟨ ≐-setoid (Carrier A) (Carrier D) ⟩
          mor (comp (comp H G) F)   ≈⟨ comp-is-∘                     ⟩  
          mor (comp H G) ∘ mor F    ≈⟨ ∘-≐-cong₁ _ comp-is-∘         ⟩   
          mor H ∘ mor G ∘ mor F     ≈˘⟨ ∘-≐-cong₂ (mor H) comp-is-∘  ⟩  
          mor H ∘ mor (comp G F)    ≈˘⟨ comp-is-∘                    ⟩  
          mor (comp H (comp G F))   ∎
  ; identityˡ   =   λ{ {f = f} → comp-is-∘ ⟨≐≐⟩ Id-is-id ∘ mor f } 
  ; identityʳ   =   λ{ {f = f} → comp-is-∘ ⟨≐≐⟩ ≡.cong (mor f) ∘ Id-is-id }
  ; equiv       =   record { IsEquivalence ≐-isEquivalence }
  ; ∘-resp-≡   =   λ f≈h g≈k → comp-is-∘ ⟨≐≐⟩ ∘-resp-≐ f≈h g≈k ⟨≐≐⟩ ≐-sym comp-is-∘
  }
  where open OneSortedAlg A ; open import Relation.Binary using (IsEquivalence)
\end{code}
%}}}

%{{{ mkForgetful

The fact that the algebras are built on the category of sets is captured by the
existence of a forgetful functor.

\begin{code}
mkForgetful : (ℓ : Level) (A : OneSortedAlg ℓ) → Functor (oneSortedCategory ℓ A) (Sets ℓ)
mkForgetful ℓ A = record
  { F₀             =   Carrier
  ; F₁             =   mor
  ; identity       =   Id-is-id  $ᵢ
  ; homomorphism   =   comp-is-∘ $ᵢ
  ; F-resp-≡       =    _$ᵢ
  }
  where open OneSortedAlg A
\end{code}

That is, the constituents of a |OneSortedAlgebra| suffice to produce a category
and a so-called presheaf as well.
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

