\section{Equality Combinators}

Here we export all equality related concepts, including those for propositional and
function extensional equality.

\begin{code}
module EqualityCombinators where

open import Level
\end{code}

%{{{ Propositional Equality

\subsection{Propositional Equality}

We use one of Agda's features to qualify all propositional equality properties
by ``|≡.|'' for the sake of clarity and to avoid name clashes with similar other
properties.

\begin{code}
import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ using (_≡_) public
\end{code}

We also provide two handy-dandy combinators for common uses of transitivity proofs.

\begin{code}
_⟨≡≡⟩_ = ≡.trans

_⟨≡≡˘⟩_ : {a : Level} {A : Set a} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
x≈y ⟨≡≡˘⟩ z≈y = x≈y ⟨≡≡⟩ ≡.sym z≈y
\end{code}
%}}}

%{{{ Function Extensionality
\subsection{Function Extensionality}

We bring into scope pointwise equality, |_≐_|, and provide a proof that it constitutes
an equivalence relation ---where the source and target of the functions being compared
are left implicit.

\begin{code}
open ≡ using () renaming (_→-setoid_ to ≐-setoid ; _≗_ to _≐_) public

open import Relation.Binary using (IsEquivalence ; Setoid)

module _ {a b : Level} {A : Set a} {B : Set b} where

  ≐-isEquivalence : IsEquivalence (_≐_ {A = A} {B})
  ≐-isEquivalence =  record {Setoid (≐-setoid A B) }

  open IsEquivalence ≐-isEquivalence public
    renaming (refl to ≐-refl ; sym to ≐-sym ; trans to ≐-trans)

  open import Equiv public using (∘-resp-≐) -- To do: port this over here!
    renaming (cong∘l to ∘-≐-cong₂ ; cong∘r to ∘-≐-cong₁)

infixr 5 _⟨≐≐⟩_
_⟨≐≐⟩_ = ≐-trans
\end{code}

Note that the precedence of this last operator is lower than that of function composition so as to avoid superfluous parenthesis.
%}}}

%{{{ Equiv
\subsection{Equiv}

We form some combinators for HoTT like reasoning.

\begin{code}
cong₂D : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → B x → C)
            → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
            → (x₂≡x₁ : x₂ ≡ x₁) → ≡.subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
cong₂D f ≡.refl ≡.refl = ≡.refl

open import Equiv public using (_≃_; id≃; sym≃; trans≃; qinv)

infix  3 _◻
infixr 2 _≃⟨_⟩_

_≃⟨_⟩_ : {x y z : Level} (X : Set x) {Y : Set y} {Z : Set z} 
      →  X ≃ Y → Y ≃ Z → X ≃ Z
X ≃⟨ X≃Y ⟩ Y≃Z = trans≃ X≃Y Y≃Z

_◻ : {x : Level} (X : Set x) → X ≃ X
X ◻ = id≃
\end{code}

\edcomm{MA}{Consider moving pertinent material here from |Equiv.lagda| at the end.}
%}}}

%{{{ _≈˘⟨_⟩_
\subsection{Making |sym|metry calls less intrusive}

It is common that we want to use an equality within a calculation as a right-to-left rewrite rule which
is accomplished by utilizing its symmetry property. We simplify this rendition, thereby saving an explicit
call and parenthesis in-favour of a less hinder-some notation.

Among other places, I want to use this combinator in module |Forget|'s proof of associativity for |oneSortedCategory|

\begin{code}
module _ {c l : Level} {S : Setoid c l} where

  open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_)
  open import Relation.Binary.EqReasoning     using (_IsRelatedTo_)
  open Setoid S

  infixr 2 _≈˘⟨_⟩_
  _≈˘⟨_⟩_ : ∀ (x {y z} : Carrier) → y ≈ x → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
  x ≈˘⟨ y≈x ⟩ y≈z = x ≈⟨ sym y≈x ⟩ y≈z
\end{code}

A host of similar such combinators can be found within the RATH-Agda library.
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
