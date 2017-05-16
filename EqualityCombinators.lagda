-- Commonly needed combinators :: Re-exports \emph{all} equality related concepts
-- Propositional and function extensional

\begin{code}
module EqualityCombinators where

open import Level
\end{code}

%{{{ Propositional Equality

\begin{code}
import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ using (_≡_) public

_⟨≡≡⟩_ = ≡.trans

_⟨≡≡˘⟩_ : {a : Level} {A : Set a} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
x≈y ⟨≡≡˘⟩ z≈y = x≈y ⟨≡≡⟩ ≡.sym z≈y 
\end{code}
%}}}

%{{{ Function Extensionality

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

-- Note that the precedence is lower than that of function composition to avoid superfluous parenthesis.
infixr 5 _⟨≐≐⟩_
_⟨≐≐⟩_ = ≐-trans
\end{code}
%}}}

%{{{ _≈˘⟨_⟩_ ; ‼ does not work as intended ‼

Want to use this combinator in module |Forget|'s proof of associativity for |oneSortedCategory|

Sadly, it currently does not work as intended.

\begin{code}
module _ {c l : Level} {S : Setoid c l} where

  open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_)
  open import Relation.Binary.EqReasoning     using (_IsRelatedTo_)
  open Setoid S

  _≈˘⟨_⟩_ : ∀ (x {y z} : Carrier) → y ≈ x → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
  x ≈˘⟨ y≈x ⟩ y≈z = x ≈⟨ sym y≈x ⟩ y≈z

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
