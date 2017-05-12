-- Commonly needed combinators :: Re-exports \emph{all} equality related concepts
-- Propositional and function extensional

module EqualityCombinators where


-- Propositional Equality

import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ using (_≡_) public

_⟨≡≡⟩_ = ≡.trans  -- handy synonyms


-- Function Extensionality

open import Equiv public

_⟨≐≐⟩_ = ≐-trans
