\section{Structures.Sidequest.Permutations.Group}

The group structure of permutations.

This file currently lists the postulated interface as the implementation is incomplete.

The intended route of attack is to tackle one postulate at a time, all the while forming
tests within |Sidequest.Permutations.Testing.lagda|.

%{{{ Imports
\begin{code}
open import Level           using (Level)
open import Relation.Binary using (Setoid)
open import Function        using (_$_)

import Relation.Binary.Indexed as I
open import EqualityCombinators hiding (reflexive)

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ   ; zero ; suc ; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup ; allFin)

open import Structures.Sidequest.Permutations.Basic

module Structures.Sidequest.Permutations.Group {s₁ s₂} (S : Setoid s₁ s₂) where

open import Structures.Sidequest.Permutations.Basic
open import Structures.Sidequest.Permutations.Vector
open import Structures.Sidequest.Permutations.ActionProperties S
open import Structures.Sidequest.Equality S renaming (_≈_ to _≈ₖ_)

private
  open module ≈₀ = Setoid S using (Carrier) renaming (_≈_ to _≈₀_)
  Seq = Vec Carrier
\end{code}
%}}}

%{{{ POSTULATED Interface

Permutations form a group,
\begin{code}
infix 5 _≈₁_
infix 6 _⊙_
infix 7 _˘

postulate

  ℓℓℓ : Level
  _≈₁_ : {n m : ℕ} → (a b : Permutation n m) → Set ℓℓℓ
    
  _⊙_ : {n m r : ℕ} → Permutation n m → Permutation m r → Permutation n r
  
  ⊙-cong : {n m r : ℕ} {a a′ : Permutation n m} {b b′ : Permutation m r}
         → a ≈₁ a′ → b ≈₁ b′ → a ⊙ b ≈₁ a′ ⊙ b′
  
  ⊙-assoc : {n m r s : ℕ} {a : Permutation n m} {b : Permutation m r} {c : Permutation r s}
          → (a ⊙ b) ⊙ c ≈₁ a ⊙ (b ⊙ c)
  
  ⊙-leftId : {n m : ℕ} {a : Permutation n m} → Id ⊙ a ≈₁ a
  
  ⊙-rightId : {n m : ℕ} {a : Permutation n m} → a ⊙ Id ≈₁ a
    
  _˘ : {n m : ℕ} → Permutation n m → Permutation m n
  
  ˘-cong : {n m : ℕ} {a a′ : Permutation n m} → a ≈₁ a′ → a ˘ ≈₁ a′ ˘
  
  ˘- : {n m : ℕ} {a : Permutation n m} → a ˘ ⊙ a ≈₁ Id
  
  solve-linear-equation : {n m r : ℕ} {a : Permutation n m} {x : Permutation m r} {b : Permutation n r}
    → a ⊙ x ≈₁ b → x ≈₁ a ˘ ⊙ b
  
  ˘-shunting : {n m : ℕ} {a : Permutation n m} {b : Permutation m n}
             → a ˘ ≈₁ b → a ≈₁ b ˘
\end{code}

Moreover, permutations provide a group action on vectors:
\begin{code}
postulate

  ◈-cong₁ : {n m : ℕ} {a b : Permutation n m} {xs : Vec Carrier n}
          → a ≈₁ b → a ◈ xs ≈ₖ b ◈ xs
  
  ◈-compose : {n m r : ℕ} {a : Permutation n m} {b : Permutation m r}
            → {xs : Vec Carrier n} → (a ⊙ b) ◈ xs  ≈ₖ  b ◈ (a ◈ xs)
  
  ◈-solve-linear-equation : {n m : ℕ} {w : Permutation n m} {xs : Vec Carrier n} {ys : Vec Carrier m}
    → w ◈ xs ≈ₖ ys → xs ≈ₖ w ˘ ◈ ys
\end{code}

\begin{spec}
◈-solve-linear-equation {n} {m} {w} {xs} {ys} w◈x≈y
  = sym Id-◈
  ⟨≈ₖ≈⟩ {!!} -- ◈-cong₁ (˘- {n} {m} {a = w})
  ⟨≈ₖ≈⟩ sym (◈-compose {a = w} {b = w ˘} {xs = xs})
  ⟨≈ₖ≈⟩ {!!} -- ◈-cong₂ {m} {n} {ps = w ˘} {w ◈ xs} {ys} w◈x≈y
\end{spec}
%}}}

%{{{ Current Implementation Efforts

The following should be heterogenous, |{n m : ℕ}|.
\begin{spec}
_˘ : {m n : ℕ} → Permutation n m → Permutation m n
ps ˘ = fromVector′ (homogeneity ps) (ps ◇ allFin _)

rndm-guess : {m n : ℕ} {ps : Permutation m n} {xs : Vec Carrier n}
           →  ps ◇ xs  ≈ₖ  fromVector′ (homogeneity ps) (ps ◇ allFin _) ◈ xs
rndm-guess {m} {.0} {[]} {[]} = refl _
rndm-guess {m} {.(suc _)} {zero ∷ ps} {x ∷ xs} = {!!}
rndm-guess {m} {.(suc _)} {suc p ∷ ps} {x ∷ xs} = {!!}

-- use inversion theorem, above, to prove this result!
crux : {n : ℕ} {ps : Permutation n n} {xs ys : Vec Carrier n} → ps ◈ xs ≈ₖ ys → xs ≈ₖ (ps ˘) ◈ ys
crux {n} {ps} {xs} {ys} = {!!}
\end{spec}

Thought process:
\begin{spec}
      ps ◈ xs ≈ ys
⇒    ps ◇ (ps ◈ xs) ≈ ps ◇ ys                     -- ◇-cong
≡    xs ≈ ps ◇ ys                                  -- inversion theorem
≡    xs ≈ fromVector (ps ◇ allFin _) ◈ ys          -- ???  
≡    xs ≈  ps ˘ ◈ ys                                -- 
\end{spec}

Alternative definition of -˘.

( vmchale makes no recursive call … )
\begin{spec}
open import Relation.Nullary

-- Permutations come with the obvious involution, but non-trivial implementation
_˘ : {n m : ℕ} → Permutation n m → Permutation m n
_˘ {zero }          []        = []
_˘ {suc n} {suc m} pp@(p ∷ ps) = (toVector′ pp ‼ p) ∷ {!!} -- ((ps ─ i' ps ?) ˘)
  where
        i' : {i j : ℕ} → Permutation (suc i) (suc j) → Fin (suc j) → Fin (suc i)
        i' q idx = (toVector′ q) ‼ idx
\end{spec}

Specification/characterisation of inverse: It can be used to solve equations.
\begin{spec}
˘-char : {n m : ℕ} {xs : Vec ≈.Carrier n} {p : Permutation n m} {ys : Vec ≈.Carrier m} → p ◈ xs ≈ₖ ys → p ˘ ◈ ys ≈ₖ xs
˘-char {zero} {.0} {[]} {[]} {[]} eq = eq
˘-char {suc n} {zero} {xs} {()} {[]} eq
˘-char {suc n} {suc m} {x ∷ xs} {zero ∷ p₁} {x₁ ∷ ys} (x≈y ∷-cong eq) = (≈.sym x≈y) ∷-cong (˘-char eq)
˘-char {suc n} {suc m} {x ∷ xs} {suc p ∷ p₁} {x₁ ∷ ys} eq = {!!}
\end{spec}

This is part of the definition of permutation equality:
\begin{spec}
◈-cong₁ : {n m : ℕ} {ps qs : Permutation n m} {xs : Seq n}
        → ps ≈ₚ qs → ps ◈ xs ≈ₖ qs ◈ xs
◈-cong₁ eq = eq
\end{spec}
This is perhaps not what we want.

Composition of permutations
\edcomm{MA}{This particular form of typing is chosen so that |Permutation| acts as a morphism}
type constructor for a category whose objects are natural numbers. Then this composition
has the type necessary to make this into a category.
\begin{spec}
infix 6 _⊙_
_⊙_ : {n m r : ℕ} → Permutation n m → Permutation m r → Permutation n r
[] ⊙ [] = []
(p ∷ ps) ⊙ (q ∷ qs) = (toVector (q ∷ qs) ‼ p) ∷ ps ⊙ qs -- (qs at′ p) ∷ (ps ⊙ (qs ─ p))
\end{spec}

-- \edcomm{MA}{I made componentwise equality heterogenous in order to make the typing here more}
-- general; yet it is not.
\begin{spec}
◈-compose : {n m r : ℕ} {ps : Permutation n m} {qs : Permutation m r}
          → {xs : Seq n} → (ps ⊙ qs) ◈ xs  ≈ₖ  qs ◈ (ps ◈ xs)
◈-compose {ps = []} {[]} {[]} = nil
◈-compose {ps = zero ∷ ps} {q ∷ qs} {x ∷ xs} = {!!}
◈-compose {ps = suc p ∷ ps} {q ∷ qs} {x ∷ xs} = {!!}
\end{spec}

\edcomm{MA}{ToDo: Prove this composition is associative; i.e., finish the construction site below.}
\begin{spec}
  -- ⊙-nil : {n : ℕ} {ps : Permutation n} → ps ⊙ nil  ≡  ps
  -- ⊙-nil {n} {ps} = ?

  -- The inversion operation is contravariant: It reverses composition.
  ◈-˘ : {n : ℕ} {ps qs : Permutation n} → (ps ⊙ qs)˘  ≈ₚ (qs ˘ ⊙ ps ˘)
  ◈-˘ {.0} {nil} {nil} = ≈ₖ-refl
  ◈-˘ {.(suc _)} {cons p ps} {qs} = {! MA: write a test to be confident this is somewhat true.!}

  insert-◈ : {n : ℕ} {ps : Permutation n} {q : Fin (suc n)} {qs : Permutation n}
             {xs : Seq n} {x : Carrier}
           → insert (ps ◈ (qs ◈ xs)) q x  ≈ₖ  (cons zero ps) ◈ (insert (qs ◈ xs) q x)
  insert-◈ {n} {ps} {q} {qs} {xs} = {! MA: write a test to be confident this is somewhat true.!}

  ◈-compose : {n : ℕ} {ps qs : Permutation n} {xs : Seq n} → (ps ⊙ qs) ◈ xs  ≈ₖ  ps ◈ (qs ◈ xs)
  ◈-compose {.0} {nil} {nil} {[]} = ≈ₖ-refl
  ◈-compose {.(suc _)} {cons zero ps} {cons q qs} {x ∷ xs} = ≈ₖ-trans (insert-cong ◈-compose) insert-◈
  ◈-compose {.(suc _)} {cons (suc p) ps} {cons q qs} {x ∷ xs} = {! MA: write a test to be confident this is somewhat true. !}
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
