\section{Structures.Sidequest.Equality}

Documenting congruence laws for |insert| and |remove|; culminating in the notable inversion laws:
\begin{spec}
  inversionTheorem  : ∀ p xs → p ◇ (p ◈ xs) ≈ₖ xs
  inversionTheorem˘ : ∀ p xs → p ◈ (p ◇ xs) ≈ₖ xs
\end{spec}

( These names are the other way around wrt “elimination”; they ought to be swapped.
  c.f. ActionProperties.lagda )

%{{{ Imports
\begin{code}
open import Level           using (Level)
open import Relation.Binary using (Setoid)
open import Function        using (_$_)

import Relation.Binary.Indexed as I
open import EqualityCombinators hiding (reflexive)

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ   ; zero ; suc ; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)

open import Structures.Sidequest.Permutations.Basic

module Structures.Sidequest.Equality {s₁ s₂} (S : Setoid s₁ s₂) where

private
  open module ≈₀ = Setoid S using (Carrier) renaming (_≈_ to _≈₀_)
  Seq = Vec Carrier
\end{code}

Subscript 0 for ``underlying'', or `base', equality.
%}}}

\begin{code}
-- Copy of Data.Vec.Equality.Equality, then tweaked.

infix 4 _≈_
data _≈_ : {n¹ n² : ℕ} → Seq n¹ → Seq n² → Set s₂ where
  []-cong  : [] ≈ []
  _∷-cong_ : {x : Carrier} {m : ℕ} {xs : Seq m} {y : Carrier} {n : ℕ} {ys : Seq n}
             (x≈y : x ≈₀ y) (xs≈ys : xs ≈ ys) → x ∷ xs ≈ y ∷ ys
\end{code}

Even though we have declared our equality to be heterogeneous at the length level,
the only possible equality proofs are necessarily homogeneous:

\begin{code}
length-equal : {m n : ℕ} {xs : Seq m} {ys : Seq n} →  xs ≈ ys → m ≡ n
length-equal []-cong         =  ≡.refl
length-equal (_ ∷-cong eq₂)  =  ≡.cong suc $ length-equal eq₂
\end{code}

%{{{ refl ; sym ; trans ; Seq-IsSetoid

This relation is indeed an equivalence relation.

\begin{code}
refl : {n : ℕ} (xs : Seq n) → xs ≈ xs
refl []       = []-cong
refl (x ∷ xs) = ≈₀.refl ∷-cong refl xs

reflexive : {n : ℕ} {xs ys : Seq n} → xs ≡ ys → xs ≈ ys
reflexive ≡.refl = refl _

sym : {n m : ℕ} {xs : Seq n} {ys : Seq m} → xs ≈ ys → ys ≈ xs
sym []-cong                  =  []-cong
sym (x¹≡x² ∷-cong xs¹≈xs²)  =  ≈₀.sym x¹≡x² ∷-cong sym xs¹≈xs²

trans : {n m l : ℕ} {xs : Seq n} {ys : Seq m} {zs : Seq l}
      →  xs ≈ ys → ys ≈ zs → xs ≈ zs
trans []-cong            []-cong             =  []-cong
trans (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs)  =
  ≈₀.trans x≈y y≈z  ∷-cong  trans xs≈ys ys≈zs

Seq-ISetoid : I.Setoid ℕ s₁ s₂
Seq-ISetoid = record { Carrier = Seq ; _≈_ = _≈_
  ; isEquivalence = record
    { refl    =   λ {n} {xs} → refl {n} xs
    ; sym     =   sym
    ; trans   =   trans
    }
  }
\end{code}
%}}}

%{{{ Equality combinators

Material ported from |Relation.Binary.PreorderReasoning|.

\begin{code}
module Seq≈ = I.Setoid Seq-ISetoid

infix  4 _IsRelatedTo_
infix  3 _□ₖ
infixr 2 _≈ₖ⟨_⟩_ _≈ₖ≡⟨_⟩_ _≈ₖ˘⟨_⟩_ _≈ₖ≡˘⟨_⟩_ _≈ₖ⟨⟩_
infix  1 ≈ₖ-begin_

data _IsRelatedTo_ {m n : ℕ} (x : Seq m) (y : Seq n) : Set s₂ where
  relTo : (x∼y : x ≈ y) → x IsRelatedTo y

≈ₖ-begin_ : {m n : ℕ} {x : Seq m} {y : Seq n} → x IsRelatedTo y → x ≈ y
≈ₖ-begin relTo x∼y = x∼y

_≈ₖ⟨_⟩_  : {k m n : ℕ} (x : Seq k) {y : Seq m} {z : Seq n}
        → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈ₖ⟨ x≈y ⟩ relTo y≈z = relTo (trans x≈y y≈z)

_≈ₖ˘⟨_⟩_  : {k m n : ℕ} (x : Seq k) {y : Seq m} {z : Seq n}
        → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
_ ≈ₖ˘⟨ y≈x ⟩ relTo y≈z = _ ≈ₖ⟨ sym y≈x ⟩ relTo y≈z

_≈ₖ≡⟨_⟩_  : {m n : ℕ} (x : Seq m) {y : Seq m} {z : Seq n}
        → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈ₖ≡⟨ x≡y ⟩ relTo y≈z = relTo (trans (Seq≈.reflexive x≡y) y≈z)

_≈ₖ≡˘⟨_⟩_  : {m n : ℕ} (x : Seq m) {y : Seq m} {z : Seq n}
        → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
_ ≈ₖ≡˘⟨ y≡x ⟩ relTo y≈z = _ ≈ₖ≡⟨ ≡.sym y≡x ⟩ relTo y≈z

_≈ₖ⟨⟩_  : {m n : ℕ} (x : Seq m) {y : Seq n}
        → x IsRelatedTo y → x IsRelatedTo y
_ ≈ₖ⟨⟩ x≈y = x≈y

_□ₖ : {n : ℕ} (x : Seq n) → x IsRelatedTo x
_□ₖ _ = relTo (refl _)

-- handy-dandy combinator for `k`component-wise equality transitivity.
infixl 4 _⟨≈ₖ≈⟩_
_⟨≈ₖ≈⟩_ = trans
\end{code}
%}}}

%{{{ _++-cong_ ; _‼_ ; lookup-cong₂

\begin{code}
_++-cong_ : {m n     : ℕ} {xs   : Seq m  } {ys  : Seq n  }
            {m′ n′ : ℕ} {xs′ : Seq m′} {ys′ : Seq n′}
          → xs ≈ xs′ → ys ≈ ys′ → xs ++ ys  ≈  xs′ ++ ys′
[]-cong          ++-cong eq₃  =  eq₃                           -- left identity law
(eq₁ ∷-cong eq₂) ++-cong eq₃  =  eq₁ ∷-cong (eq₂ ++-cong eq₃)  -- mutual associativity law

lookup-cong₂ : {n : ℕ} {i : Fin n} {xs ys : Seq n} → xs ≈ ys → lookup i xs ≈₀ lookup i ys
lookup-cong₂ {i =  _   } []-cong          =  ≈₀.refl
lookup-cong₂ {i = zero } (x≈y ∷-cong _ )  =  x≈y
lookup-cong₂ {i = suc i′} (_   ∷-cong eq)  =  lookup-cong₂ {i = i′} eq
\end{code}
%}}}

%{{{ insert-cong₁ ; insert-cong₂ ; insert-cong₃ ; remove-cong₂
\begin{code}
insert-cong₁ : {n : ℕ} {xs ys : Seq n} {i : Fin (1 + n)} {e : Carrier}
             → xs ≈ ys → insert xs i e  ≈  insert ys i e
insert-cong₁ {i = zero}  xs≈ys               =  ≈₀.refl ∷-cong xs≈ys
insert-cong₁ {i = suc _} []-cong             =  refl _
insert-cong₁ {i = suc i} (x≈y ∷-cong xs≈ys)  =  x≈y ∷-cong insert-cong₁ {i = i} xs≈ys

insert-cong₂ : {n : ℕ} {xs : Seq n} {i j : Fin (1 + n)} {e : Carrier}
             → i ≡ j → insert xs i e  ≈  insert xs j e
insert-cong₂ ≡.refl = refl _

insert-cong₃ : {n : ℕ} {xs : Seq n} {i : Fin (1 + n)} {d e : Carrier}
             → e ≈₀ d → insert xs i e  ≈  insert xs i d
insert-cong₃ {xs = []   } {zero  } e≈d  = e≈d      ∷-cong  []-cong
insert-cong₃ {xs = []   } {suc ()} _
insert-cong₃ {xs = _ ∷ _} {zero  } e≈d  =  e≈d     ∷-cong  refl _
insert-cong₃ {xs = _ ∷ xs} {suc i} e≈d  =  ≈₀.refl ∷-cong  insert-cong₃ {xs = xs} {i} e≈d

remove-cong₂ : {n : ℕ} {i : Fin (suc n)} {xs ys : Seq (suc n)}
            → xs ≈ ys → removeElem i xs ≈ removeElem i ys
remove-cong₂ {_}     {zero  } (_ ∷-cong xs≈ys) = xs≈ys
remove-cong₂ {zero } {suc ()} (_ ∷-cong _)
remove-cong₂ {suc _} {suc i } {_ ∷ _} {_ ∷ _} (x≈y ∷-cong xs≈ys)
  = x≈y  ∷-cong  remove-cong₂ {i = i} xs≈ys
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
