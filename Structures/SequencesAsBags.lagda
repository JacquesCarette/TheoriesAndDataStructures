\section{Bags Implemented by Sequences}

Here we use |Table| as a means to implement |Bags|. This ends up being somewhat more convenient
than using |List| directly, even though how we use them are equivalent types. One important
aspect is that the tables involved are over a |Setoid|.

%{{{ imports
\begin{code}
module Structures.SequencesAsBags where

open import Level
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Table using (Table; permute; rearrange; lookup)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Table.Relation.Equality using (setoid)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.SetoidReasoning
open import Function.Equality using (module Π)
import Function.Inverse as Inv using (module Inverse)
open import Function.Inverse using (_↔_)
open import Algebra   using (CommutativeMonoid)

open import FinEquivPlusTimes using (module Plus)
open import FinEquivTypeEquiv using (module PlusE; _fin≃_)
open import TypeEquiv using (swap₊)
import Equiv
\end{code}
%}}}

%{{{ Seq
\begin{code}
-- A “sequence” is the functional view of a list ─which are properly handled in Agda as vectors.
-- `ATable`
record Seq {a : Level} (A : Set a) : Set a where
  constructor sequence
  field
   len : ℕ
   _‼_ : Fin len → A  -- lookup operation

  -- These are of-course just |Table|s where the length is packaged into the record;
  -- thereby being somewhat more homogeneous or “untyped”.

  table : Table A len
  table = Table.tabulate _‼_

open Seq public

table˘ : {a : Level} {A : Set a} {n : ℕ} → Table A n → Seq A
table˘ {n = n} it = sequence n (lookup it)

-- Permute operation lifted from tables to sequences.
sPermute : {a : Level} {A : Set a} (T : Seq A) {m : ℕ} (p : Fin m ↔ Fin (len T)) → Seq A
sPermute T p = table˘ (permute p (table T))

infix 4 sPermute
syntax sPermute T p  =  p ◈ T

-- Table setoid on vectors of length |len T₁|.
Eq : {ℓ c : Level} (S : Setoid ℓ c) {n : ℕ} → Setoid ℓ c
Eq S {n} = setoid S n

\end{code}
%}}}

%{{{ Sequence equality _≈ₛ_ ; BagRep
\begin{code}
module _ {ℓ c : Level} (S : Setoid ℓ c) where
  open Setoid S using () renaming (Carrier to S₀)

  infixr 3 _≈ₛ_
  record _≈ₛ_ (T₁ T₂ : Seq S₀) : Set (ℓ ⊔ c) where
    constructor _⟨π⟩_
    open Setoid (setoid S (len T₁)) -- Table setoid on vectors of length |len T₁|.
    field
      shuffle : Permutation (len T₁) (len T₂)
      eq : (table T₁) ≈ permute shuffle (table T₂)

    homogenous : len T₁ P.≡ len T₂
    homogenous = ↔⇒≡ shuffle

  open _≈ₛ_

  ≈ₛ-refl : {T : Seq S₀} → T ≈ₛ T
  ≈ₛ-refl {T} = record { shuffle = id ; eq = refl }
    where open Setoid (Eq S)

  interchange : (f : Seq S₀) {m : ℕ} (s : Permutation m (len f)) {k : Fin m}
                (let open Setoid S) → (s ◈ f) ‼ k ≈ f ‼ (s ⟨$⟩ʳ k)
  interchange f {m} s {k} = let open Setoid S in begin⟨ S ⟩
      (s ◈ f) ‼ k
    ≈⟨ refl ⟩
      table˘ (permute s (table f)) ‼ k
    ≈⟨ refl ⟩
      lookup (permute s (table f)) k
    ≈⟨ refl ⟩
      lookup (rearrange (s ⟨$⟩ʳ_) (table f) ) k
    ≈⟨ refl ⟩
      lookup (table f) (s ⟨$⟩ʳ k)
    ≈⟨ refl ⟩
      f ‼ (s ⟨$⟩ʳ k)
    ∎

  ≈ₛ-sym : {f g : Seq S₀} → f ≈ₛ g → g ≈ₛ f
  ≈ₛ-sym {f} {g} (s ⟨π⟩ f≈sg) = let open Setoid S in record
    { shuffle = flip s
    ; eq = λ k → begin⟨ S ⟩
           g ‼ k
         ≡⟨  P.sym (P.cong (g ‼_) (inverseʳ s)) ⟩
           g ‼ (s ⟨$⟩ʳ (s ⟨$⟩ˡ k))
         ≈⟨ refl ⟩
           (s ◈ g) ‼ (s ⟨$⟩ˡ k)
         ≈⟨ sym (f≈sg (s ⟨$⟩ˡ k)) ⟩
           f ‼ (s ⟨$⟩ˡ k)
         ≈⟨ refl ⟩
           (flip s ◈ f) ‼ k
         ∎
    }

  ≈ₛ-trans : {f g h : Seq S₀} → f ≈ₛ g → g ≈ₛ h → f ≈ₛ h
  ≈ₛ-trans {f} {g} {h} (s ⟨π⟩ f≈sg) (r ⟨π⟩ g≈rh) = let open Setoid S in record
    { shuffle = Inv._∘_ r s
    ; eq      = λ k → begin⟨ S ⟩
                f ‼ k
              ≈⟨ f≈sg k ⟩
                (s ◈ g) ‼ k
              ≈⟨ refl ⟩
                g ‼ (s ⟨$⟩ʳ k)
              ≈⟨ g≈rh (s ⟨$⟩ʳ k) ⟩
                (r ◈ h) ‼ (s ⟨$⟩ʳ k)
              ≈⟨ refl ⟩
                (s ◈ (r ◈ h)) ‼ k
              ∎
     }

  ≈ₛ-isEquivalence : IsEquivalence _≈ₛ_
  ≈ₛ-isEquivalence = record { refl = ≈ₛ-refl ; sym = ≈ₛ-sym ; trans = ≈ₛ-trans }

  BagSetoid : Setoid ℓ (c ⊔ ℓ)
  BagSetoid = record
    { Carrier         =   Seq S₀
    ; _≈_             =   _≈ₛ_
    ; isEquivalence   =   ≈ₛ-isEquivalence
    }
\end{code}
%}}}

%{{{ singleton ; singleton-cong
\begin{code}
  singleton : S₀ → Seq S₀
  singleton x = sequence 1 λ{ _ → x }

  open Setoid S using () renaming (_≈_ to _≈₀_)

  singleton-cong : {x y : S₀} → x ≈₀ y → singleton x ≈ₛ singleton y
  singleton-cong {x} {y} x≈y = record
    { shuffle = Inv.id
    ; eq      = λ _ → x≈y
    }
\end{code}
%}}}

%{{{ Permutation is equivalent to _fin≃_ (which is Fin n ≃ Fin m)
\begin{code}
  Perm⇒fin≃ : {m n : ℕ} → Permutation m n → m fin≃ n
  Perm⇒fin≃ p = _⟨$⟩_ (to p) , Equiv.qinv (_⟨$⟩_ (from p)) (right-inverse-of p) (left-inverse-of p)
    where open Inv.Inverse; open Function.Equality using (_⟨$⟩_)

  fin≃⇒Perm : {m n : ℕ} → m fin≃ n → Permutation m n
  fin≃⇒Perm (f , Equiv.qinv b α β) = record { to = P.→-to-⟶ f ; from = P.→-to-⟶ b
    ; inverse-of = record { left-inverse-of = β ; right-inverse-of = α } }

  ≡⇒≈₀ : {x y : S₀} → x P.≡ y → x ≈₀ y
  ≡⇒≈₀ P.refl = Setoid.refl S

  -- this lemma is true, but likely useless.
  fin≃⇒lookup : {m n : ℕ} → (p : m fin≃ n) → (f : Fin m → S₀) (i : Fin m) → f i ≈₀ lookup (permute (fin≃⇒Perm p) (Table.tabulate λ j → f (Equiv.isqinv.g (proj₂ p) j))) i
  fin≃⇒lookup p f i =  ≡⇒≈₀ (P.cong f (P.sym (Equiv.isqinv.β (proj₂ p) i)))
\end{code}
%}}}

%{{{ ø ; _⊕_ ; many holes
\begin{code}
  ∅ : Seq S₀
  ∅ = sequence 0 λ ()

  open import Data.Table.Base
  import Data.List as L
  open Plus -- from FinEquivPlusTimes
  open PlusE -- from FinEquivTypeEquiv

  infixr 6 _⊕_
  _⊕_ : Seq S₀ → Seq S₀ → Seq S₀
  f ⊕ g = sequence (lf + lg) λ i → [ f ‼_ , g ‼_ ]′ (proj₁ +≃⊎ i)
    where
      lf = len f
      lg = len g
\end{code}

\begin{code}

  ⊕-comm : {f g : Seq S₀} → f ⊕ g  ≈ₛ  g ⊕ f
  ⊕-comm {f} {g} = record
    { shuffle = fin≃⇒Perm (swap+ {lf} {lg})
    ; eq      = λ i → {!!}
    }
    where
      lf = len f
      lg = len g

  ⊕-assoc : {f g h : Seq S₀} → (f ⊕ g) ⊕ h  ≈ₛ  f ⊕ (g ⊕ h)
  ⊕-assoc {f} {g} {h} = record
    { shuffle = fin≃⇒Perm (assocr+ {len f} {len g} {len h})
    ; eq      = λ i → begin⟨ S ⟩
      lookup (table ((f ⊕ g) ⊕ h)) i                           ≈⟨ Setoid.refl S ⟩
      lookup (Table.tabulate (_‼_ ((f ⊕ g) ⊕ h))) i             ≈⟨ Setoid.refl S ⟩
      ((f ⊕ g) ⊕ h) ‼ i                                         ≈⟨ {!fin≃⇒lookup (assocr+ {len f}) ((f ⊕ g ⊕ h) ‼_) i!} ⟩
      (f ⊕ g ⊕ h) ‼ (proj₁ (assocr+ {len f}) i)                 ≈⟨ Setoid.refl S ⟩
      lookup (Table.tabulate (_‼_ (f ⊕ g ⊕ h))) (proj₁ (assocr+ {len f}) i)   ≈⟨ Setoid.refl S ⟩
      lookup (table (f ⊕ g ⊕ h)) (to (fin≃⇒Perm (assocr+ {len f})) Π.⟨$⟩ i) ≈⟨ Setoid.refl S ⟩
      lookup (Table.tabulate (lookup (table (f ⊕ g ⊕ h)) ∘  (to (fin≃⇒Perm (assocr+ {len f})) Π.⟨$⟩_) )) i  ≈⟨ Setoid.refl S ⟩
      lookup (permute (fin≃⇒Perm (assocr+ {len f})) (table (f ⊕ g ⊕ h))) i ∎
    }
    where open Inv.Inverse; open import Function using (_∘_)

  commutativeMonoid : CommutativeMonoid ℓ (ℓ ⊔ c)
  commutativeMonoid = record
    { Carrier               =   Seq S₀
    ; _≈_                   =   _≈ₛ_
    ; _∙_                   =   _⊕_
    ; ε                     =   ∅
    ; isCommutativeMonoid   =   record
      { isSemigroup   =   record
        { isEquivalence = ≈ₛ-isEquivalence ; assoc = λ f g h → ⊕-assoc {f} {g} {h} ; ∙-cong = {!!} }
      ; identityˡ     =   λ x → (fin≃⇒Perm unite+) ⟨π⟩ {!!}
      ; comm          =   λ f g → ⊕-comm {f} {g}
      }
    }
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
