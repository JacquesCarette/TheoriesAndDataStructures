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
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation
open import Data.Table.Relation.Equality using (setoid)
open import Data.Product using (Σ; _,_; _×_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.SetoidReasoning
open import Function.Equality using (module Π)
import Function.Inverse as Inv using (module Inverse)
open import Function.Inverse using (_↔_)
open import Algebra   using (CommutativeMonoid)

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

-- module _ {ℓ c : Level} (S : Setoid ℓ c) where
--   _≈ₜ_ : (f g : Seq (Setoid.Carrier S)) → Set c
--   f ≈ₜ g = let open Setoid (setoid S (len f)) in table f ≈ {!table g!}
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

%{{{ ø ; _⊕_ ; many holes
\begin{code}
  ∅ : Seq S₀
  ∅ = sequence 0 λ ()

  open import Data.Table.Base
  import Data.List as L

  infixr 6 _⊕_
  _⊕_ : Seq S₀ → Seq S₀ → Seq S₀
  f ⊕ g = table˘ (fromList (toList (table f) L.++ toList (table g)))
\end{code}

\begin{spec}

  -- MA: The following are essentially the ``identity'' isomorphisms +-identity, +-commutativity, and +-associtivity?

  ⊕-comm : {f g : Seq S₀} → f ⊕ g  ≈ₛ  g ⊕ f
  ⊕-comm {f} {g} = record
    { shuffle = record
      { to         = record { _⟨$⟩_ = λ x → {!!} ; cong = {!!} }
      ; from       = {!!}
      ; inverse-of = {!!}
      }
    ; eq      = {!!}
    }
    where

      open import Data.Nat

      len-homo : len (f ⊕ g) P.≡ len f + len g
      len-homo with L.tabulate (_‼_ f) | L.tabulate (_‼_ g)
      len-homo | L.[] | L.[] = {!!}
      len-homo | L.[] | x L.∷ q = {!!}
      len-homo | x L.∷ p | q = {!!}

      +-comm : Fin (len (f ⊕ g)) → Fin (len (g ⊕ f))
      +-comm x = {!!}

  ⊕-assoc : {f g h : Seq S₀} → (f ⊕ g) ⊕ h  ≈ₛ  f ⊕ (g ⊕ h)
  ⊕-assoc {f} {g} {h} = record
    { shuffle = {!!}
    ; eq      = {!!}
    }
  
  commutativeMonoid : CommutativeMonoid ℓ (ℓ ⊔ c)
  commutativeMonoid = record
    { Carrier               =   Seq S₀
    ; _≈_                   =   _≈ₛ_
    ; _∙_                   =   _⊕_
    ; ε                     =   ∅
    ; isCommutativeMonoid   =   record
      { isSemigroup   =   record
        { isEquivalence = ≈ₛ-isEquivalence ; assoc = λ f g h → ⊕-assoc {f} {g} {h} ; ∙-cong = {!!} }
      ; identityˡ     =   λ x → {!!}
      ; comm          =   λ f g → ⊕-comm {f} {g}
      }
    }
\end{spec}

\begin{code}
  postulate
    commutativeMonoid : CommutativeMonoid ℓ (ℓ ⊔ c)
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
