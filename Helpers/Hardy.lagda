\section{Items from Hardy's fork of the standard library}

Material taken from Brad Hardy's variant of the standard library,
https://github.com/bch29/agda-stdlib. In particular, from his
module Algebra.Properties.CommutativeMonoid.

\begin{code}
module Helpers.Hardy where

open import Algebra using (CommutativeMonoid)
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; punchIn; zero; suc)
open import Data.Fin.Permutation as Perm using (Permutation; Permutation′; _⟨$⟩ˡ_; _⟨$⟩ʳ_)
open import Relation.Binary using (module Setoid)  
  
open import Data.Table as Table
open import Data.Table.Relation.Equality as TE using (_≗_)
  
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  
module HardyCommutativeMonoid {g₁ g₂} (M : CommutativeMonoid g₁ g₂) where

  open CommutativeMonoid M renaming
   (ε to 0#; _∙_ to _+_; ∙-cong to +-cong; identity to +-identity; assoc to +-assoc; comm to +-comm)
  open import Algebra.Operations.CommutativeMonoid M using (sumₜ)

  import Relation.Binary.EqReasoning as EqR; open EqR setoid

  module _ {n} where
    open Setoid (TE.setoid setoid n) public using () renaming (_≈_ to _≋_)
      
  -- When summing over a function from a finite set, we can pull out any value and move it to the front.
  
  sumₜ-punchIn : ∀ {n} t (i : Fin (suc n)) → sumₜ t ≈ lookup t i + sumₜ (rearrange (punchIn i) t)
  sumₜ-punchIn f zero = refl
  sumₜ-punchIn {zero} t (suc ())
  sumₜ-punchIn {suc n} t (suc i) =
    let x = head t
        y = lookup t (suc i)
        z = sumₜ (rearrange (punchIn i) (tail t))
    in begin
      x + sumₜ (tail t)  ≈⟨ +-cong refl (sumₜ-punchIn (tail t) i) ⟩
      x + (y + z)        ≈⟨ sym (+-assoc _ _ _) ⟩
      (x + y) + z        ≈⟨ +-cong (+-comm _ _) refl ⟩
      (y + x) + z        ≈⟨ +-assoc _ _ _ ⟩
      y + (x + z)        ∎
  
-- '_≈_' is a congruence over 'sumTable n'.

  sumₜ-cong : ∀ {n} {t t′ : Table Carrier n} → t ≋ t′ → sumₜ t ≈ sumₜ t′
  sumₜ-cong {zero} p = refl
  sumₜ-cong {suc n} p = +-cong (p _) (sumₜ-cong (p ∘ suc))

  -- '_≡_' is a congruence over 'sum n'.
  
  sumₜ-cong≡ : ∀ {n} {t t′ : Table Carrier n} → t ≗ t′ → sumₜ t ≡ sumₜ t′
  sumₜ-cong≡ {zero} p = ≡.refl
  sumₜ-cong≡ {suc n} p = ≡.cong₂ _+_ (p _) (sumₜ-cong≡ (p ∘ suc))

  -- Any permutation of a table has the same sum as the original.
  
  sumₜ-permute : ∀ {n} t (π : Permutation′ n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
  sumₜ-permute {zero} t π = refl
  sumₜ-permute {suc n} t π =
    let f = lookup t
        0i = zero
        ππ0 = π ⟨$⟩ʳ (π ⟨$⟩ˡ 0i)
    in begin
      sumₜ t                                                                      ≡⟨⟩
      f 0i + sumₜ (rearrange (punchIn 0i) t)                                      ≈⟨ +-cong refl (sumₜ-permute _ (Perm.remove (π ⟨$⟩ˡ 0i) π)) ⟩
      f 0i + sumₜ (rearrange (punchIn 0i ∘ (Perm.remove (π ⟨$⟩ˡ 0i) π ⟨$⟩ʳ_)) t)  ≡⟨ ≡.cong₂ _+_ ≡.refl (sumₜ-cong≡ (≡.cong f ∘ ≡.sym ∘ Perm.punchIn-permute′ π 0i)) ⟩
      f 0i + sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≡⟨ ≡.cong₂ _+_ (≡.cong f (≡.sym (Perm.inverseʳ π))) ≡.refl ⟩
      f _  + sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≈⟨ sym (sumₜ-punchIn (rearrange (π ⟨$⟩ʳ_) t) (π ⟨$⟩ˡ 0i)) ⟩
      sumₜ (rearrange (π ⟨$⟩ʳ_) t)                                                ∎
  
  -- A version of 'sumₜ-permute' allowing heterogeneous sum lengths.
  
  sumₜ-permute′ : ∀ {m n} t (π : Permutation m n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
  sumₜ-permute′ t π with Perm.↔⇒≡ π
  sumₜ-permute′ t π | ≡.refl = sumₜ-permute t π
\end{code}

∑-permute : ∀ {n} f (π : Permutation′ n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (π ⟨$⟩ʳ i)
∑-permute = sumₜ-permute ∘ tabulate

∑-permute′ : ∀ {m n} f (π : Permutation m n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (π ⟨$⟩ʳ i)
∑-permute′ = sumₜ-permute′ ∘ tabulate

-- The sum over the constantly zero function is zero.
sumₜ-zero : ∀ n → sumₜ (replicate {n} 0#) ≈ 0#

-- The '∑' operator distributes over addition.
∑-+-hom : ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i + ∑[ i < n ] g i ≈ ∑[ i < n ] (f i + g i)

-- The '∑' operator commutes with itself.
∑-comm : ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j

-- One-point rule: Summing over a pulse gives you the single value picked out by the pulse.
sumₜ-select : ∀ {n i} (t : Table Carrier n) → sumₜ (select 0# i t) ≈ lookup t i

-- Converting to a table then summing is the same as summing the original list
sumₜ-fromList : ∀ xs → sumₜ (fromList xs) ≡ sumₗ xs

-- Converting to a list then summing is the same as summing the original table
sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (toList t)

-- If addition is idempotent on a particular value 'x', then summing over any
-- arbitrary number of copies of 'x' gives back 'x'.

sumₜ-idem-replicate : ∀ n {x} → _+_ IdempotentOn x → sumₜ (Table.replicate {suc n} x) ≈ x

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
