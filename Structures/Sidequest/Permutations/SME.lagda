\section{|Structures.Sidequest.Permutations.SME| --- Symmetric-Monoidal Expressions}

Here we consider only |𝕏| at |1|.

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.SME where

open import Level using (Level)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

-- open import EqualityCombinators  hiding (reflexive)
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)
open import FinUtils using (Fin-complement′ ; allFin′)
open import DataProperties using (_‼_)

open import Data.Maybe
open import Data.List as List
open import Data.Vec as Vec
open import Data.Nat hiding (fold ; _*_)
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_ ; fold ; _≤_)
open import Data.Product using (_,_)
\end{code}



\begin{code}
infixr 8 _⨾_
infixr 9 _⊗_
data SME : ℕ → ℕ → Set where
  𝕀 : {n : ℕ} → SME n n
  _⨾_ : {k m n : ℕ} → SME k m → SME m n → SME k n
  _⊗_ : {m₁ m₂ n₁ n₂ : ℕ} → SME m₁ n₁ → SME m₂ n₂ → SME (m₁ + m₂) (n₁ + n₂)
  𝕏 : SME 2 2
\end{code}

\begin{code}
endo : {m n : ℕ} → SME m n → m ≡ n
endo 𝕀 = ≡.refl
endo (e₁ ⨾ e₂) = ≡.trans (endo e₁) (endo e₂)
endo (e₁ ⊗ e₂) = ≡.cong₂ _+_ (endo e₁) (endo e₂)
endo 𝕏 = ≡.refl
\end{code}

\begin{code}
substSrc : {m₁ m₂ n : ℕ} → m₁ ≡ m₂ → SME m₁ n → SME m₂ n
substSrc m₁≡m₂ = ≡.subst (λ m → SME m _) m₁≡m₂

substTrg : {m n₁ n₂ : ℕ} → n₁ ≡ n₂ → SME m n₁ → SME m n₂
substTrg n₁≡n₂ = ≡.subst (SME _) n₁≡n₂
\end{code}

\begin{code}
leftUnit : {n : ℕ} → SME (0 + n) n
leftUnit = 𝕀

leftUnit⁻¹ : {n : ℕ} → SME n (0 + n)
leftUnit⁻¹ = 𝕀
\end{code}

\begin{code}
rightUnit : {n : ℕ} → SME (n + 0) n
rightUnit {n} = substTrg (+-right-identity n) 𝕀

rightUnit⁻¹ : {n : ℕ} → SME n (n + 0)
rightUnit⁻¹ {n} = substSrc (+-right-identity n) 𝕀
\end{code}

\begin{code}
assocR : {k m n : ℕ} → SME ((k + m) + n) (k + (m + n))
assocR {k} {m} {n} = substTrg (+-assoc k m n) 𝕀

assocL : {k m n : ℕ} → SME (k + (m + n)) ((k + m) + n)
assocL {k} {m} {n} = substSrc (+-assoc k m n) 𝕀
\end{code}

\begin{code}
𝕏′ : {n : ℕ} → Fin n → SME (suc n) (suc n)
𝕏′ {zero} ()
𝕏′ {suc n} zero = 𝕏 ⊗ 𝕀 {n}
𝕏′ {suc n} (suc i) = 𝕀 {1} ⊗ 𝕏′ i
\end{code}

\begin{code}
-- |𝕏″ : (m n : ℕ) → SME (m + n) (n + m)|
-- |𝕏″ m n = {!!}|
\end{code}

\begin{code}
infixr 5 _≋_
data _≋_ : {m n : ℕ} → SME m n → SME m n → Set where
  refl : {m n : ℕ} {e : SME m n} → e ≋ e
  sym : {m n : ℕ} {e₁ e₂ : SME m n} → e₁ ≋ e₂ → e₂ ≋ e₁
  trans : {m n : ℕ} {e₁ e₂ e₃ : SME m n} → e₁ ≋ e₂ → e₂ ≋ e₃ → e₁ ≋ e₃
  leftId : {m n : ℕ} → (e : SME m n) → 𝕀 ⨾ e ≋ e
  rightId : {m n : ℕ} → (e : SME m n) → e ⨾ 𝕀 ≋ e
  ⨾-assoc  : {j k m n : ℕ} (e₁ : SME j k) (e₂ : SME k m) (e₃ : SME m n)
           → (e₁ ⨾ e₂) ⨾ e₃ ≋ e₁ ⨾ (e₂ ⨾ e₃)
  ⊗-leftId : {m n : ℕ} → (e : SME m n) → 𝕀 {0} ⊗ e ≋ e
  ⊗-rightId : {m n : ℕ} → (e : SME m n) → (e ⊗ 𝕀 {0}) ⨾ rightUnit ≋ rightUnit ⨾ e
  ⊗-assocR  : {m₁ m₂ m₃ n₁ n₂ n₃ : ℕ} (e₁ : SME m₁ n₁) (e₂ : SME m₂ n₂) (e₃ : SME m₃ n₃)
            → ((e₁ ⊗ e₂) ⊗ e₃) ⨾ assocR {n₁} {n₂} {n₃} ≋ assocR {m₁} {m₂} {m₃} ⨾ (e₁ ⊗ (e₂ ⊗ e₃))
  -- \unfinished
  -- \edcomm{WK}{All sym-mon-cat axioms needed here, except for those holding definitionally.}
\end{code}



\begin{code}
module Action {ℓ c : Level} (𝒮 : Setoid c ℓ) where

  open import Structures.Sidequest.Equality 𝒮 renaming (_≈_ to _≈ₖ_)

  private
    open module ≈₀ = Setoid 𝒮 using (Carrier)
    Seq = Vec Carrier
\end{code}
Subscript 0 for ``underlying'', or `base', equality.

\begin{code}
  _◣_ : {m n : ℕ} → SME m n → Seq m → Seq n
  𝕀 ◣ v = v
  𝕏 ◣ (x₁ ∷ x₂ ∷ []) = x₂ ∷ x₁ ∷ []
  (e₁ ⨾ e₂) ◣ v = e₂ ◣ (e₁ ◣ v)
  (_⊗_ {m₁} {m₂} e₁ e₂) ◣ v with Vec.splitAt m₁ {m₂} v
  ... | v₁ , v₂ , v₁++v₂≡v = (e₁ ◣ v₁) Vec.++ (e₂ ◣ v₂)
\end{code}

A ``tracing'' version:
\begin{spec}
  _◺_ : {n : ℕ} → List (Fin n) → Seq (suc n) → List (Seq (suc n))
  [] ◺ v = List.[]
  (i ∷ is)  ◺ v = let v′ = 𝕏′ i ◣ v in v′ ∷ (is ◺ v′)
\end{spec}

\begin{code}
  FinSeqOp : ℕ → Set c
  FinSeqOp n = Fin n → Seq (suc n) → Seq (suc n)
\end{code}

|i 𝕩 v ≡ 𝕏′ i ◣ v|
\begin{code}
  _𝕩_ : {n : ℕ} → FinSeqOp n
  zero 𝕩 (x₁ ∷ x₂ ∷ xs) = x₂ ∷ x₁ ∷ xs
  (suc i) 𝕩 (x₁ ∷ xs) = x₁ ∷ (i 𝕩 xs)
\end{code}

|i 𝕪 v ≡ (𝕏″ 1 (suc i) ⊗ 𝕀) ◣ v|
\begin{code}
  _𝕪_ : {n : ℕ} → FinSeqOp n
  _𝕪_ {n} i (x₁ ∷ xs) with Vec.splitAt (suc (toℕ i)) {n ∸ suc (toℕ i)}
                         (≡.subst (Vec _) (≡.sym (Fin-complement′ i)) xs)
  ... | xs₁ , xs₂ , xs₁++xs₂≡xs  = ≡.subst (Vec _) eq (xs₁ Vec.++ x₁ ∷ xs₂)
    where
      eq = ≡.trans (+-suc (suc (toℕ i)) (n ∸ suc (toℕ i))) (≡.cong suc (Fin-complement′ i))
\end{code}


|_𝕫_ i ≡ _𝕪_ i ∘ _𝕪_ (i - 1) ∘ ⋯ ∘  _𝕪_ 1 ∘ _𝕪_ zero|
\begin{code}
  _𝕫_ : {n : ℕ} → FinSeqOp n
  _𝕫_ {n} i = _𝕪_ {n} i ∘₀ λ v → List.foldr _𝕪_ v (List.reverse (allFin′ i))
\end{code}

A faster |_◺_|, based on arbitrary |FinSeqOp|:
\begin{code}
  execFinList : {n : ℕ} → FinSeqOp n → List (Fin n) → Seq (suc n) → List (Seq (suc n))
  execFinList fsOp [] v = List.[]
  execFinList fsOp (i ∷ is) v = let v′ = fsOp i v in v′ ∷ (execFinList fsOp is v′)
\end{code}

Soundness of |_≋_| with respect to the |_◣_| semantics:
\begin{spec}
  ◣-cong₁ : {m n : ℕ} {e₁ e₂ : SME m n} {v : Seq m} → e₁ ≋ e₂ → (e₁ ◣ v) ≈ₖ (e₂ ◣ v)
  ◣-cong₁ eq = {! {- \unfinished -}!}
\end{spec}
Completeness will probably need essentially the coherence argument
for symmetric monoidal categories. \unfinished
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
