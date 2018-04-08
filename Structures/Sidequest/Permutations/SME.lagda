\section{|Structures.Sidequest.Permutations.SME| --- Symmetric-Monoidal Expressions}

Here we consider only |𝕏| at |1|.

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.SME where

open import Level using (Level) renaming (_⊔_ to _⊍_)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

-- open import EqualityCombinators  hiding (reflexive)
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)
open import FinUtils using (Fin-complement′ ; allFin′)
open import DataProperties using (_‼_)

open import Data.Maybe
open import Data.List as List
open import Data.Vec as Vec hiding (last)
open import Data.Nat hiding (fold ; _*_)
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_ ; fold ; _≤_)
open import Data.Product using (_,_)
\end{code}
%}}}

%{{{ Free Symmetric Monoidal  -- Expressions

The semantics of these syntactical items is obtained by the |_◣_| operation below.

\begin{code}
infixr 8 _⨾_
infixr 9 _⊗_

-- A datatype for expressing how permutations are to be constructed.
data SME : ℕ → ℕ → Set where

  -- The Identity permutation on `n` elements.
  𝕀 : {n : ℕ} → SME n n

  -- Composition of permutations.
  _⨾_ : {k m n : ℕ} → SME k m → SME m n → SME k n

  -- Concurrent composition: Loosely put, | (a ⊗ b) ◣ (xs ++ ys) = (a ◣ xs) ++ (b ◣ ys)|.
  _⊗_ : {m₁ m₂ n₁ n₂ : ℕ} → SME m₁ n₁ → SME m₂ n₂ → SME (m₁ + m₂) (n₁ + n₂)

  -- Swap permutation
  𝕏 : SME 2 2
\end{code}
%}}}

%{{{ endo : {m n : ℕ} → SME m n → m ≡ n
\begin{code}
endo : {m n : ℕ} → SME m n → m ≡ n
endo 𝕀 = ≡.refl
endo (e₁ ⨾ e₂) = ≡.trans (endo e₁) (endo e₂)
endo (e₁ ⊗ e₂) = ≡.cong₂ _+_ (endo e₁) (endo e₂)
endo 𝕏 = ≡.refl
\end{code}
%}}}

%{{{ substSrc ; substTrg
\begin{code}
substSrc : {m₁ m₂ n : ℕ} → m₁ ≡ m₂ → SME m₁ n → SME m₂ n
substSrc m₁≡m₂ = ≡.subst (λ m → SME m _) m₁≡m₂

substTrg : {m n₁ n₂ : ℕ} → n₁ ≡ n₂ → SME m n₁ → SME m n₂
substTrg n₁≡n₂ = ≡.subst (SME _) n₁≡n₂
\end{code}

\edcomm{MA}{ WK, |substTgt| instead?}

%}}}

%{{{ Unit and associative laws at the SME type level
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
thenOne : {n : ℕ} → SME (n + 1) (suc n)
thenOne {n} = substTrg (+-comm _ _) 𝕀

thenOne⁻¹ : {n : ℕ} → SME (suc n) (n + 1)
thenOne⁻¹ {n} = substSrc (+-comm _ _) 𝕀
\end{code}

\begin{code}
assocR : {k m n : ℕ} → SME ((k + m) + n) (k + (m + n))
assocR {k} {m} {n} = substTrg (+-assoc k m n) 𝕀

assocL : {k m n : ℕ} → SME (k + (m + n)) ((k + m) + n)
assocL {k} {m} {n} = substSrc (+-assoc k m n) 𝕀
\end{code}
%}}}

%{{{ Adjacent Swaps: Generalizing 𝕏

Permutation |𝕏′ i| swaps the elements at locations |i| and |i+1|.

\begin{code}
𝕏′ : {n : ℕ} → Fin n → SME (suc n) (suc n)
𝕏′ {zero} ()
𝕏′ {suc n} zero = 𝕏 ⊗ 𝕀 {n}
𝕏′ {suc n} (suc i) = 𝕀 {1} ⊗ 𝕏′ i

-- Examples: The list [0,1,2,3] has the following swaps.

p1023 : 𝕏′ {3} zero ≡ 𝕏 ⊗ 𝕀 {2}
p1023 = ≡.refl

p0213 : 𝕏′ {3} (suc zero) ≡ 𝕀 {1} ⊗ (𝕏 ⊗ 𝕀 {1})
p0213 = ≡.refl

p0132 : 𝕏′ {3} (suc (suc zero)) ≡ 𝕀 {1} ⊗ 𝕀 {1} ⊗ 𝕏 ⊗ 𝕀 {0}
p0132 = ≡.refl
\end{code}

Swapping segments,
\begin{spec}
-- |𝕏″ : (m n : ℕ) → SME (m + n) (n + m)|
-- |𝕏″ m n = {!!}|

𝕏″ : (m n : ℕ) → SME (m + n) (n + m)
𝕏″ zero n       =  rightUnit⁻¹
𝕏″ (suc m) zero = rightUnit
𝕏″ (suc m) (suc n) = {!!}
\end{spec}
%}}}

%{{{ Equivalence for terms
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
%}}}

\begin{code}
module Action {ℓ c : Level} (𝒮 : Setoid c ℓ) where

  import Structures.Sidequest.Equality
  open module ≈ₖ = Structures.Sidequest.Equality 𝒮 renaming (_≈_ to _≈ₖ_)

  private
    open module ≈₀ = Setoid 𝒮 using (Carrier)
    Seq = Vec Carrier
\end{code}
Subscript 0 for ``underlying'', or `base', equality.

Interpretation of SM syntax as permutations:
\begin{code}
  _◣_ : {m n : ℕ} → SME m n → Seq m → Seq n
  𝕀 ◣ v = v
  𝕏 ◣ (x₁ ∷ x₂ ∷ []) = x₂ ∷ x₁ ∷ []
  (e₁ ⨾ e₂) ◣ v = e₂ ◣ (e₁ ◣ v)         -- \edcomm{MA}{Perhaps use “∘” or switch order of application?}
  (_⊗_ {m₁} {m₂} e₁ e₂) ◣ v with Vec.splitAt m₁ {m₂} v
  ... | v₁ , v₂ , v₁++v₂≡v = (e₁ ◣ v₁) Vec.++ (e₂ ◣ v₂)
\end{code}

%{{{ observational equality
\begin{code}
  infixr 4 _≐_

  _≐_ : {m n : ℕ} → SME m n → SME m n → Set (c ⊍ ℓ)
  p ≐ q = {xs : Seq _} → p ◣ xs  ≈ₖ   q ◣ xs

  ≐-refl : {m n : ℕ} {e : SME m n} → e ≐ e
  ≐-refl = ≈ₖ.refl _

  ≐-sym : {m n : ℕ} {e₁ e₂ : SME m n} → e₁ ≐ e₂ → e₂ ≐ e₁
  ≐-sym = λ eq → ≈ₖ.sym eq

  ≐-trans : {m n : ℕ} {e₁ e₂ e₃ : SME m n} → e₁ ≐ e₂ → e₂ ≐ e₃ → e₁ ≐ e₃
  ≐-trans eq₁ eq₂ = ≈ₖ.trans eq₁ eq₂

  ≐-leftId : {m n : ℕ} → (e : SME m n) → 𝕀 ⨾ e ≐ e
  ≐-leftId _ = ≐-refl

  ≐-rightId : {m n : ℕ} → (e : SME m n) → e ⨾ 𝕀 ≐ e
  ≐-rightId _ = ≐-refl

  ≐-⨾-assoc  : {j k m n : ℕ} (e₁ : SME j k) (e₂ : SME k m) (e₃ : SME m n)
           → (e₁ ⨾ e₂) ⨾ e₃ ≐ e₁ ⨾ (e₂ ⨾ e₃)
  ≐-⨾-assoc _ _ _ = ≐-refl

  ≐-⊗-leftId : {m n : ℕ} → (e : SME m n) → 𝕀 {0} ⊗ e ≐ e
  ≐-⊗-leftId _ = ≐-refl

  ++-rightId : {n : ℕ} {xs : Seq n} → xs Vec.++ []  ≈ₖ  xs
  ++-rightId {.0} {[]} = ≈ₖ.refl _
  ++-rightId {.(suc _)} {x ∷ xs} = ≈₀.refl ∷-cong ++-rightId

  -- |≐-⊗-rightId : {m n : ℕ} → (e : SME m n) → (e ⊗ 𝕀 {0}) ⨾ rightUnit ≐ rightUnit ⨾ e|
  -- |≐-⊗-rightId {m} {n} e {v} with +-right-identity m | endo e | Vec.splitAt m v|
  -- |≐-⊗-rightId {m} {.m} e {.(v₁ Vec.++ [])} | ff | ≡.refl | v₁ , [] , ≡.refl = {!!}| 
\end{code}
%}}}

%{{{ A tracing version of permutation application, along with |sink| and |float|

A ``tracing'' version:
\begin{code}
  _◺_ : {n : ℕ} → List (Fin n) → Seq (suc n) → List (Seq (suc n))
  [] ◺ v = List.[]
  (i ∷ is)  ◺ v = let v′ = 𝕏′ i ◣ v in v′ ∷ (is ◺ v′)

  -- Push the head element “downwards”, to the right, i-many times  
  sink : {n : ℕ} (i : Fin n) → SME n n
  sink {suc n} zero = 𝕀
  sink {suc n} (suc i) = (thenOne⁻¹ ⨾ (sink i ⊗ 𝕀 {1}) ⨾ thenOne) ⨾ 𝕏′ i  -- push right then a swap
                                                                                                                                         -- c.f., |head-is-last-◣| below.
  -- Move i-Th element to be new head element.
  float : {n : ℕ} (i : Fin n) → SME n n
  float {suc n} zero = 𝕀
  float {suc n} (suc i) = 𝕏′ i  ⨾ (thenOne⁻¹ ⨾ (float i ⊗ 𝕀 {1}) ⨾ thenOne)  -- c.f., |last-is-head-◣| below.

  -- Since 𝕏′ is a linear time algorithm that is invoked a linear amount of times in each of the above
  -- algorithms, they are necessarily quadratic time.  Below |drown| is also quadratic as the sum of quadratics.

  -- Move i-th element to be the the last element.
  drown : {n : ℕ} (i : Fin n) → SME n n
  drown {suc n} zero    = sink (fromℕ n) -- sink (raise 1 (fromℕ n))
  drown {suc n} (suc i) = float (suc i) ⨾ sink (fromℕ n) -- float (suc (suc i)) ⨾ sink (raise 1 (fromℕ n))

  -- Rotation: “Pull” on a sequence |[x₀, …, xₖ]| holding at |xᵢ|, leftwards and circling around, to obtain
  -- sequence |[xᵢ₊₁, …, xₖ, x₀, …, xᵢ]|. That is, rotate the sequence so that the |i|-th element is now last.
  𝓡  : {n : ℕ} (i : Fin n) → SME n n
  𝓡 zero     =  drown zero
  𝓡 (suc i)  = drown (suc i) ⨾ (thenOne⁻¹ ⨾ (𝓡 i ⊗ 𝕀 {1}) ⨾ thenOne)  -- c.f., |rotate-test| below.
  --
  -- Super slow function: We perform a quadractic call a linear number of times, totalling cubic time.

  -- Rotation: “Pull” on a sequence |[x₀, …, xₖ]| holding at |xᵢ|, rightwards and circling around, to obtain
  -- sequence |[xᵢ, …, xₖ, x₀, …, xᵢ₋₁]|. That is, rotate the sequence so that the |i|-th element is now first.
  -- |𝓡⁻¹  : {n : ℕ} (i : Fin n) → SME n n|
  -- |𝓡⁻¹ zero     =  float zero|
  -- |𝓡⁻¹ (suc i)  = (thenOne⁻¹ ⨾ (𝓡⁻¹ i ⊗ 𝕀 {1}) ⨾ thenOne) ⨾ float (suc i)  -- c.f., |rotate-test| below.|

  -- \edcomm{MA}{To consider.}
  -- Drowning the last element leaves the list unchanged.
  -- |Reverse = drown n ⨾ drown (n-1) ⨾ ⋯ ⨾ down 0|.
  -- Rotating n, i.e., 1 less the length, leaves the list unchanged.
  
  module Tests₀ (e₀ e₁ e₂ e₃ : Carrier) where

    drown-test-0 : drown zero ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₁ ∷ e₂ ∷ e₃ ∷ e₀ ∷ []
    drown-test-0 = ≡.refl

    drown-test-1 : drown (suc zero) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₀ ∷ e₂ ∷ e₃ ∷ e₁ ∷ []
    drown-test-1 = ≡.refl

    drown-test-2 : drown (suc (suc zero)) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₀ ∷ e₁ ∷ e₃ ∷ e₂ ∷ []
    drown-test-2 = ≡.refl

    drown-test-3 : drown (suc (suc (suc zero))) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []
    drown-test-3 = ≡.refl

    rotate-test :   (drown (suc (suc zero))
                           ⨾ drown {3} (suc zero) ⊗ (𝕀 {1})
                           ⨾ drown {2} zero ⊗ 𝕀 {2}) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])
                       ≡ e₃ ∷ e₀ ∷ e₁ ∷ e₂ ∷ []
    rotate-test = ≡.refl

    𝓡-test-3 :  𝓡 (suc (suc (suc zero))) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []
    𝓡-test-3 = ≡.refl

    𝓡-test-2 :  𝓡 (suc (suc zero)) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₃ ∷ e₀ ∷ e₁ ∷ e₂ ∷ [] -- c.f.. |rotate-test| above :-)
    𝓡-test-2 = ≡.refl

    𝓡-test-1 :  𝓡 (suc zero) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₂ ∷ e₃ ∷ e₀ ∷ e₁ ∷ []
    𝓡-test-1 = ≡.refl

    𝓡-test-0 :  𝓡 zero ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ e₁ ∷ e₂ ∷ e₃ ∷ e₀ ∷ []
    𝓡-test-0 = ≡.refl

    -- |𝓡⁻¹-test-3 :  𝓡⁻¹ (suc (suc (suc zero))) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) ≡ {!𝓡⁻¹ (suc (suc (suc zero))) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])!}|
    -- |𝓡⁻¹-test-3 = ≡.refl|

    -- c.f., |p0132| above.
    p0132-◺ : (( suc {2} (suc zero) ∷ suc zero ∷ zero ∷ []) ◺ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []))
                  ≡ (e₀ ∷ e₁ ∷ e₃ ∷ e₂ ∷ [])          -- result of applying takes [0,1,3,2]  to (e₀ e₁ e₂ e₃)  -- |≈ 𝕏′ 3|
                  ∷  (e₀ ∷ e₃ ∷ e₁ ∷ e₂ ∷ [])         -- *then* applying    takes  [0,2,1,3] to that,             -- |≈ 𝕏′ 1|
                  ∷  (e₃ ∷ e₀ ∷ e₁ ∷ e₂ ∷ []) ∷ []  -- *then* applying    takes  [1,0,2,3] to that.              -- |≈ 𝕏′ 0|
    p0132-◺ = ≡.refl

    swap-1-3 : ((suc (suc zero) ∷ suc zero ∷ suc (suc zero) ∷ []) ◺ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []))
               ≡    -- (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])          -- no swap 
                      (e₀ ∷ e₁ ∷ e₃ ∷ e₂ ∷ [])            -- swap indices 2-3
                  ∷  (e₀ ∷ e₃ ∷ e₁ ∷ e₂ ∷ [])            -- swap indices 1-2
                  ∷  (e₀ ∷ e₃ ∷ e₂ ∷ e₁ ∷ []) ∷ []     -- swap indices 2-3
    swap-1-3 = ≡.refl

    hd = e₀

    head-is-last-◣ : ((𝕏′ zero ⨾ 𝕏′ (suc zero)) ⨾ 𝕏′ (suc (suc zero))) ◣ (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])
                       ≡ (e₁ ∷ e₂ ∷ e₃ ∷ hd ∷ [])
    head-is-last-◣ = ≡.refl

    head-is-last-sink : sink (suc (suc (suc zero))) ◣ (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  (e₁ ∷ e₂ ∷ e₃ ∷ hd ∷ [])
    head-is-last-sink = ≡.refl

    head-is-third-sink : sink (suc (suc zero)) ◣ (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  (e₁ ∷ e₂ ∷ hd ∷ e₃ ∷ [])
    head-is-third-sink = ≡.refl

    head-is-second-sink : sink (suc zero) ◣ (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  (e₁ ∷ hd ∷ e₂ ∷ e₃ ∷ [])
    head-is-second-sink = ≡.refl

    head-is-first-sink : sink zero ◣ (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  (hd ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])
    head-is-first-sink = ≡.refl

    last = e₃

    last-is-head-◣ : (𝕏′ (suc (suc zero)) ⨾ 𝕏′ (suc zero) ⨾ 𝕏′ zero) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ last ∷ [])
                       ≡ (last ∷ e₀ ∷ e₁ ∷ e₂ ∷ [])
    last-is-head-◣ = ≡.refl

    last-is-head-float : float (suc (suc (suc zero))) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ last ∷ [])  ≡  (last ∷ e₀ ∷ e₁ ∷ e₂ ∷ [])
    last-is-head-float = ≡.refl

    two-is-head-float : float (suc (suc zero)) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  e₂ ∷ e₀ ∷ e₁ ∷ e₃ ∷ []
    two-is-head-float = ≡.refl

    one-is-head-float : float (suc zero) ◣ (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])  ≡  e₁ ∷ e₀ ∷ e₂ ∷ e₃ ∷ []
    one-is-head-float = ≡.refl

    head-is-head-float : float zero ◣ (e₀ ∷ e₁ ∷ e₂ ∷ last ∷ [])  ≡  (e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ [])
    head-is-head-float = ≡.refl  

  {-
        Given [⋯, xᵢ, ⋯, xⱼ, ⋯].
        Leave the first and last segements unalted via |𝕀 {i-1} ⊗ ⁉ ⊗ 𝕀 {n-j} |.
        Then `⁉` may be to `sink` xᵢ beside xⱼ, then swap, then `float` xⱼ. 
        Now may have [⋯, xⱼ, ⋯, xᵢ, ⋯] ?
   -}
   
  -- |𝓧 : {n : ℕ} (i j : Fin n) → SME n n|
  -- |𝓧 {suc n} zero j = {!(float j ⨾ ?)!} ⊗ 𝕀|   -- Indexitis.
  -- |𝓧 {suc n} (suc i) j = {!!}|
\end{code}
%}}}

%{{{ A direct approach to permutation combinators

We formed a syntax for permutations *then* gave it a semantics.

The idea of transforming a number into its associated permutation --e.g., factorids--
can be done directly:

\begin{code}
  FinSeqOp : ℕ → Set c
  FinSeqOp n = Fin n → Seq (suc n) → Seq (suc n)
\end{code}

 Swapping as a function: |i 𝕩 v| is obtained by swapping the |i| and |i|-th elements of |v|.
\begin{code}
  _𝕩_ : {n : ℕ} → FinSeqOp n
  zero 𝕩 (x₁ ∷ x₂ ∷ xs) = x₂ ∷ x₁ ∷ xs
  (suc i) 𝕩 (x₁ ∷ xs) = x₁ ∷ (i 𝕩 xs)

  𝕩-spec : {n : ℕ} {i : Fin n} {v : Seq (suc n)} → i 𝕩 v  ≡  𝕏′ i ◣ v
  𝕩-spec {.(suc _)} {zero} {x ∷ x₁ ∷ v} = ≡.refl
  𝕩-spec {.(suc _)} {suc i} {x ∷ x₁ ∷ v} = ≡.cong (x ∷_) 𝕩-spec
\end{code}

|i 𝕪 v ≡ (𝕏″ 1 (suc i) ⊗ 𝕀) ◣ v|
\begin{code}
  _𝕪_ : {n : ℕ} → FinSeqOp n
  _𝕪_ {n} i (x₁ ∷ xs) with Vec.splitAt (suc (toℕ i)) {n ∸ suc (toℕ i)}
                         (≡.subst (Vec _) (≡.sym (Fin-complement′ i)) xs)
  ... | xs₁ , xs₂ , xs₁++xs₂≡xs  = ≡.subst (Vec _) eq (xs₁ Vec.++ x₁ ∷ xs₂)
    where
      eq = ≡.trans (+-suc (suc (toℕ i)) (n ∸ suc (toℕ i))) (≡.cong suc (Fin-complement′ i))

  module Tests (e₀ e₁ e₂ e₃ : Carrier) where

    𝕪0 : (zero 𝕪 ((e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []))) ≡ (e₁ ∷ e₀ ∷ e₂ ∷ e₃ ∷ [])
    𝕪0 = ≡.refl

    𝕪1 : (suc zero 𝕪 ((e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []))) ≡ e₁ ∷ e₂ ∷ e₀ ∷ e₃ ∷ []
    𝕪1 = ≡.refl

    𝕪2 : (suc (suc zero) 𝕪 ((e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []))) ≡ e₁ ∷ e₂ ∷ e₃ ∷ e₀ ∷ []
    𝕪2 = ≡.refl

    𝕪-is-sink-example : {i : Fin 3} (let v = e₀ ∷ e₁ ∷ e₂ ∷ e₃ ∷ []) → i 𝕪 v  ≡  sink (suc i) ◣ v
    𝕪-is-sink-example {zero}                         =   ≡.refl
    𝕪-is-sink-example {suc zero}                  =   ≡.refl
    𝕪-is-sink-example {suc (suc zero)}        =   ≡.refl
    𝕪-is-sink-example {suc (suc (suc ()))}

  -- |𝕪-is-sink : {n : ℕ} {i : Fin n} {v : Seq (suc n)} → i 𝕪 v  ≡  sink (suc i) ◣ v|
  -- |𝕪-is-sink {.1} {zero} {x ∷ x₁ ∷ []} = ≡.refl|
  -- |𝕪-is-sink {.(suc (suc _))} {zero} {x ∷ x₁ ∷ x₂ ∷ v} = {!!}|
  -- |𝕪-is-sink {.(suc _)} {suc i} {v} = {!!}|
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
%}}}

%{{{ Soundness and Completeness

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
