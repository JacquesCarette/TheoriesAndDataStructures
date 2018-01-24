\section{Structures.Sidequest}

%{{{ Imports
\begin{code}
module Structures.Sidequest where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; _∘_)
open import Function using () renaming (id to Id₀ ; _∘_ to _∘₀_)

open import DataProperties hiding (⟨_,_⟩)
open import ParComp
open import EqualityCombinators
open import Belongs
open import Structures.CommMonoid renaming (Hom to CMArrow)

open import Data.Nat.Properties using (≤-steps ; n≤1+n ; n∸n≡0)

open import Data.List using (monoid)
open import Data.Fin using (fromℕ)

open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
-- open CommMonoid using (eq-in ; isCommMonoid)
\end{code}
%}}}


%{{{ VecEquality
\begin{code}
module VecEquality {ℓ c : Level} (𝒮 : Setoid c ℓ) where

  open import Data.Vec
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold ; _≤_)

  -- Sequences
  open Setoid 𝒮
  module ≈ = Setoid 𝒮
  Seq = Vec Carrier

  -- `k`omponent-wise equality on sequences ;; MA: Subscript `c` not directly available.
  infix 5 _≈ₖ_  
  data _≈ₖ_ : {n : ℕ} → Seq n → Seq n → Set (c ⊍ ℓ) where
    nil  : [] ≈ₖ []
    cons : {x y : Carrier} {n : ℕ} {xs ys : Seq n} (x≈y : x ≈ y) (xs≈ys : xs ≈ₖ ys) → (x ∷ xs) ≈ₖ (y ∷ ys)
\end{code}

It is a simple matter to show that this is an equivalence relation.
\begin{code}
  ≈ₖ-refl : {n : ℕ} {xs : Seq n} → xs ≈ₖ xs
  ≈ₖ-refl {xs = []    } = nil
  ≈ₖ-refl {xs = y ∷ ys} = cons ≈.refl ≈ₖ-refl

  ≈ₖ-sym : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → ys ≈ₖ xs
  ≈ₖ-sym nil = nil
  ≈ₖ-sym (cons x≈y xs≈ys) = cons (≈.sym x≈y) (≈ₖ-sym xs≈ys)

  ≈ₖ-trans : {n : ℕ} {xs ys zs : Seq n} → xs ≈ₖ ys → ys ≈ₖ zs → xs ≈ₖ zs
  ≈ₖ-trans nil nil = nil
  ≈ₖ-trans (cons x≈y xs≈ys) (cons y≈z ys≈zs) = cons (≈.trans x≈y y≈z) (≈ₖ-trans xs≈ys ys≈zs)
\end{code}
%}}}

%{{{ Permutations
\begin{code}
module Permutations {ℓ c : Level} (𝒮 : Setoid c ℓ)
  where

  open VecEquality 𝒮
  open Setoid 𝒮
  open import Data.Vec
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold ; _≤_)  
\end{code}

  %{{{ Permutations datatype, insert, permute ◈ 
\begin{code}
  data Permutation : ℕ → Set where
    nil  : Permutation 0
    cons : {n : ℕ} → (p : Fin (suc n)) → (ps : Permutation n) → Permutation (suc n)

  -- What exactly are the semantics of these things?
  -- Insertions!
  -- See the |permute| operation below.

  -- |insert xs i x ≈ xs[1…i-1] ++ [x] ++ xs[i … len xs]|
  -- ( Note that this is different from |Data.Vec._[_]≔_| which updates a positional element. )
  insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
  insert xs zero a = a ∷ xs
  insert [] (suc ()) a
  insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

  -- Given a permutation, apply it to a vector.
  infix 6 _◈_
  _◈_ : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
  nil         ◈ []       = []
  (cons p ps) ◈ (x ∷ xs) = insert (ps ◈ xs) p x

  _ℕ∷_ : (n : ℕ) (ps : Permutation n) → Permutation (suc n)
  _ℕ∷_ = λ n ps → cons (fromℕ n) ps
\end{code}
%}}}
  %{{{ Example permutations: Reverse and Identity

\begin{code}
  rotate : {n : ℕ} (i : ℕ) → Permutation (i + n)
  rotate {zero}  zero    = nil
  rotate {suc n} zero    = cons zero (rotate 0)
  rotate {n}     (suc i) = cons (fromℕ (i + n)) (rotate i)

  test₀ : rotate 0 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test₀ = ≡.refl

  test₁ : rotate 1 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (2 ∷ 3 ∷ 4 ∷ 5 ∷ 1 ∷ [])
  test₁ = ≡.refl

  test₂ : rotate 2 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 ∷ 4 ∷ 5 ∷ 2 ∷ 1 ∷ [])
  test₂ = ≡.refl

  test₃ : rotate 3 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (4 ∷ 5 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₃ = ≡.refl

  test₄ : rotate 4 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₄ = ≡.refl

  test₅ : rotate 5 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₅ = ≡.refl

  Id : {n : ℕ} → Permutation n
  Id = rotate 0
  -- I.e., insertions at position 0 only; since 0 rotations needed.  

  -- rev {n} = rotate n {0} -- we need to use subst to obtain |n + 0 ≡ n|
  -- A direct implementation is then clearer.
  rev : {n : ℕ} → Permutation n
  rev {zero}  = nil
  rev {suc n} = n ℕ∷ rev
\end{code}

\end{code}

%{{{ Attempt at automatically generating coherency proofs

\begin{code}
{-
  Also considered,

  -- rotate : {n : ℕ} (i : Fin n) → Permutation (toℕ i + n) 
  -- rotate {suc zero} zero    = cons zero nil
  -- rotate {suc (suc n)} zero = cons zero (rotate zero)
  -- rotate {suc n} (suc i) = cons (fromℕ (toℕ i + suc n)) (subst Permutation {!!} (rotate (inject₁ i)))
-}  

  rotate₋₁ : (n : ℕ) (i : ℕ){{coh : i ≤ n}} → Permutation (i + n)
  rotate₋₁ zero .0 {{z≤n}} = nil
  rotate₋₁ (suc n) .0 {{z≤n}} = cons zero (rotate₋₁ n 0 {{z≤n}})
  rotate₋₁ (suc n) .(suc i) {{s≤s {i} coh}} = cons (fromℕ (i + suc n)) (rotate₋₁ (suc n) i {{≤-steps 1 coh}})

  test₋₁ : rotate₋₁ 5 0 {{ z≤n }} ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test₋₁ = ≡.refl

  -- ToDo: Consider adding this import into the personal umbrella file |DataProperties|.
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  proveLeq : {m n : ℕ} {pf : True (m Data.Nat.≤? n) } → m ≤ n
  proveLeq {m} {n} {pf} = toWitness {Q = m Data.Nat.≤? n} pf

  9≤10 : 9 ≤ 10
  9≤10 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) -- auto

  99≤100 : 99 ≤ 100  -- remove final 0 to see err msg
  99≤100 = proveLeq                                       -- succinct.

  open import Data.Unit using (tt)

  -- rotate₁ : {n : ℕ} {i : ℕ} → Permutation (i + n)
  -- rotate₁ {n} {i} = rotate₋₁ n i {{ proveLeq {i} {n} {{! Agda, why hath thou forsaken me!}} }}
\end{code}

%}}}

%}}}

The following is inspired by copumkin & vmchale's libraries.

  %{{{ Relationship between Vec and Permutation
\begin{code}
  -- Notice that |Permutation n| is similar to, but distinct from, |Vec (Fin (suck n)) n|.
  -- More accurately, as in the traditional sense of the concept,
  -- |Permutation n ≅ (Π i : 0..n-1 • Fin (n ∸ i))|; cf |_at_| below.
  toVec : {n : ℕ} → Permutation n → Vec ℕ n
  toVec nil         = []
  toVec (cons p ps) = toℕ p ∷ toVec ps

  -- ToDo: Consider forming inverse of toVec.

  infixr 6 _at_ _at′_

  _at_ : {n : ℕ} → Permutation n → (i : Fin n) → Fin (n ∸ toℕ i)
  cons p ps at zero   =  p
  cons p ps at suc i  =  ps at i

  at-spec : {n : ℕ} {ps : Permutation n} {i : Fin n} → toℕ (ps at i)  ≡  lookup i (toVec ps)
  at-spec {.(suc _)} {cons p ps} {zero}  =  ≡.refl
  at-spec {.(suc _)} {cons p ps} {suc i} =  at-spec {ps = ps}

  open import Data.Fin.Properties using (inject≤-lemma ; to-from ; toℕ-injective)

  _at′_ : {n : ℕ} → Permutation n → Fin n → Fin n
  cons p p₁ at′ zero = p
  cons p p₁ at′ suc i = inject≤ (p₁ at′ i) (n≤1+n _)

  at′-spec : {n : ℕ} {ps : Permutation n} {i : Fin n} → toℕ (ps at′ i)  ≡ lookup i (toVec ps)
  at′-spec {.(suc _)} {cons p ps} {zero} = ≡.refl
  at′-spec {.(suc n)} {cons {n} p ps} {suc i}
    rewrite inject≤-lemma (ps at′ i) (n≤1+n n) = at′-spec {ps = ps}

  -- It is easier to prove certain results with |_at_| rather than |_at′_| due to the
  -- pesky injection. This combinator will hopefully alleviate some troubles.
  -- See |rev-end′| for example usage.
  at-at′ : {n : ℕ} {ps : Permutation n} {i : Fin n} → toℕ (ps at i) ≡  toℕ (ps at′ i)
  at-at′ {.(suc _)} {cons p ps} {zero} = ≡.refl
  at-at′ {.(suc n)} {cons p ps} {suc {n} i}
    rewrite inject≤-lemma (ps at′ i) (n≤1+n n) =  at-at′ {n} {i = i}

  test-Id : toVec (Id {5}) ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  test-Id = ≡.refl

  Id-spec : {n : ℕ} {j : Fin (suc n)} → toℕ (Id {suc n} at j)  ≡  0
  Id-spec {n} {zero} = ≡.refl
  Id-spec {zero} {suc ()}
  Id-spec {suc n} {suc j} = Id-spec {n} {j}

  rev-spec : {n : ℕ} {i : Fin n} → (toℕ (rev {n} at i)) ≡ n ∸ toℕ (suc i)
  rev-spec {.(suc n)} {zero {n}} = to-from n
  rev-spec {.(suc n)} {suc {n} i} = rev-spec {n} {i}

  test-rev : toVec (rev {5}) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
  test-rev = ≡.refl

  rev-end : {n : ℕ} → toℕ (rev {suc n} at fromℕ n) ≡ 0
  rev-end {n} = rev-spec {suc n} {fromℕ n} ⟨≡≡⟩ n-𝓃=0
    where n-𝓃=0 : n ∸ toℕ (fromℕ n) ≡ 0
          n-𝓃=0 rewrite to-from n = n∸n≡0 n

  rev-start′ : {n : ℕ} → (rev {suc n} at′ zero) ≡ fromℕ n
  rev-start′ {n} = ≡.refl

  rev-end′ :  {n : ℕ} → rev {suc n} at′ fromℕ n ≡ zero
  rev-end′ {n} = toℕ-injective (≡.sym at-at′ ⟨≡≡⟩ rev-end)
\end{code}
%}}}
  %{{{ Inversion of permutations: deleteP and _˘
\begin{code}
  -- Deletion for permutations:
  -- [p₁, …, pₙ] ─ i   ↦   [p₁ ∸ 1, …, pᵢ₋₁ ∸ 1, pᵢ, pᵢ₊₁, …, pₙ] ?
  _─_ : {n : ℕ} → Permutation (suc n) → Fin (suc n) → Permutation n
  cons p ps         ─ zero              =  ps  -- i.e. delete the zero'th element is essentially “tail”
  (cons zero ps)    ─ (suc {zero} ())
  (cons zero ps)    ─ (suc {(suc n)} i) = cons zero (ps ─ i)  -- the suc is dropped, parenthesis move.
  cons (suc p) ps   ─ suc {zero} ()
  (cons (suc p) ps) ─ (suc {(suc n)} i) = cons p (ps ─ i)  -- the suc's “cancel” & mutually associate.

{-
  ─-spec : {n : ℕ} {ps : Permutation (suc n)} {i : Fin n} → (ps ─ (suc i)) at i  ≡  {!!}
  ─-spec {n} {ps} {i} = {!!}
  -- Where is mine hero in shining logical armor?
-}

  open import Relation.Nullary

  -- Permutations come with the obvious involution, but non-trivial implementation
  _˘ : {n : ℕ} → Permutation n → Permutation n
  _˘ {zero }     nil          = nil
  _˘ {suc n} ps@(cons p ps′) = cons 𝓅 ( (ps ─ 𝒑)˘ )
    where 𝓅 : Fin (suc n)
          𝓅 = ps at′ p

          𝒑 : Fin (suc n)
          𝒑 = ps at′ 𝓅

  test-rev˘ : toVec (rev {5} ˘) ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  test-rev˘ = ≡.refl
  -- Oh no, this looks bad!
  test-rev˘˘ :  ¬  toVec ((rev {5} ˘)˘) ≡ toVec (rev {5}) -- It seems this is not an involution!
  test-rev˘˘ ()

  -- |n ℕ∷_| and |_─ fromℕ n| are inverses
  ℕ∷-inverse-─ : {n : ℕ} → n ℕ∷ (rev {suc n} ─ fromℕ n)  ≡  rev {suc n}
  ℕ∷-inverse-─ {zero} = ≡.refl
  ℕ∷-inverse-─ {suc n} = ≡.cong (λ x → cons (fromℕ (suc n)) x) ℕ∷-inverse-─

  test-rev-end : toVec (rev {5} ─ fromℕ 4) ≡ 3 ∷ 2 ∷ 1 ∷ 0 ∷ [] -- i.e., toVec (rev {4})
  test-rev-end = ≡.refl

  rev-end=rev : {n : ℕ}  →  rev {suc n} ─ fromℕ n  ≡  rev {n}
  rev-end=rev {zero} = ≡.refl
  rev-end=rev {suc n} = ≡.cong (n ℕ∷_) rev-end=rev

  rev˘=Id : {n : ℕ} → rev ˘  ≡  Id {n}
  rev˘=Id {zero} = ≡.refl
  rev˘=Id {suc n} = ≡.cong₂ cons rev-end′ it -- ≡.cong₂ cons rev-end′ goal

    where

      step₁ : rev {suc n}  at′ rev {suc n} at′ fromℕ n ≡ (rev {suc n}) at′ zero
      step₁ = ≡.cong (rev at′_) rev-end′

      step₂ : (rev {suc n}) at′ zero  ≡  fromℕ n
      step₂ = rev-start′

      it₀ :    (rev {suc n} ─ (rev {suc n} at′ rev {suc n} at′ fromℕ n))  ˘
            ≡ (rev {n}) ˘
      it₀ = ≡.cong _˘ (≡.cong (rev {suc n} ─_) (step₁ ⟨≡≡⟩ step₂)
            ⟨≡≡⟩ rev-end=rev)

      it : (rev {suc n} ─ (rev {suc n} at′ rev {suc n} at′ fromℕ n))  ˘
            ≡ Id
      it = it₀ ⟨≡≡⟩ rev˘=Id
\end{code}

\begin{spec}
  -- Extensional Permutation equality
  infix 5 _≈ₚ_
  _≈ₚ_ : {n : ℕ} (ps qs : Permutation n) → Set (c ⊍ ℓ)
  _≈ₚ_ {n} ps qs  =  {xs : Seq n} → ps ◈ xs  ≈ₖ  qs ◈ xs

  -- This operation is involutionary: It is its own inverse.
  -- ˘˘ : {n : ℕ} {ps : Permutation n} → ps ˘ ˘  ≈ₚ  ps
  -- ˘˘ {zero} {nil} = ≈ₖ-refl
  -- ˘˘ {suc n} {cons p ps} {x ∷ xs} = {! FALSE: See test-rev˘˘!}

  -- The identity permutation is a fixed point.
  Id˘ : {n : ℕ} → Id ˘  ≈ₚ  Id {n}
  Id˘ {.0} {[]} = ≈ₖ-refl
  Id˘ {.(suc _)} {x ∷ xs} = cons ≈.refl Id˘
\end{spec}
%}}}
  %{{{ Properties of insertion and deletion for vectors
\begin{code}
  insert-cong : {n : ℕ} {xs ys : Seq n} {i : Fin (suc n)} {e : Carrier}
              → xs  ≈ₖ  ys  →  insert xs i e  ≈ₖ  insert ys i e
  insert-cong {i = zero} xs≈ys = cons ≈.refl xs≈ys
  insert-cong {i = suc _} nil              = ≈ₖ-refl
  insert-cong {i = suc _} (cons x≈y xs≈ys) = cons x≈y (insert-cong xs≈ys)

  -- Inverse of insert
  delete : {n : ℕ} {a : Level} {A : Set a} → Vec A (suc n) → Fin (suc n) → Vec A n
  delete (x ∷ xs) zero    = xs
  delete (x ∷ []) (suc ())
  delete (x ∷ _ ∷ xs) (suc zero) = x ∷ xs
  delete (x ∷ y ∷ xs) (suc (suc i)) = x ∷ delete (y ∷ xs) (suc i)

  delete-suc : {n : ℕ} {xs : Seq (suc n)} {i : Fin (suc n)} {x : Carrier}
             → delete (x ∷ xs) (suc i)  ≈ₖ  (x ∷ delete xs i)
  delete-suc {xs = x ∷ xs} {zero}   =  ≈ₖ-refl
  delete-suc {xs = x ∷ xs} {suc i}  =  ≈ₖ-refl

  delete-insert : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x : Carrier}
                → delete (insert xs i x) i  ≈ₖ  xs
  delete-insert {xs = []} {zero} = ≈ₖ-refl
  delete-insert {xs = []} {suc ()}
  delete-insert {xs = x ∷ xs} {zero} = ≈ₖ-refl
  delete-insert {xs = x ∷ xs} {suc zero} = ≈ₖ-refl
  delete-insert {xs = x ∷ xs} {suc (suc i)} {e} = goal
    where it :    delete (x ∷ insert xs (suc i) e) (suc (suc i))
               ≈ₖ (x ∷ delete (insert xs (suc i) e) (suc i))
          it = delete-suc

          indHyp : delete (insert xs (suc i) e) (suc i)  ≈ₖ  xs
          indHyp = delete-insert

          goal : delete (x ∷ insert xs (suc i) e) (suc (suc i)) ≈ₖ (x ∷ xs)
          goal = ≈ₖ-trans it (cons ≈.refl indHyp)

  insert-delete : {n : ℕ} {xs : Seq (suc n)} {i : Fin (suc n)}
                → insert (delete xs i) i (lookup i xs)  ≈ₖ  xs
  insert-delete {zero} {x ∷ xs} {zero} = ≈ₖ-refl
  insert-delete {zero} {x ∷ xs} {suc ()}
  insert-delete {suc n} {x ∷ xs} {zero} = ≈ₖ-refl
  insert-delete {suc n} {x ∷ xs} {suc i} = goal
    where it : delete (x ∷ xs) (suc i)  ≈ₖ  (x ∷ delete xs i)
          it = delete-suc

          notice :    insert (x ∷ delete xs i) (suc i) (lookup i xs)
                   ≈ₖ (x ∷ insert (delete xs i) i (lookup i xs))
          notice = ≈ₖ-refl  -- by definition of |insert|

          indHyp :    insert (delete xs i) i (lookup i xs)
                   ≈ₖ  xs
          indHyp = insert-delete

          goal :    insert (delete (x ∷ xs) (suc i)) (suc i) (lookup i xs)
                  ≈ₖ (x ∷ xs)
          goal = ≈ₖ-trans (insert-cong it) (cons ≈.refl indHyp) 
\end{code}
%}}}
  %{{{ ◈ is a group action: It is an functorial in it's first argument.

\begin{code}
  ◈-leftId : {n : ℕ} {xs : Seq n} → Id ◈ xs  ≈ₖ  xs
  ◈-leftId {zero} {[]} = ≈ₖ-refl
  ◈-leftId {suc n} {x ∷ xs} = cons ≈.refl ◈-leftId

  -- Composition of permutations
  infix 6 _⊙_
  _⊙_ : {n : ℕ} → Permutation n → Permutation n → Permutation n
  nil ⊙ nil = nil
  cons p ps ⊙ qs  =  cons (qs at′ p) (ps ⊙ (qs ─ p))

  -- ⊙-nil : {n : ℕ} {ps : Permutation n} → ps ⊙ nil  ≡  ps
  -- ⊙-nil {n} {ps} = ?

{-
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

-}

\end{code}

%}}}

%}}}

Expected definition,
\begin{spec}
  data _≈ₚ_ {n : ℕ} (xs ys : Seq n) : Set (c ⊍ ℓ) where
    yes : (p : Permutation n) → p ◈ xs ≈ₖ ys → xs ≈ₚ ys
\end{spec}

However this does not fit in with our needs in |Bag.lagda|, so we work with a bit of
an awkward definition. \edcomm{MA}{Perhaps we could have a transform between the two forms?}

\begin{spec}
  List = Σ n ∶ ℕ • Seq n

  data _≈ₚₗ_ : (x y : List) → Set (c ⊍ ℓ) where
    yes : {n : ℕ} {xs ys : Seq n} (p : Permutation n) → p ◈ xs ≈ₖ ys → (n , xs) ≈ₚₗ (n , ys)

  to-awkward : {m n : ℕ} {xs : Seq m} {ys : Seq n} → m ≡ n → xs ≈ₚ ys → (n , xs) ≈ₚₗ (m , ys)
  to-awkward ≡.refl (yes p p◈xs≈ys) = yes p p◈xs≈ys

  postulate ≈ₚ-refl :  {n : ℕ}{xs       : Seq n} → xs ≈ₚ xs
  postulate ≈ₚ-sym :   {n : ℕ}{xs ys    : Seq n} → xs ≈ₚ ys → ys ≈ₚ xs
  postulate ≈ₚ-trans : {n : ℕ}{xs ys zs : Seq n} → xs ≈ₚ ys → ys ≈ₚ zs → xs ≈ₚ zs

  ≈ₚ-isEquivalence : {n : ℕ} → IsEquivalence (_≈ₚ_ {n})
  ≈ₚ-isEquivalence = record { refl = ≈ₚ-refl ; sym = ≈ₚ-sym ; trans = ≈ₚ-trans }

  ≈ₚₗ-isEquivalence : IsEquivalence _≈ₚₗ_
  ≈ₚₗ-isEquivalence = record { refl = to-awkward ≈ₚ-refl ; sym = {!to-awkward ∘₀ ?!} ; trans = {!!} }

  ε : List
  ε = (0 , [])

  _⊕_ : List → List → List
  (_ , xs) ⊕ (_ , ys) = (_ , xs ++ ys)

  -- Strangely properties about Vec catenation are not in the standard library

  ⊕-left-unit : ∀ ys → (ε ⊕ ys) ≈ₚₗ ys
  ⊕-left-unit ys = ≈ₚₗ-refl

--  ≈ₚₗ-pair : {m n : ℕ} {xs : Seq m} {ys : Seq n} → m ≡ n → s ≈ₚₗ t → (m , xc

  ⊕-right-unit : ∀ ys → (ys ⊕ ε) ≈ₚₗ ys
  ⊕-right-unit (.0 , []) = ≈ₚₗ-refl
  ⊕-right-unit (.(suc _) , x ∷ proj₄) = {!≈ₚₗ-refl!}
\end{spec}

\begin{code}
  open import Data.List
  Seq∞ = List Carrier

  record _≈ₚ_ (xs ys : List Carrier) : Set (c ⊍ ℓ) where
    len₁ : ℕ
    len₁ = length xs

    len₂ : ℕ
    len₂ = length ys

    field
      lengths : len₂ ≡ len₁
      witness : Permutation len₁
      proof   : witness ◈ fromList xs ≈ₖ ≡.subst Seq lengths (fromList ys)

  ≈ₚ-reflexive : {xs ys : Seq∞} → xs ≡ ys → xs ≈ₚ ys
  ≈ₚ-reflexive ≡.refl = record { lengths = ≡.refl ; witness = Id ; proof = ◈-leftId   }

  ≈ₚ-refl :  {xs : Seq∞} → xs ≈ₚ xs
  ≈ₚ-refl = ≈ₚ-reflexive ≡.refl

  postulate ≈ₚ-sym :   {xs ys    : Seq∞} → xs ≈ₚ ys → ys ≈ₚ xs
  postulate ≈ₚ-trans : {xs ys zs : Seq∞} → xs ≈ₚ ys → ys ≈ₚ zs → xs ≈ₚ zs

  ≈ₚ-isEquivalence : IsEquivalence _≈ₚ_
  ≈ₚ-isEquivalence = record { refl = ≈ₚ-refl ; sym = ≈ₚ-sym ; trans = ≈ₚ-trans }

  singleton-≈ : {x y : Carrier} → x ≈ y → (x ∷ []) ≈ₚ (y ∷ [])
  singleton-≈ x≈y = record { lengths = ≡.refl ; witness = Id ; proof = VecEquality.cons x≈y nil }
\end{code}


%{{{ approach via vectors rather than lists

\begin{code}
module Lemmas {l c : Level} {𝒮 : Setoid c l} (𝒞 : CommMonoid 𝒮) where

  open CommMonoid 𝒞
  open IsCommutativeMonoid isCommMonoid -- \edcomm{MA}{The field name really oughtn't be abbreviated!}
  
  open Setoid 𝒮
  
  open VecEquality 𝒮
  -- module ≈ = Setoid 𝒮

  open Permutations 𝒮

  -- from CommMonoid.CommMonoid
  -- open Setoid 𝒮 using () renaming (Carrier to X₀)
  -- postulate e            : X₀
  -- postulate _*_          : X₀ → X₀ → X₀  -- \edcomm{MA}{Why is this `e` but above is `·`?}
  -- _⟨≈⟩_ = ≈.trans
  -- infix -666 eq-in
  -- eq-in = ≈._≈_
  -- syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon
  -- import Algebra.FunctionProperties as AFP
  -- open AFP ≈._≈_
  -- postulate  _⟨∙⟩_        : Congruent₂ _*_
  -- postulate assoc       : Associative _*_
  -- postulate     comm        : Commutative _*_

  open import Data.List
  open import Data.Nat  hiding (fold ; _*_)
  open import Data.Fin  hiding (_+_ ; fold ; _≤_)  
\end{code}


\begin{code}  
  -- fold is a setoid homomorphism

  fold : Seq∞ → Carrier
  fold = foldr _*_ e

  open import Data.Vec using (fromList)

  fold-cong : {xs ys : Seq∞} → xs ≈ₚ ys → fold xs ≈ fold ys
  fold-cong {[]} {[]} record { lengths = ≡.refl ; witness = witness ; proof = proof } = {!!}
  fold-cong {[]} {x ∷ ys} record { lengths = () ; witness = witness ; proof = proof }
  fold-cong {x ∷ xs} {ys} record { lengths = lengths ; witness = witness ; proof = proof } = {!!}

\end{code}
  fold-cong : {xs ys : Seq∞} → fromList xs ≈ₖ fromList ys → fold xs ≈ fold ys
  fold-cong {_} {[]} {.[]} nil = refl
  fold-cong {_} {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

  open Permutations 𝒮
  
  data _≈ᵥ_ {n : ℕ} (xs : Seq n) (ys : Seq n) : Set (c ⊍ l) where
    yes : (p : Permutation n) → p ◈ xs ≈ₖ ys → xs ≈ᵥ ys

  open import Relation.Binary.SetoidReasoning

  -- commutativity here!
  proposition₄ : {n : ℕ} {zs : Seq n} {x y : Carrier}
               → fold (x ∷ y ∷ zs) ≈ fold (y ∷ x ∷ zs)
  proposition₄ {n} {zs} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ zs)
    ≈˘⟨ assoc _ _ _ ⟩
      (x * y) * fold zs
    ≈⟨ comm _ _ ⟨∙⟩ refl ⟩
      (y * x) * fold zs
    ≈⟨ assoc _ _ _ ⟩
      fold (y ∷ x ∷ zs)
    ∎

  proposition₃ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x y : Carrier}
               → fold (x ∷ y ∷ xs) ≈ fold (y ∷ insert xs i x)
  proposition₃ {.0} {[]} {zero} =  proposition₄ 
  proposition₃ {.0} {[]} {suc ()}
  proposition₃ {.(suc _)} {x ∷ xs} {zero} = proposition₄ 
  proposition₃ {.(suc _)} {hd ∷ xs} {suc i} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ hd ∷ xs)
    ≈⟨ proposition₄ ⟩
      fold (y ∷ x ∷ hd ∷ xs)
    ≡⟨ ≡.refl ⟩
      y * fold (x ∷ hd ∷ xs)
    ≈⟨ refl ⟨∙⟩ proposition₃ ⟩
      y * fold (hd ∷ insert xs i x)
    ≡⟨ ≡.refl ⟩
      fold (y ∷ hd ∷ insert xs i x)
    ∎
  
  proposition₂ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x : Carrier}
               → fold (x ∷ xs) ≈ fold (insert xs i x)
  proposition₂ {.0} {[]} {zero} = refl
  proposition₂ {.0} {[]} {suc ()}
  proposition₂ {.(suc _)} {y ∷ xs} {zero} = refl
  proposition₂ {.(suc _)} {y ∷ xs} {suc i} = proposition₃

  open import Relation.Binary.PropositionalEquality using (inspect; [_])

  proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n} → fold xs ≈ fold (p ◈ xs) 
  proposition₁ {.0} {[]} {nil} = refl
  proposition₁ {.(suc _)} {x ∷ xs} {cons zero ps} = refl ⟨∙⟩ proposition₁
  proposition₁ {.(suc _)} {x ∷ xs} {cons (suc p) ps} with ps ◈ xs | inspect (_◈_ ps) xs
  proposition₁ {.(suc 0)} {x ∷ xs} {cons (suc ()) ps} | [] | _
  proposition₁ {.(suc (suc _))} {x ∷ xs} {cons (suc p) ps} | x′ ∷ xs′ | [ ps-on-xs≈xs′ ] = begin⟨ 𝒮 ⟩
      x * fold xs
    ≈⟨ refl ⟨∙⟩ proposition₁ ⟩
      x * fold (ps ◈ xs)
    ≡⟨ ≡.cong (λ zs → x * fold zs) ps-on-xs≈xs′ ⟩
      x * fold (x′ ∷ xs′)
    ≡⟨ ≡.refl ⟩
      fold (x ∷ x′ ∷ xs′)
    ≈⟨ proposition₄ ⟩
      fold (x′ ∷ x ∷ xs′)
    ≡⟨ ≡.refl ⟩
      x′ * fold (x ∷ xs′)
    ≈⟨ refl ⟨∙⟩ proposition₂ ⟩
      x′ * fold (insert xs′ p x)
    ∎

  -- This is essentially |Multiset.fold-permute|, the pesky-hole from the summer.
  proposition₀ : {n : ℕ} {xs ys : Seq n} → xs ≈ᵥ ys → fold xs ≈ fold ys 
  proposition₀ (yes p p-on-xs≈ys) = trans proposition₁ (fold-cong p-on-xs≈ys)


%{{{ Vector based approach, it works:
\begin{spec}  
  -- fold is a setoid homomorphism

  fold : {n : ℕ} → Seq n → Carrier
  fold = foldr (λ _ → Carrier) _*_ e

  fold-cong : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong {_} {[]} {.[]} nil = refl
  fold-cong {_} {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

  open Permutations 𝒮
  
  data _≈ᵥ_ {n : ℕ} (xs : Seq n) (ys : Seq n) : Set (c ⊍ l) where
    yes : (p : Permutation n) → p ◈ xs ≈ₖ ys → xs ≈ᵥ ys

  open import Relation.Binary.SetoidReasoning

  -- commutativity here!
  proposition₄ : {n : ℕ} {zs : Seq n} {x y : Carrier}
               → fold (x ∷ y ∷ zs) ≈ fold (y ∷ x ∷ zs)
  proposition₄ {n} {zs} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ zs)
    ≈˘⟨ assoc _ _ _ ⟩
      (x * y) * fold zs
    ≈⟨ comm _ _ ⟨∙⟩ refl ⟩
      (y * x) * fold zs
    ≈⟨ assoc _ _ _ ⟩
      fold (y ∷ x ∷ zs)
    ∎

  proposition₃ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x y : Carrier}
               → fold (x ∷ y ∷ xs) ≈ fold (y ∷ insert xs i x)
  proposition₃ {.0} {[]} {zero} =  proposition₄ 
  proposition₃ {.0} {[]} {suc ()}
  proposition₃ {.(suc _)} {x ∷ xs} {zero} = proposition₄ 
  proposition₃ {.(suc _)} {hd ∷ xs} {suc i} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ hd ∷ xs)
    ≈⟨ proposition₄ ⟩
      fold (y ∷ x ∷ hd ∷ xs)
    ≡⟨ ≡.refl ⟩
      y * fold (x ∷ hd ∷ xs)
    ≈⟨ refl ⟨∙⟩ proposition₃ ⟩
      y * fold (hd ∷ insert xs i x)
    ≡⟨ ≡.refl ⟩
      fold (y ∷ hd ∷ insert xs i x)
    ∎
  
  proposition₂ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x : Carrier}
               → fold (x ∷ xs) ≈ fold (insert xs i x)
  proposition₂ {.0} {[]} {zero} = refl
  proposition₂ {.0} {[]} {suc ()}
  proposition₂ {.(suc _)} {y ∷ xs} {zero} = refl
  proposition₂ {.(suc _)} {y ∷ xs} {suc i} = proposition₃

  open import Relation.Binary.PropositionalEquality using (inspect; [_])

  proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n} → fold xs ≈ fold (p ◈ xs) 
  proposition₁ {.0} {[]} {nil} = refl
  proposition₁ {.(suc _)} {x ∷ xs} {cons zero ps} = refl ⟨∙⟩ proposition₁
  proposition₁ {.(suc _)} {x ∷ xs} {cons (suc p) ps} with ps ◈ xs | inspect (_◈_ ps) xs
  proposition₁ {.(suc 0)} {x ∷ xs} {cons (suc ()) ps} | [] | _
  proposition₁ {.(suc (suc _))} {x ∷ xs} {cons (suc p) ps} | x′ ∷ xs′ | [ ps-on-xs≈xs′ ] = begin⟨ 𝒮 ⟩
      x * fold xs
    ≈⟨ refl ⟨∙⟩ proposition₁ ⟩
      x * fold (ps ◈ xs)
    ≡⟨ ≡.cong (λ zs → x * fold zs) ps-on-xs≈xs′ ⟩
      x * fold (x′ ∷ xs′)
    ≡⟨ ≡.refl ⟩
      fold (x ∷ x′ ∷ xs′)
    ≈⟨ proposition₄ ⟩
      fold (x′ ∷ x ∷ xs′)
    ≡⟨ ≡.refl ⟩
      x′ * fold (x ∷ xs′)
    ≈⟨ refl ⟨∙⟩ proposition₂ ⟩
      x′ * fold (insert xs′ p x)
    ∎

  -- This is essentially |Multiset.fold-permute|, the pesky-hole from the summer.
  proposition₀ : {n : ℕ} {xs ys : Seq n} → xs ≈ᵥ ys → fold xs ≈ fold ys 
  proposition₀ (yes p p-on-xs≈ys) = trans proposition₁ (fold-cong p-on-xs≈ys)
\end{spec}
%}}}

%}}}

%{{{ attempting to connect the above with work in BagEq
\begin{spec}
  open BagEq 𝒮
  _≈ᵥᵥ_ : {n : ℕ} → Seq n → Seq n → Set (c ⊍ l)
  _≈ᵥᵥ_ = λ xs ys → toList xs ⇔ toList ys

  open Locations 𝒮
  -- no.
  bridge₁ : {n : ℕ} {xs ys : Seq n} {a b : Carrier} → (a ∷ xs) ≈ᵥᵥ (b ∷ ys) → a ≈ b ⊎ a ∈₀ toList ys
  bridge₁ {.0} {[]} {[]} eq = {!!}
  bridge₁ {.(suc _)} {x ∷ xs} {x₁ ∷ ys} eq = {!!}

  bridge : {n : ℕ} {xs ys : Seq n} → xs ≈ᵥᵥ ys → xs ≈ᵥ ys
  bridge {.0} {[]} {[]} eq = yes nil nil
  bridge {.(suc _)} {x ∷ xs} {y ∷ ys} eq = {!This may require decidable equality on elements.!}
\end{spec}
%}}}

%{{{ Ignore: Lists approach requires some transformations between with Fin's
\begin{spec}
open import Algebra   using (CommutativeMonoid)
module Lemmas′ {l c : Level} {𝒞 : CommutativeMonoid c l} where

  open CommutativeMonoid 𝒞
  open import Relation.Binary.SetoidReasoning -- renaming (_∎ to _■)

  open import Data.List     using (List; []; _++_; _∷_; foldr; length)  renaming (map to mapL)
  open import Data.List.Properties using (map-++-commute; map-id; map-compose)

  open import Data.Nat hiding (fold)
  open import Data.Fin hiding (_+_ ; fold)

  -- Sequences
  Seq = List Carrier

  -- `k`omponent-wise equality on sequences ;; MA: Subscript `c` not directly available.
  data _≈ₖ_ : Seq → Seq → Set (c ⊍ l) where
    nil  : [] ≈ₖ []
    cons : {x y : Carrier} {xs ys : Seq} → x ≈ y → xs ≈ₖ ys → (x ∷ xs) ≈ₖ (y ∷ ys)

  -- MA: It is a simple matter to show that this is an equivalence relation. TODO.
  
  -- fold is a setoid homomorphism

  fold : Seq → Carrier
  fold = foldr _∙_ ε

  fold-cong : {xs ys : Seq} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong {[]} {.[]} nil = refl
  fold-cong {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = begin⟨ setoid ⟩
      fold (x ∷ xs)
    ≡⟨ ≡.refl ⟩
      x ∙ fold xs
    ≈⟨ ∙-cong x≈y (fold-cong xs≈ys) ⟩
      y ∙ fold ys
    ≡⟨ ≡.refl ⟩
      fold (y ∷ ys)
    ∎
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

  -- from copumkin's library
  data Permutation : ℕ → Set where
    nil  : Permutation 0
    cons : {n : ℕ} (p : Fin (1 + n)) (ps : Permutation n) → Permutation (1 + n)

  -- insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
  insert : (xs : Seq) → Fin (1 + length xs) → Carrier → Seq
  insert xs zero a = a ∷ xs
  insert [] (suc ()) a
  insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

  -- permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
  mutual
  
    permute : (xs : Seq) → Permutation (length xs) → Seq
    permute [] nil = []
    permute (x ∷ xs) (cons p ps)  = insert (permute xs ps) (cast p) x
    --
    -- Note that we switch the order as compared to copumkin since we're using lists.

    cast : {xs : Seq} {p : Permutation (length xs)}
         → Fin (1 + length xs) → Fin (1 + length (permute xs p))
    cast {[]} {nil} i = i
    cast {x ∷ xs} {cons p p₁} zero = zero
    cast {x ∷ xs} {cons p p₁} (suc i) = {!!} -- suc (insert-cast {!!}) -- (insert-cast {!!})

    insert-cast : {xs : Seq} {i : Fin (1 + length xs)} {x : Carrier}
                  {ps : Permutation (length xs)}
              → Fin (length xs) → Fin (length (insert (permute xs ps) (cast i) x))
    insert-cast = {!!}
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
