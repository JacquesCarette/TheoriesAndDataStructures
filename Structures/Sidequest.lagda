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
open import Data.Nat.Properties.Simple using (+-right-identity)

open import Data.List using (monoid)
open import Data.Fin using (fromℕ)

open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
-- open CommMonoid using (eq-in ; isCommMonoid)
\end{code}
%}}}

%{{{ VecEquality
\edcomm{MA}{See |Data.Vec.Equality|; it may have this setup already. However, ours is heterogenous.}
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
  data _≈ₖ_ : {n m : ℕ} → Seq n → Seq m → Set (c ⊍ ℓ) where
    nil  : [] ≈ₖ []
    cons : {x y : Carrier} {n m : ℕ} {xs : Seq n} {ys : Seq m} (x≈y : x ≈ y) (xs≈ys : xs ≈ₖ ys) → (x ∷ xs) ≈ₖ (y ∷ ys)
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

We initially took the following as definition. However, later in the development we were
led inexorably to the utilisation of |subst|. Previous experience suggests that using
an additional parameter which at first seems to be more general than necessary but in-fact
the constructor only permit this new parameter to have the same value as was needed before
with the |subst|.

\edcomm{JC}{Basically, a permutation tells you how to insert all elements of |Fin m| into something of length |n| surjectively. Naturally, this can only be done when |n = m|. |Apply| then applies |Permutation m n| to a |Vec A m|, to obtain a |Vec A n|.}

\begin{spec}
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
\end{spec}

Instead we employ a definition relying on a new additional parameter --which will then be forced to be
equal to an existing parameter. This is in the spirit of the so-called John Major Equality or the
oxymoronic “Heterogeneous Equality” concept.

\edcomm{JC}{I think of |Permutation n m| as having length |n| and inhabited by things of type |Fin m|. So you use |n| to index, and |m| for what you retrieve.}

\begin{code}
  infixr 5 _∷_
  data Permutation : (n _ : ℕ) → Set where
    []  : Permutation 0 0
    _∷_ : {n : ℕ} → (p : Fin (suc n)) → (ps : Permutation n n) → Permutation (suc n) (suc n)

  -- Notice the additional parameter, in all possible constructions, is the same as the first pa ram.
  homogeneity : {n m : ℕ} → Permutation n m → n ≡ m
  homogeneity [] = ≡.refl
  homogeneity (p ∷ ps) = ≡.cong suc (homogeneity ps)
\end{code}

One may ask why we do not employ a more general typing for cons, as in
\begin{spec}
   _∷_ : {n m : ℕ} → (p : Fin (suc n)) → (ps : Permutation n m) → Permutation (suc n) (suc m)
\end{spec}
The issue here is that the need for |homogeneity| comes to the forefront for many uses of
|Permutation|s in the form of |rewrite|'s or |with|'s --both of which are avoided when we use the
less generic typing.

For example, our application operation |_◈_| below, and those that use it, must use a |rewrite|
clause:
\begin{spec}
  _◈_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A n → Vec A m
  []       ◈ []       = []
  it@(p ∷ ps) ◈ (x ∷ xs) rewrite (homogeneity it) = insert (ps ◈ xs) p x
\end{spec}

\begin{code}
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
  _◈_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A n → Vec A m
  []       ◈ []       = []
  (p ∷ ps) ◈ (x ∷ xs) = insert (ps ◈ xs) p x

  _ℕ∷_ : (n : ℕ) (ps : Permutation n n) → Permutation (suc n) (suc n)
  _ℕ∷_ = λ n ps → fromℕ n ∷ ps
\end{code}
%}}}
  %{{{ Rotational Permutations: Reverse and Identity

Let's consider the formation of the family of permutations that rotate a given vector.

We can form such a family in three ways:
\begin{itemize}
\item |rotate₋₁|: We request a proof that the rotational push is no more the length of the vector.

\item |rotate|:  The rotational push along with an \emph{offset} are needed to form the permutation.

\item |rotate₁|:   The rotational push is of type |Fin n| where |n| is the length of the vector.

          The downside of this definition is that it requires a double-pattern matching on |n|
          for any of its uses to normalise. This cost is a bit more than we want and so we instead
          use |rotate| while acknowledging that |rotate₁| may be the more appropriate definition.
\end{itemize}

\begin{code}
  -- Make an i-length rotation for an (i + offset)-length vector.
  rotate : {offset : ℕ} (i : ℕ) → Permutation (i + offset) (i + offset)
  rotate {zero}  zero    = []
  rotate {suc offset} zero    = zero     ∷ rotate 0
  rotate {offset}     (suc i) = (i + offset) ℕ∷ rotate i

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
  -- That these two can both be written is distastefully permissive.
  test₅ : rotate 5 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₅ = ≡.refl

  rotate₁ : {n : ℕ} (i : Fin n) → Permutation n n
  rotate₁ {zero} ()
  rotate₁ {suc zero} zero = zero ∷ []
  rotate₁ {suc (suc n)} zero = zero ∷ rotate₁ zero
  rotate₁ {suc n} (suc i) = n ℕ∷ rotate₁ i

  test₀′  : rotate₁ zero ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test₀′  = ≡.refl

  test₁′  : rotate₁ (suc zero)  ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (2 ∷ 3 ∷ 4 ∷ 5 ∷ 1 ∷ [])
  test₁′  = ≡.refl

  test₂′  : rotate₁ (suc (suc zero)) ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 ∷ 4 ∷ 5 ∷ 2 ∷ 1 ∷ [])
  test₂′  = ≡.refl

  test₃′  : rotate₁ (suc (suc (suc zero))) ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (4 ∷ 5 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₃′  = ≡.refl

  test₄′  : rotate₁ (suc (suc (suc (suc zero)))) ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  test₄′  = ≡.refl

  -- Ill-typed.
  -- test₅′  : rotate₁ (suc (suc (suc (suc (suc zero))))) ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  -- test₅′  = ≡.refl

  -- This permutation performs 0-many rotations on a given vector.
  Id : {n : ℕ} → Permutation n n
  Id {n} = rotate 0

  -- The identity is deserving of its name.
  Id-◈ : {n : ℕ} {xs : Seq n} → Id ◈ xs ≈ₖ xs
  Id-◈ {xs = []   } = nil
  Id-◈ {xs = _ ∷ _} = cons ≈.refl Id-◈

  -- ( This is what characterizes, or specifies, the identity! )
  Id-spec = Id-◈
\end{code}

Using |rotate₁| would have been a bit more verbose:
\begin{code}
  Idd : {n : ℕ} → Permutation n n
  Idd {zero}  = []
  Idd {suc n} = rotate₁ zero

  Idd-◈ : {n : ℕ} {xs : Seq n} → Idd ◈ xs ≈ₖ xs
  Idd-◈ {.0} {[]} = nil
  Idd-◈ {.1} {x ∷ []} = ≈ₖ-refl
  Idd-◈ {.(suc (suc _))} {x ∷ x₁ ∷ xs} = cons ≈.refl Idd-◈
\end{code}

\begin{code}
  -- |rev {n} == rotate {0} n| -- we need to use subst to obtain |n + 0 ≡ n|
  -- A direct implementation is then clearer.
  rev : {n : ℕ} → Permutation n n
  rev {zero}  = []
  rev {suc n} = n ℕ∷ rev
\end{code}

\begin{spec}
  private
    suc-injective : {m n : ℕ} → _≡_ {A = ℕ} (suc m) (suc n) → m ≡ n
    suc-injective ≡.refl = ≡.refl

  rev-as-rotate : {n : ℕ}
    → rev {n} ≡ ≡.subst (λ m → Permutation m m) (+-right-identity n) (rotate {0} n)
  rev-as-rotate {zero} = ≡.refl
  rev-as-rotate {suc n} with ≡.cong suc (+-right-identity (suc n))
  ...| l = {! Why not, Agda?!}
\end{spec}

\edcomm{MA}{Since addition is defined recursively on the first argument, the equality |rev {n} = rotate {0} n| is ill-typed since the left side has type `Permutation n n` whereas the right has the type `Permutation (n + 0) (n + 0)` which does not rewrite `n + 0` to `n`, by definition of addition. One possible solution might be to redefine `rotate` to produce elements of type `Permutation (n + i) (n + i)` to obtain the automatic rewrite for `0 + n` to `n`. However, it is not longer trivial to infer `n` so that all the types match-up and so we obtain a host of yellow. See the next block below.}

\begin{spec}
  rotat : {offset : ℕ} (i : ℕ) → Permutation (offset + i) (offset + i)
  rotat {zero} zero = []
  rotat {zero} (suc i) = i ℕ∷ rotat {zero} i -- 0 offset with an i rotation is the reverse permutation.
  rotat {suc offset} i = (offset + i) ℕ∷ rotat {offset} i

  yellow-test₁ : rotat {{! Try to fill me!!}} 1 ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (2 ∷ 3 ∷ 4 ∷ 5 ∷ 1 ∷ [])
  yellow-test₁ = ≡.refl
\end{spec}

%{{{ Attempt at automatically generating coherency proofs

\begin{code}
{-
  Also considered,

  -- rotate : {n : ℕ} (i : Fin n) → Permutation (toℕ i + n)
  -- rotate {suc zero} zero    = cons zero nil
  -- rotate {suc (suc n)} zero = cons zero (rotate zero)
  -- rotate {suc n} (suc i) = cons (fromℕ (toℕ i + suc n)) (subst Permutation {!!} (rotate (inject₁ i)))
-}

  rotate₋₁ : (n : ℕ) (i : ℕ){{coh : i ≤ n}} → Permutation (i + n) (i + n)
  rotate₋₁ zero .0 {{z≤n}} = []
  rotate₋₁ (suc n) .0 {{z≤n}} = zero ∷ (rotate₋₁ n 0 {{z≤n}})
  rotate₋₁ (suc n) .(suc i) {{s≤s {i} coh}} = (i + suc n) ℕ∷ (rotate₋₁ (suc n) i {{≤-steps 1 coh}})

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
  toVec : {n m : ℕ} → Permutation n m → Vec ℕ n
  toVec [] = []
  toVec (p ∷ ps) = toℕ p ∷ toVec ps

  toVector : {n m : ℕ} → Permutation n m → Vec (Fin n) m
  toVector = λ p → p ◈ Data.Vec.allFin _

  -- Notice that no need to explicitly invoke |homogeneity| since
  -- the pattern matching ensures |n ≡ m|.
  --
  -- Likewise below for |_at_|.

  -- ToDo: Consider forming inverse of toVec.

  -- move to DataCombinators.lagda
  _‼_ : {a : Level} {A : Set a} {n : ℕ} → Vec A n → Fin n → A
  _‼_ = λ xs i → lookup i xs
\end{code}

Deprecated.
\begin{spec}
  infixr 6 _at_  _at′_

  _at_ : {n m : ℕ} → Permutation n m → (i : Fin n) → Fin (n ∸ toℕ i)
  (p ∷ ps) at zero   =  p
  (p ∷ ps) at suc i  =  ps at i

  at-spec : {n m : ℕ} {ps : Permutation n m} {i : Fin n} → toℕ (ps at i)  ≡  lookup i (toVec ps)
  at-spec {.(suc _)} {_} {p ∷ ps} {zero}  =  ≡.refl
  at-spec {.(suc _)} {_} {p ∷ ps} {suc i} =  at-spec {ps = ps} {i}

  open import Data.Fin.Properties using (inject≤-lemma ; to-from ; toℕ-injective)

  _at′_ : {n m : ℕ} → Permutation n m → Fin n → Fin n
  (p ∷ ps) at′ zero = p
  (p ∷ ps) at′ suc i = inject≤ (ps at′ i) (n≤1+n _)
  -- \edcomm{JC}{I think of |Permutation n m| as having length |n| and inhabited by things of type |Fin m|. So you use |n| to index, and |m| for what you retrieve.}

  at′-spec : {n m : ℕ} {ps : Permutation n m} {i : Fin n} → toℕ (ps at′ i)  ≡ lookup i (toVec ps)
  at′-spec {.(suc _)} {_} {p ∷ ps} {zero} = ≡.refl
  at′-spec {.(suc n)} {_} {_∷_ {n} p ps} {suc i}
    rewrite inject≤-lemma (ps at′ i) (n≤1+n n) = at′-spec {ps = ps} {i}

  -- It is easier to prove certain results with |_at_| rather than |_at′_| due to the
  -- pesky injection. This combinator will hopefully alleviate some troubles.
  -- See |rev-end′| for example usage.
  at-at′ : {n m : ℕ} {ps : Permutation n m} {i : Fin n} → toℕ (ps at i) ≡  toℕ (ps at′ i)
  at-at′ {.(suc _)} {m} {p ∷ ps} {zero} = ≡.refl
  at-at′ {.(suc n)} {m} {p ∷ ps} {suc {n} i}
    rewrite inject≤-lemma (ps at′ i) (n≤1+n n) =  at-at′ {n} {m} {i = i}

  test-Id : toVec (Id {5}) ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  test-Id = ≡.refl

  Id-spec₁ : {n : ℕ} {j : Fin (suc n)} → toℕ (Id {suc n} at j)  ≡  0
  Id-spec₁ {n} {zero} = ≡.refl
  Id-spec₁ {zero} {suc ()}
  Id-spec₁ {suc n} {suc j} = Id-spec {n} {j}

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
  rev-end′ {n} = toℕ-injective
    (≡.sym (at-at′ {suc n} {suc n} {ps = rev {suc n}} {fromℕ n}) ⟨≡≡⟩ rev-end {n})
\end{spec}
%}}}
  %{{{ Inversion of permutations: deleteP and _˘

\edcomm{MA}{The inversion construct does not function as intended -- it is not invertible for example!
See |test-rev˘˘| below.}

\begin{code}
  -- Deletion for permutations
  _─_ : {n m : ℕ} → Permutation (suc n) (suc m) → Fin (suc n) → Permutation n m
  (p  ∷ ps)      ─ zero              =  ps  -- i.e. delete the zero'th element is essentially “tail”
  (zero ∷ ps)    ─ (suc {zero} ())
  (zero ∷ ps)    ─ (suc {(suc n)} i) = zero ∷ (ps ─ i)
  ((suc p) ∷ ps) ─ suc {zero} ()
  ((suc p) ∷ ps) ─ (suc {(suc n)} i) = either sub1 Id₀ (idris (suc p)) ∷ (ps ─ i)

    where

      open import Data.Sum using () renaming (map to _⊎₁_; [_,_] to either)

      -- Attempt to tighten the bound on a Fin
      idris : {m : ℕ} → Fin (suc m) → (Fin (suc m)) ⊎ (Fin m)
      idris {zero} zero = inj₁ zero
      idris {zero} (suc ())
      idris {suc m} zero = inj₂ zero
      idris {suc m} (suc i) = (suc ⊎₁ suc) (idris i)

      -- spec : {m : ℕ} {i : Fin (suc m)} (i<m : toℕ i Data.Nat.< m) → idris i ≡ inj₂ (fromℕ≤ i<m)

      sub1 : {m : ℕ} → Fin (suc (suc m)) → Fin (suc m)
      sub1 zero    = zero
      sub1 (suc i) = i
\end{code}

\edcomm{MA}{Perhaps it is my poor understanding of dependent types: Why is it that
|(either sub1 Id₀ (idris (suc q))) ≠ q|?
\begin{spec}
      orginalUse : {m : ℕ} {q : Fin (suc m)}
                 → (either sub1 Id₀ (idris (suc q))) ≡ q
      orginalUse {zero} {zero} = ≡.refl
      orginalUse {zero} {suc ()}
      orginalUse {suc m} {zero} = {! woah! Nice! … But, why?!}
      orginalUse {suc m} {suc q} = {!!}
\end{spec}
}

\edcomm{MA}{Having a “specification” for permutation deletion would be exceedingly helpful!}

\begin{code}
  open import Relation.Nullary

  -- Permutations come with the obvious involution, but non-trivial implementation
  _˘ : {n m : ℕ} → Permutation n m → Permutation m n
  _˘ {zero }     []        = []
  _˘ {suc n} ps@(p ∷ _) = (toVector ps ‼ i'p) ∷ (ps ─ i'p)˘
    where
          i'p : Fin (suc n)
          i'p = toVector ps ‼ p

  -- vmchale makes no recursive call...

  -- Specification/characterisation of inverse: It can be used to solve equations.
  ˘-char : {n m : ℕ} {xs : Seq n} {p : Permutation n m} {ys : Seq m} → p ◈ xs ≈ₖ ys → p ˘ ◈ ys ≈ₖ xs
  ˘-char {n} {m} {xs} {p} {ys} eq = {!!}

  test-rev˘ : toVec (rev {5} ˘) ≡ {!toVec ((rev {5}) )!} -- 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  test-rev˘ = {!!} -- ≡.refl
  -- Oh no, this looks bad!
  test-rev˘˘ :  ¬  toVec ((rev {5} ˘)˘) ≡ toVec (rev {5}) -- It seems this is not an involution!
  test-rev˘˘ = {!!} -- ()

  -- |n ℕ∷_| and |_─ fromℕ n| are inverses
  ℕ∷-inverse-─ : {n : ℕ} → n ℕ∷ (rev {suc n} ─ fromℕ n)  ≡  rev {suc n}
  ℕ∷-inverse-─ {zero} = ≡.refl
  ℕ∷-inverse-─ {suc n} = {!!} -- ≡.cong ((suc n) ℕ∷_) ℕ∷-inverse-─

  test-rev-end : toVec (rev {5} ─ fromℕ 4) ≡ 3 ∷ 2 ∷ 1 ∷ 0 ∷ [] -- i.e., |toVec (rev {4})|
  test-rev-end = ≡.refl

  rev-end=rev : {n : ℕ}  →  rev {suc n} ─ fromℕ n  ≡  rev {n}
  rev-end=rev {zero} = ≡.refl
  rev-end=rev {suc n} = {!!} -- ≡.cong (n ℕ∷_) rev-end=rev

{-
  rev˘=Id : {n : ℕ} → rev ˘  ≡  Id {n}
  rev˘=Id {zero} = ≡.refl
  rev˘=Id {suc n} = {!!} -- ≡.cong₂ _∷_ rev-end′ it

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
-}
\end{code}

\begin{code}
  -- Extensional Permutation equality
  infix 5 _≈ₚ_
  _≈ₚ_ : {n m : ℕ} (ps qs : Permutation n m) → Set (c ⊍ ℓ)
  _≈ₚ_ {n} ps qs  =  {xs : Seq n} → ps ◈ xs  ≈ₖ  qs ◈ xs

  -- This operation is involutionary: It is its own inverse.
  -- ˘˘ : {n : ℕ} {ps : Permutation n} → ps ˘ ˘  ≈ₚ  ps
  -- ˘˘ {zero} {nil} = ≈ₖ-refl
  -- ˘˘ {suc n} {cons p ps} {x ∷ xs} = {! FALSE: See test-rev˘˘!}

  -- The identity permutation is a fixed point.
  Id˘ : {n : ℕ} → Id ˘  ≈ₚ  Id {n}
  Id˘ {.0} {[]} = ≈ₖ-refl
  Id˘ {.(suc _)} {x ∷ xs} = {!!} -- cons ≈.refl Id˘
\end{code}
%}}}

  %{{{ cong properties

\begin{code}
  insert-cong₁ : {n : ℕ} {xs ys : Seq n} {i : Fin (1 + n)} {e : Carrier}
               → xs ≈ₖ ys → insert xs i e  ≈ₖ  insert ys i e
  insert-cong₁ {i = zero} xs≈ys = cons ≈.refl xs≈ys
  insert-cong₁ {i = suc _} nil              = ≈ₖ-refl
  insert-cong₁ {i = suc j} (cons x≈y xs≈ys) = cons x≈y (insert-cong₁ {i = j} xs≈ys)

  insert-cong₂ : {n : ℕ} {xs : Seq n} {i j : Fin (1 + n)} {e : Carrier}
               → i ≡ j → insert xs i e  ≈ₖ  insert xs j e
  insert-cong₂ ≡.refl = ≈ₖ-refl

  insert-cong₃ : {n : ℕ} {xs : Seq n} {i : Fin (1 + n)} {d e : Carrier}
               → e ≈ d → insert xs i e  ≈ₖ  insert xs i d
  insert-cong₃ {xs = []} {zero} e≈d = cons e≈d nil
  insert-cong₃ {xs = []} {suc ()} e≈d
  insert-cong₃ {xs = x ∷ xs} {zero} e≈d = cons e≈d ≈ₖ-refl
  insert-cong₃ {xs = x ∷ xs} {suc i} e≈d = cons ≈.refl (insert-cong₃ e≈d)

  ◈-cong₁ : {n m : ℕ} {ps qs : Permutation n m} {xs : Seq n}
          → ps ≈ₚ qs → ps ◈ xs ≈ₖ qs ◈ xs
  ◈-cong₁ eq = eq
  -- This is part of the definition of permutation equality.

  ◈-cong₂ : {n m : ℕ} {ps : Permutation n m} {xs ys : Seq n}
          → xs ≈ₖ ys → ps ◈ xs ≈ₖ ps ◈ ys
  ◈-cong₂ nil = ≈ₖ-refl
  ◈-cong₂ {ps = p ∷ ps} (cons {xs = xs} {ys = ys} x≈y eq)
    = {!!} -- ≈ₖ-trans (insert-cong₁ (◈-cong₂ eq)) (insert-cong₃ {_} {ps ◈ ys} {p} x≈y)
\end{code}
  %}}}

  %{{{ Properties of insertion and deletion for vectors
\edcomm{MA}{This section should live in something named |Vector.Setoid| since we are considering setoid
related artifacts of vectors.}

\begin{code}
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
          it = delete-suc {xs =  insert xs (suc i) e}

          indHyp : delete (insert xs (suc i) e) (suc i)  ≈ₖ  xs
          indHyp = delete-insert {i = suc i} {x = e}

          goal : delete (x ∷ insert xs (suc i) e) (suc (suc i)) ≈ₖ (x ∷ xs)
          goal = ≈ₖ-trans it (cons ≈.refl indHyp)

  insert-delete : {n : ℕ} {xs : Seq (suc n)} {i : Fin (suc n)}
                → insert (delete xs i) i (lookup i xs)  ≈ₖ  xs
  insert-delete {zero} {x ∷ xs} {zero} = ≈ₖ-refl
  insert-delete {zero} {x ∷ xs} {suc ()}
  insert-delete {suc n} {x ∷ xs} {zero} = ≈ₖ-refl
  insert-delete {suc n} {x ∷ xs} {suc i} = goal
    where it : delete (x ∷ xs) (suc i)  ≈ₖ  (x ∷ delete xs i)
          it = delete-suc {xs = xs}

          notice :    insert (x ∷ delete xs i) (suc i) (lookup i xs)
                   ≈ₖ (x ∷ insert (delete xs i) i (lookup i xs))
          notice = ≈ₖ-refl  -- by definition of |insert|

          indHyp :    insert (delete xs i) i (lookup i xs)
                   ≈ₖ  xs
          indHyp = insert-delete {i = i}

          goal :    insert (delete (x ∷ xs) (suc i)) (suc i) (lookup i xs)
                  ≈ₖ (x ∷ xs)
          goal = ≈ₖ-trans (insert-cong₁ {i = suc i} it) (cons ≈.refl indHyp)
\end{code}
%}}}
  %{{{ ◈ is a group action: It is an functorial in it's first argument.

\begin{code}
  ◈-leftId : {n : ℕ} {xs : Seq n} → Id ◈ xs  ≈ₖ  xs
  ◈-leftId {zero} {[]} = ≈ₖ-refl
  ◈-leftId {suc n} {x ∷ xs} = {!!} -- cons ≈.refl ◈-leftId

  -- Composition of permutations
  -- \edcomm{MA}{This particular form of typing is chosen so that |Permutation| acts as a morphism}
  -- type constructor for a category whose objects are natural numbers. Then this composition
  -- has the type necessary to make this into a category.
  infix 6 _⊙_
  _⊙_ : {n m r : ℕ} → Permutation n m → Permutation m r → Permutation n r
  [] ⊙ [] = []
  (p ∷ ps) ⊙ qs with homogeneity (p ∷ ps) | homogeneity qs
  (p ∷ ps) ⊙ qs | _≡_.refl | _≡_.refl = {!!} -- (qs at′ p) ∷ (ps ⊙ (qs ─ p))

  -- \edcomm{MA}{I made componentwise equality heterogenous in order to make the typing here more}
  -- general; yet it is not.
  ◈-compose : {n : ℕ} {ps : Permutation n n} {qs : Permutation n n}
            → {xs : Seq n} → (ps ⊙ qs) ◈ xs  ≈ₖ  ps ◈ (qs ◈ xs)
  ◈-compose = {!!}
\end{code}

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

%}}}

Expected definition,
\begin{code}
  module FirstAttempt where
    data _≈₁_ {n m : ℕ} (xs : Seq n) (ys : Seq m) : Set (c ⊍ ℓ) where
      yes : (p : Permutation n m) → p ◈ xs ≈ₖ ys → xs ≈₁ ys
    
    ≈₁-refl :  {n  : ℕ}{xs : Seq n} → xs ≈₁ xs
    ≈₁-refl {n} {xs} = yes Id Id-◈
    
    ≈₁-sym : {n m : ℕ}{xs : Seq n} {ys : Seq m} → xs ≈₁ ys → ys ≈₁ xs
    ≈₁-sym {n} {m} {xs} {ys} (yes p x) = {! Would need to use inversion here! !}
    
   -- ≈₁-trans : {n m r : ℕ}{xs : Seq n} {ys : Seq m} {zs : Seq r} → xs ≈₁ ys → ys ≈₁ zs → xs ≈₁ zs
    ≈₁-trans : {n : ℕ}{xs ys zs : Seq n} → xs ≈₁ ys → ys ≈₁ zs → xs ≈₁ zs
    ≈₁-trans (yes p p◈xs≈ys) (yes q q◈ys≈zs) = yes (q ⊙ p)
      (≈ₖ-trans ◈-compose (≈ₖ-trans (◈-cong₂ p◈xs≈ys) q◈ys≈zs))
    
    ≈₁-isEquivalence : {n : ℕ} → IsEquivalence (_≈₁_ {n} {n})
    ≈₁-isEquivalence {n} = record { refl = ≈₁-refl ; sym = ≈₁-sym ; trans = ≈₁-trans }
    
    ≈₁-∷-cong₂ : {n m : ℕ} {xs : Seq n} {ys : Seq n} {e : Carrier} → xs ≈₁ ys → (e ∷ xs) ≈₁ (e ∷ ys)
    ≈₁-∷-cong₂ eq = {!!}
\end{code}

However this does not fit in with our needs in |Bag.lagda|, so we work with a bit of
an awkward definition. \edcomm{MA}{Perhaps we could have a transform between the two forms?}

\begin{code}
    List = Σ n ∶ ℕ • Seq n
    
    length : List → ℕ
    length (n , xs) = n
    
    seq : (l : List) → Seq (length l)
    seq (n , xs) = xs
    
    data _≈₂_ (xs ys : List) : Set (c ⊍ ℓ) where
      yes : (p : Permutation (length xs) (length ys)) → p ◈ seq xs ≈ₖ seq ys → xs ≈₂ ys
    
    to-awkward : {m n : ℕ} {xs : Seq n} {ys : Seq m} → m ≡ n → xs ≈₁ ys → (n , xs) ≈₂ (m , ys)
    to-awkward ≡.refl (yes p p◈xs≈ys) = yes p p◈xs≈ys
    
    ≈₂-refl :  {xs : List} → xs ≈₂ xs
    ≈₂-refl = to-awkward ≡.refl ≈₁-refl
    
    ≈₂-sym : {xs ys : List} → xs ≈₂ ys → ys ≈₂ xs
    ≈₂-sym (yes p p◈xs≈ys) = to-awkward (homogeneity p) (≈₁-sym (yes p p◈xs≈ys))
    
    ≈₂-trans : {xs ys zs : List} → xs ≈₂ ys → ys ≈₂ zs → xs ≈₂ zs
    ≈₂-trans (yes p x) (yes q x₁) with homogeneity p | homogeneity q
    ...| ≡.refl | ≡.refl = to-awkward ≡.refl (≈₁-trans (yes p x) (yes q x₁))
    
    -- MA: The following will not work due to the poor typing of ≈₂-trans:
    -- |to-awkward (≡.sym (homogeneity p ⟨≡≡⟩ homogeneity q)) (≈₂-trans ? ?)|
    
    ≈₂-isEquivalence : IsEquivalence _≈₂_
    ≈₂-isEquivalence = record { refl = ≈₂-refl ; sym = ≈₂-sym ; trans = ≈₂-trans }  
    
    ε : List
    ε = (0 , [])
    
    _⊕_ : List → List → List
    (_ , xs) ⊕ (_ , ys) = (_ , xs ++ ys)
    
    -- not-so-strangely properties about Vec catenation are not in the standard library
    -- since they would involve much usage of subst due to the alteration of vector sizes.
    -- Perhaps take a glance at Data.Vec.Equality.
    
    ⊕-left-unit : ∀ ys → (ε ⊕ ys) ≈₂ ys
    ⊕-left-unit ys = ≈₂-refl
    
    -- ++-right-unit : {n : ℕ} {xs : Seq n} → xs ++ [] ≈ₖ xs
    -- ++-right-unit {xs = xs} = {!!}
    
    ⊕-right-unit : ∀ ys → (ys ⊕ ε) ≈₂ ys
    ⊕-right-unit (.0 , []) = ≈₂-refl
    ⊕-right-unit (.(suc _) , x ∷ proj₄) = to-awkward (≡.cong suc (≡.sym (+-right-identity _)))
                 {!≈₁-∷-cong₂ ?!}
\end{code}

\begin{code}
  open import Data.List
  Seq∞ = List Carrier

  record _≈₃_ (xs ys : List Carrier) : Set (c ⊍ ℓ) where
    field
      witness : Permutation (length xs) (length ys)
      proof   : witness ◈ (fromList xs) ≈ₖ fromList ys

  ≈₃-reflexive : {xs ys : Seq∞} → xs ≡ ys → xs ≈₃ ys
  ≈₃-reflexive ≡.refl = record { witness = Id ; proof = ◈-leftId   }

  ≈₃-refl :  {xs : Seq∞} → xs ≈₃ xs
  ≈₃-refl = ≈₃-reflexive ≡.refl

  ≈₃-sym : {xs ys : Seq∞} → xs ≈₃ ys → ys ≈₃ xs
  ≈₃-sym record { witness = witness ; proof = proof } = record { witness = witness ˘ ; proof = {!!} }

  postulate ≈₃-trans : {xs ys zs : Seq∞} → xs ≈₃ ys → ys ≈₃ zs → xs ≈₃ zs

  ≈₃-isEquivalence : IsEquivalence _≈₃_
  ≈₃-isEquivalence = record { refl = ≈₃-refl ; sym = ≈₃-sym ; trans = ≈₃-trans }

  singleton-≈ : {x y : Carrier} → x ≈ y → (x ∷ []) ≈₃ (y ∷ [])
  singleton-≈ x≈y = record { witness = Id ; proof = VecEquality.cons x≈y nil }
\end{code}

%{{{ approach via vectors rather than lists

\begin{spec}
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
\end{spec}


\begin{spec}
  -- fold is a setoid homomorphism

  fold : Seq∞ → Carrier
  fold = foldr _*_ e

  open import Data.Vec using (fromList)

  fold-cong : {xs ys : Seq∞} → xs ≈ₚ ys → fold xs ≈ fold ys
  fold-cong {[]} {[]} record { lengths = ≡.refl ; witness = witness ; proof = proof } = refl
  fold-cong {[]} {x ∷ ys} record { lengths = () ; witness = witness ; proof = proof }
  fold-cong {x ∷ xs} {[]} record { lengths = () ; witness = witness ; proof = proof }
  fold-cong {x ∷ xs} {x₁ ∷ ys} record { lengths = lengths ; witness = (Permutations.cons zero witness) ; proof = proof } = {!!}
  fold-cong {x ∷ xs} {x₁ ∷ ys} record { lengths = lengths ; witness = (Permutations.cons (suc p) witness) ; proof = proof } = {!!}

\end{spec}
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
