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

open import DataProperties hiding (⟨_,_⟩)
open import ParComp
open import EqualityCombinators
open import Belongs
open import Structures.CommMonoid renaming (Hom to CMArrow)

open import Data.Nat.Properties using (≤-steps ; n≤1+n)

open import Data.List using (monoid)
open import Data.Fin using (fromℕ)

open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
-- open CommMonoid using (eq-in ; isCommMonoid)
\end{code}
%}}}

%{{{ approach via vectors rather than lists

\begin{code}
module Lemmas {l c : Level} {𝒮 : Setoid c l} {𝒞 : CommMonoid 𝒮} where

  open CommMonoid 𝒞
  open IsCommutativeMonoid isCommMonoid -- \edcomm{MA}{The field name really oughtn't be abbreviated!}

  open import Data.Vec
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold ; _≤_)

  -- Sequences
  open Setoid 𝒮
  Seq = Vec Carrier

  -- `k`omponent-wise equality on sequences ;; MA: Subscript `c` not directly available.
  infix 5 _≈ₖ_  
  data _≈ₖ_ : {n : ℕ} → Seq n → Seq n → Set (c ⊍ l) where
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

\begin{code}  
  -- fold is a setoid homomorphism

  fold : {n : ℕ} → Seq n → Carrier
  fold = foldr (λ _ → Carrier) _*_ e

  fold-cong : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong {_} {[]} {.[]} nil = refl
  fold-cong {_} {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.
\end{code}

The following is inspired by copumkin & vmchale's libraries.

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
  permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
  permute nil [] = []
  permute (cons p ps) (x ∷ xs) = insert (permute ps xs) p x

  infix 6 _◈_
  _◈_ = permute
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

  id : {n : ℕ} → Permutation n
  id = rotate 0
  -- I.e., insertions at position 0 only; since 0 rotations needed.  

  -- rev {n} = rotate n {0} -- we need to use subst to obtain |n + 0 ≡ n|
  -- A direct implementation is then clearer.
  rev : {n : ℕ} → Permutation n
  rev {zero}  = nil
  rev {suc n} = cons (fromℕ n) rev
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

%{{{ Relationship between Vec and Permutation
\begin{code}
  -- Notice that |Permutation n| is similar to, but distinct from, |Vec (Fin (suck n)) n|.
  -- More accurately, as in the traditional sense of the concept,
  -- |Permutation n ≅ (Π i : 0..n-1 • Fin (n ∸ i))|; cf |_at_| below.
  toVec : {n : ℕ} → Permutation n → Vec ℕ n
  toVec nil         = []
  toVec (cons p ps) = toℕ p ∷ toVec ps

  _at_ : {n : ℕ} → Permutation n → (i : Fin n) → Fin (n ∸ toℕ i)
  cons p ps at zero   =  p
  cons p ps at suc i  =  ps at i

  _at′_ : {n : ℕ} → Permutation n → Fin n → Fin n
  cons p p₁ at′ zero = p
  cons p p₁ at′ suc i = inject≤ (p₁ at′ i) (n≤1+n _)
\end{code}
%}}}

%{{{ Inversion of permutations: deleteP and _˘
\begin{code}
  -- Deletion for permutations: |PS : Perm (suc n) ↦ psᵢ ∸ 1 : Perm n| ?
  -- [p₁, …, pₙ] ↦ [p₁ ∸ 1, …, pᵢ₋₁ ∸ 1, pᵢ₊₁ ∸1, …, pₙ ∸ 1]
  deleteP : {n : ℕ} → Fin (suc n) → Permutation (suc n) → Permutation n
  deleteP {n} zero (cons p ps) = ps
  deleteP {zero} (suc ()) ps
  deleteP {suc n} (suc i) (cons zero ps) = cons zero (deleteP i ps)
  deleteP {suc n} (suc i) (cons (suc p) ps) = cons p (deleteP i ps)

-- Where is mine hero in shining logical armor?
-- 
--   deleteP-spec : {n : ℕ} {i : Fin (suc n)} {ps : Permutation (suc (suc n))}
--                → toℕ ( (deleteP (suc i) ps) at i) ≡ toℕ (ps at (suc i)) ∸ 1
--   deleteP-spec {zero} {zero} {cons zero (cons zero nil)} = ≡.refl
--   deleteP-spec {zero} {suc ()} {cons zero (cons zero nil)}
--   deleteP-spec {zero} {zero} {cons (suc zero) (cons zero nil)} = ≡.refl
--   deleteP-spec {zero} {suc ()} {cons (suc zero) (cons zero nil)}
--   deleteP-spec {zero} {i} {cons (suc (suc ())) (cons zero nil)}
--   deleteP-spec {zero} {i} {cons p (cons (suc ()) ps)}
--   deleteP-spec {suc n} {zero} {cons zero (cons p ps)} = {! shakka when the walls fell!}
--   deleteP-spec {suc n} {suc i} {cons zero ps} = {!!}
--   deleteP-spec {suc n} {i} {cons (suc p) ps} = {!!}

  -- Permutations come with the obvious involution, but non-trivial implementation
  _˘ : {n : ℕ} → Permutation n → Permutation n
  _˘ {zero }     nil          = nil
  _˘ {suc n} ps@(cons p ps′) = cons 𝓅 ( (deleteP 𝒑 ps)˘ )
    where 𝓅 : Fin (suc n)
          𝓅 = ps at′ p

          𝒑 : Fin (suc n)
          𝒑 = ps at′ 𝓅

  test₆ : (rev ˘) ◈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test₆ = ≡.refl

  rev˘≈Id : {n : ℕ} {xs : Seq n} → rev ˘ ◈ xs  ≡  xs
  rev˘≈Id {n} {xs} = {!!}

  -- Extensional Permutation equality
  infix 5 _≈ₚ_
  _≈ₚ_ : {n : ℕ} (ps qs : Permutation n) → Set (c ⊍ l)
  _≈ₚ_ {n} ps qs  =  {xs : Seq n} → ps ◈ xs  ≈ₖ  qs ◈ xs

  -- This operation is involutionary: It is its own inverse.
  ˘˘ : {n : ℕ} {ps : Permutation n} → ps ˘ ˘  ≈ₚ  ps
  ˘˘ {zero} {nil} = ≈ₖ-refl
  ˘˘ {suc n} {cons p ps} {x ∷ xs} = {! Lord, give me strength.!}

  -- The identity permutation is a fixed point.
  Id˘ : {n : ℕ} → id ˘  ≈ₚ  id {n}
  Id˘ {.0} {[]} = ≈ₖ-refl
  Id˘ {.(suc _)} {x ∷ xs} = cons ≈.refl Id˘
\end{code}
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
  ◈-leftId : {n : ℕ} {xs : Seq n} → id ◈ xs  ≈ₖ  xs
  ◈-leftId {zero} {[]} = ≈ₖ-refl
  ◈-leftId {suc n} {x ∷ xs} = cons ≈.refl ◈-leftId

  -- Composition of permutations
  infix 6 _⊙_
  _⊙_ : {n : ℕ} → Permutation n → Permutation n → Permutation n
  nil ⊙ qs        =  qs
  cons p ps ⊙ qs  =  cons (qs at′ p) (ps ⊙ deleteP p qs)
  
  -- The inversion operation is contravariant: It reverses composition.
  ◈-˘ : {n : ℕ} {ps qs : Permutation n} → (ps ⊙ qs)˘  ≈ₚ (qs ˘ ⊙ ps ˘)
  ◈-˘ = {!!}

  insert-◈ : {n : ℕ} {ps : Permutation n} {q : Fin (suc n)} {qs : Permutation n}
             {xs : Seq n} {x : Carrier}
           → insert (ps ◈ (qs ◈ xs)) q x  ≈ₖ  (cons zero ps) ◈ (insert (qs ◈ xs) q x)
  insert-◈ {n} {ps} {q} {qs} {xs} = {!!}

  ◈-compose : {n : ℕ} {ps qs : Permutation n} {xs : Seq n} → (ps ⊙ qs) ◈ xs  ≈ₖ  ps ◈ (qs ◈ xs)
  ◈-compose {.0} {nil} {nil} {[]} = ≈ₖ-refl
  ◈-compose {.(suc _)} {cons zero ps} {cons q qs} {x ∷ xs} = ≈ₖ-trans (insert-cong ◈-compose) insert-◈
  ◈-compose {.(suc _)} {cons (suc p) ps} {cons q qs} {x ∷ xs} = {!!}
\end{code}

%}}}

%{{{ the pesky-hole from the summer
\begin{code}
  data _≈ᵥ_ {n : ℕ} (xs : Seq n) (ys : Seq n) : Set (c ⊍ l) where
    yes : (p : Permutation n) → permute p xs ≈ₖ ys → xs ≈ᵥ ys

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

  proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n} → fold xs ≈ fold (permute p xs) 
  proposition₁ {.0} {[]} {nil} = refl
  proposition₁ {.(suc _)} {x ∷ xs} {cons zero ps} = refl ⟨∙⟩ proposition₁
  proposition₁ {.(suc _)} {x ∷ xs} {cons (suc p) ps} with permute ps xs | inspect (permute ps) xs
  proposition₁ {.(suc 0)} {x ∷ xs} {cons (suc ()) ps} | [] | _
  proposition₁ {.(suc (suc _))} {x ∷ xs} {cons (suc p) ps} | x′ ∷ xs′ | [ ps-on-xs≈xs′ ] = begin⟨ 𝒮 ⟩
      x * fold xs
    ≈⟨ refl ⟨∙⟩ proposition₁ ⟩
      x * fold (permute ps xs)
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
\end{code}  
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
