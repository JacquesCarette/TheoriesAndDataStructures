{-# OPTIONS --without-K #-}

module Helpers.FinNatLemmas where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (m+n∸n≡m; m≤m+n; +-∸-assoc; cancel-+-left; module ≤-Reasoning)
open import Data.Nat.Properties.Simple
  using (+-comm; +-assoc; *-comm; distribʳ-*-+; +-right-identity)

open import Data.Fin
  using (Fin; zero; suc; toℕ; raise; fromℕ≤; reduce≥; inject+)
open import Data.Fin.Properties
  using (bounded; toℕ-injective; toℕ-raise; toℕ-fromℕ≤; inject+-lemma)

open import Relation.Binary using (module StrictTotalOrder)
open import Relation.Binary.Core using (_≢_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; refl; sym; cong; cong₂; trans; module ≡-Reasoning)

------------------------------------------------------------------------------
-- Fin and Nat lemmas

toℕ-fin : (m n : ℕ) → (eq : m ≡ n) (fin : Fin m) →
  toℕ (subst Fin eq fin) ≡ toℕ fin
toℕ-fin m .m refl fin = refl

∸≡ : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  toℕ i ∸ m ≡ toℕ j ∸ m → i ≡ j
∸≡ m n i j i≥ j≥ p = toℕ-injective pr
  where pr = begin (toℕ i
                    ≡⟨ sym (m+n∸n≡m (toℕ i) m) ⟩
                    (toℕ i + m) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm (toℕ i) m) ⟩
                    (m + toℕ i) ∸ m
                    ≡⟨ +-∸-assoc m i≥ ⟩
                    m + (toℕ i ∸ m)
                    ≡⟨ cong (λ x → m + x) p ⟩
                    m + (toℕ j ∸ m)
                    ≡⟨ sym (+-∸-assoc m j≥) ⟩
                    (m + toℕ j) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm m (toℕ j)) ⟩
                    (toℕ j + m) ∸ m
                    ≡⟨ m+n∸n≡m (toℕ j) m ⟩
                    toℕ j ∎)
             where open ≡-Reasoning

cancel-right∸ : (m n k : ℕ) (k≤m : k ≤ m) (k≤n : k ≤ n) →
  (m ∸ k ≡ n ∸ k) → m ≡ n
cancel-right∸ m n k k≤m k≤n mk≡nk =
  begin (m
         ≡⟨ sym (m+n∸n≡m m k) ⟩
         (m + k) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm m k) ⟩
         (k + m) ∸ k
         ≡⟨ +-∸-assoc k k≤m ⟩
         k + (m ∸ k)
         ≡⟨ cong (λ x → k + x) mk≡nk ⟩
         k + (n ∸ k)
         ≡⟨ sym (+-∸-assoc k k≤n) ⟩
         (k + n) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm k n) ⟩
         (n + k) ∸ k
         ≡⟨ m+n∸n≡m n k ⟩
         n ∎)
  where open ≡-Reasoning

raise< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) →
         toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<))) ≡ n + toℕ i
raise< m n i i< =
  begin (toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (raise n (fromℕ≤ i<)) ⟩
         toℕ (raise n (fromℕ≤ i<))
         ≡⟨ toℕ-raise n (fromℕ≤ i<) ⟩
         n + toℕ (fromℕ≤ i<)
         ≡⟨ cong (λ x → n + x) (toℕ-fromℕ≤ i<) ⟩
         n + toℕ i ∎)
  where open ≡-Reasoning

toℕ-reduce≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
               toℕ (reduce≥ i i≥) ≡ toℕ i ∸ m
toℕ-reduce≥ 0 n i _ = refl
toℕ-reduce≥ (suc m) n zero ()
toℕ-reduce≥ (suc m) n (suc i) (s≤s i≥) = toℕ-reduce≥ m n i i≥

inject≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
        toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))) ≡ toℕ i ∸ m
inject≥ m n i i≥ =
  begin (toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (inject+ m (reduce≥ i i≥)) ⟩
         toℕ (inject+ m (reduce≥ i i≥))
         ≡⟨ sym (inject+-lemma m (reduce≥ i i≥)) ⟩
         toℕ (reduce≥ i i≥)
         ≡⟨ toℕ-reduce≥ m n i i≥ ⟩
         toℕ i ∸ m ∎)
  where open ≡-Reasoning

fromℕ≤-inj : (m n : ℕ) (i j : Fin n) (i< : toℕ i < m) (j< : toℕ j < m) →
  fromℕ≤ i< ≡ fromℕ≤ j< → i ≡ j
fromℕ≤-inj m n i j i< j< fi≡fj =
  toℕ-injective
    (trans (sym (toℕ-fromℕ≤ i<)) (trans (cong toℕ fi≡fj) (toℕ-fromℕ≤ j<)))

reduce≥-inj : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  reduce≥ i i≥ ≡ reduce≥ j j≥ → i ≡ j
reduce≥-inj m n i j i≥ j≥ ri≡rj =
  toℕ-injective
    (cancel-right∸ (toℕ i) (toℕ j) m i≥ j≥
      (trans (sym (toℕ-reduce≥ m n i i≥))
      (trans (cong toℕ ri≡rj) (toℕ-reduce≥ m n j j≥))))

inj₁-toℕ≡ : {m n : ℕ} (i : Fin (m + n)) (i< : toℕ i < m) →
            toℕ i ≡ toℕ (inject+ n (fromℕ≤ i<))
inj₁-toℕ≡ {0} _ ()
inj₁-toℕ≡ {suc m} zero (s≤s z≤n) = refl
inj₁-toℕ≡ {suc (suc m)} (suc i) (s≤s (s≤s i<)) = cong suc (inj₁-toℕ≡ i (s≤s i<))

inj₁-≡ : {m n : ℕ} (i : Fin (m + n)) (i< : toℕ i < m) → i ≡ inject+ n (fromℕ≤ i<)
inj₁-≡ i i< = toℕ-injective (inj₁-toℕ≡ i i<)

inj₂-toℕ≡ :  {m n : ℕ} (i : Fin (m + n)) (i≥ : m ≤ toℕ i ) →
             toℕ i ≡ toℕ (raise m (reduce≥ i i≥))
inj₂-toℕ≡ {Data.Nat.zero} i i≥ = refl
inj₂-toℕ≡ {suc m} zero ()
inj₂-toℕ≡ {suc m} (suc i) (s≤s i≥) = cong suc (inj₂-toℕ≡ i i≥)

inj₂-≡ :  {m n : ℕ} (i : Fin (m + n)) (i≥ : m ≤ toℕ i ) → i ≡ raise m (reduce≥ i i≥)
inj₂-≡ i i≥ = toℕ-injective (inj₂-toℕ≡ i i≥)

inject+-injective : {m n : ℕ} (i j : Fin m) → (inject+ n i ≡ inject+ n j) → i ≡ j
inject+-injective {m} {n} i j p = toℕ-injective pf
  where
    open ≡-Reasoning
    pf : toℕ i ≡ toℕ j
    pf = begin (
      toℕ i
          ≡⟨ inject+-lemma n i ⟩
      toℕ (inject+ n i)
          ≡⟨ cong toℕ p ⟩
      toℕ (inject+ n j)
          ≡⟨ sym (inject+-lemma n j) ⟩
      toℕ j ∎)

raise-injective : {m n : ℕ} (i j : Fin n) → (raise m i ≡ raise m j) → i ≡ j
raise-injective {m} {n} i j p = toℕ-injective (cancel-+-left m pf)
  where
    open ≡-Reasoning
    pf : m + toℕ i ≡ m + toℕ j
    pf = begin (
      m + toℕ i
        ≡⟨ sym (toℕ-raise m i)  ⟩
      toℕ (raise m i)
        ≡⟨ cong toℕ p ⟩
      toℕ (raise m j)
        ≡⟨ toℕ-raise m j ⟩
      m + toℕ j ∎)

toℕ-invariance : ∀ {n n'} → (i : Fin n) → (eq : n ≡ n') → toℕ (subst Fin eq i) ≡ toℕ i
toℕ-invariance i refl = refl

-- see FinEquiv for the naming

inject+0≡uniti+ : ∀ {m} → (n : Fin m) → (eq : m ≡ m + 0) → inject+ 0 n ≡ subst Fin eq n
inject+0≡uniti+ {m} n eq = toℕ-injective pf
  where
    open ≡-Reasoning
    pf : toℕ (inject+ 0 n) ≡ toℕ (subst Fin eq n)
    pf = begin (
      toℕ (inject+ 0 n)
        ≡⟨ sym (inject+-lemma 0 n) ⟩
      toℕ n
        ≡⟨ sym (toℕ-invariance n eq) ⟩
      toℕ (subst Fin eq n) ∎)

-- Following code taken from
-- https://github.com/copumpkin/derpa/blob/master/REPA/Index.agda#L210

-- the next few bits are lemmas to prove uniqueness of euclidean division

-- first : for nonzero divisors, a nonzero quotient would require a larger
-- dividend than is consistent with a zero quotient, regardless of
-- remainders.

large : ∀ {d} {r : Fin (suc d)} x (r′ : Fin (suc d)) →
        toℕ r ≢ suc x * suc d + toℕ r′
large {d} {r} x r′ pf = irrefl pf (
    start
      suc (toℕ r)
    ≤⟨ bounded r ⟩
      suc d
    ≤⟨ m≤m+n (suc d) (x * suc d) ⟩
      suc d + x * suc d -- same as (suc x * suc d)
    ≤⟨ m≤m+n (suc x * suc d) (toℕ r′) ⟩
      suc x * suc d + toℕ r′ -- clearer in two steps; we'd need assoc anyway
    □)
  where
  open ≤-Reasoning
    renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
  open Relation.Binary.StrictTotalOrder Data.Nat.Properties.strictTotalOrder

-- a raw statement of the uniqueness, in the arrangement of terms that's
-- easiest to work with computationally

addMul-lemma′ : ∀ x x′ d (r r′ : Fin (suc d)) →
  x * suc d + toℕ r ≡ x′ * suc d + toℕ r′ → r ≡ r′ × x ≡ x′
addMul-lemma′ zero zero d r r′ hyp = (toℕ-injective hyp) , refl
addMul-lemma′ zero (suc x′) d r r′ hyp = ⊥-elim (large x′ r′ hyp)
addMul-lemma′ (suc x) zero d r r′ hyp = ⊥-elim (large x r (sym hyp))
addMul-lemma′ (suc x) (suc x′) d r r′ hyp
                      rewrite +-assoc (suc d) (x * suc d) (toℕ r)
                            | +-assoc (suc d) (x′ * suc d) (toℕ r′)
                      with addMul-lemma′ x x′ d r r′ (cancel-+-left (suc d) hyp)
... | pf₁ , pf₂ = pf₁ , cong suc pf₂

-- and now rearranged to the order that Data.Nat.DivMod uses

addMul-lemma : ∀ x x′ d (r r′ : Fin (suc d)) →
  toℕ r + x * suc d ≡ toℕ r′ + x′ * suc d → r ≡ r′ × x ≡ x′
addMul-lemma x x′ d r r′ hyp rewrite +-comm (toℕ r) (x * suc d)
                                   | +-comm (toℕ r′) (x′ * suc d)
  = addMul-lemma′ x x′ d r r′ hyp

-- purely about Nat, but still not in Data.Nat.Properties.Simple

distribˡ-*-+ : ∀ m n o → m * (n + o)  ≡ m * n + m * o
distribˡ-*-+ m n o =
  trans (*-comm m (n + o)) (
  trans (distribʳ-*-+ m n o) (
        (cong₂ _+_ (*-comm n m) (*-comm o m))))

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n = trans (*-comm n 1) (+-right-identity n)

------------------------------------------------------------------------
