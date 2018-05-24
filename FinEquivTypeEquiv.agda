{-# OPTIONS --without-K #-}

module FinEquivTypeEquiv where

-- The goal is to establish that finite sets and equivalences form a
-- commutative semiring.

import Level using (zero)

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)

open import Relation.Binary using (IsEquivalence)
open import Algebra using (CommutativeSemiring)
open import Algebra.Structures
  using (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)

open import Equiv using (_≃_; id≃; sym≃; trans≃; _●_; _⊎≃_; _×≃_)
open import TypeEquiv
  using (assocl₊equiv; unite₊equiv; unite₊′equiv; swap₊equiv;
         unite⋆equiv; unite⋆′equiv; swap⋆equiv; assocl⋆equiv;
         distzequiv; distzrequiv; distequiv; distlequiv)

open import FinEquivPlusTimes using (F0≃⊥; module Plus; Fin1≃⊤; module Times)
open Plus using (+≃⊎; ⊎≃+)
open Times using (*≃×; ×≃*)

------------------------------------------------------------------------------
-- This is the relation we are interested in showing is a commutative
-- semiring.

_fin≃_ : (m n : ℕ) → Set
m fin≃ n = Fin m ≃ Fin n

------------------------------------------------------------------------------
-- Additive monoid

module PlusE where

  infix 9 _+F_

  -- additive monoid equivalences

  -- unite+

  unite+ : {m : ℕ} → Fin (0 + m) ≃ Fin m
  unite+ = unite₊equiv ● F0≃⊥ {Level.zero} ⊎≃ id≃ ● +≃⊎

  -- and on the other side as well

  unite+r : {m : ℕ} → Fin (m + 0) ≃ Fin m
  unite+r = unite₊′equiv ● id≃ ⊎≃ F0≃⊥ {Level.zero} ● +≃⊎

  -- swap₊

  swap+ : {m n : ℕ} → Fin (m + n) ≃ Fin (n + m)
  swap+ {m} = ⊎≃+ ● swap₊equiv ● +≃⊎ {m}

  -- associativity

  assocl+ : {m n o : ℕ} → Fin (m + (n + o)) ≃ Fin ((m + n) + o)
  assocl+ {m} = ⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎ {m}

  -- congruence

  _+F_ : {m n o p : ℕ} → (Fin m ≃ Fin n) → (Fin o ≃ Fin p) →
              Fin (m + o) ≃ Fin (n + p)
  Fm≃Fn +F Fo≃Fp = ⊎≃+ ● Fm≃Fn ⊎≃ Fo≃Fp ● +≃⊎

  uniti+ : {m : ℕ} → Fin m ≃ Fin (0 + m)
  uniti+ = sym≃ unite+

  uniti+r : {m : ℕ} → Fin m ≃ Fin (m + 0)
  uniti+r = sym≃ unite+r

  assocr+ : {m n o : ℕ} → Fin ((m + n) + o) ≃ Fin (m + (n + o))
  assocr+ {m} = sym≃ (assocl+ {m})

  sswap+ : {m n : ℕ} → Fin (n + m) ≃ Fin (m + n)
  sswap+ {m} {n} = sym≃ (swap+ {m} {n})

-----------------------------------------------------------------------------
-- Multiplicative monoid

module TimesE where

  infixl 7 _*F_

  -- multiplicative monoid equivalences

  -- unite*

  unite* : {m : ℕ} → Fin (1 * m) ≃ Fin m
  unite* {m} = unite⋆equiv ● Fin1≃⊤ {Level.zero} ×≃ id≃ ● *≃×

  -- unite*r

  unite*r : {m : ℕ} → Fin (m * 1) ≃ Fin m
  unite*r {m} = unite⋆′equiv ● id≃ ×≃ Fin1≃⊤ {Level.zero} ● *≃×

  -- swap*

  swap* : {m n : ℕ} → Fin (m * n) ≃ Fin (n * m)
  swap* {m} {n} = ×≃* ● swap⋆equiv ● *≃× {m}

  -- associativity

  assocl* : {m n o : ℕ} → Fin (m * (n * o)) ≃ Fin ((m * n) * o)
  assocl* {m} {n} {o} = ×≃* ● ×≃* ×≃ id≃ ● assocl⋆equiv ● id≃ ×≃ *≃× ● *≃× {m}

  -- congruence

  _*F_ : {m n o p : ℕ} → Fin m ≃ Fin n → Fin o ≃ Fin p →
              Fin (m * o) ≃ Fin (n * p)
  Fm≃Fn *F Fo≃Fp = ×≃* ● Fm≃Fn ×≃ Fo≃Fp ● *≃×

  uniti* : {m : ℕ} → Fin m ≃ Fin (1 * m)
  uniti* = sym≃ unite*

  uniti*r : {m : ℕ} → Fin m ≃ Fin (m * 1)
  uniti*r = sym≃ unite*r

  assocr* : {m n o : ℕ} → Fin ((m * n) * o) ≃ Fin (m * (n * o))
  assocr* {m} {n} {o} = sym≃ (assocl* {m})

  sswap* : {m n : ℕ} → Fin (n * m) ≃ Fin (m * n)
  sswap* {m} {n} = sym≃ (swap* {m} {n})

------------------------------------------------------------------------------
-- Distributivity of multiplication over addition

module PlusTimesE where

  -- now that we have two monoids, we need to check distributivity

  -- note that the sequence below is "logically right", *but* could be
  -- replaced by id≃ !
  distz : {m : ℕ} → Fin (0 * m) ≃ Fin 0
  distz {m} = sym≃ F0≃⊥ ● distzequiv ● F0≃⊥ {Level.zero} ×≃ id≃ ● *≃× {0} {m}
    where open Times

  distzr : {m : ℕ} → Fin (m * 0) ≃ Fin 0
  distzr {m} = sym≃ F0≃⊥ ● distzrequiv ● id≃ ×≃ F0≃⊥ {Level.zero} ● *≃× {m} {0}
    where open Times

  dist : {m n o : ℕ} → Fin ((m + n) * o) ≃ Fin ((m * o) + (n * o))
  dist {m} {n} {o} = ⊎≃+ {m * o} {n * o} ● ×≃* {m} ⊎≃ ×≃* ● distequiv ● +≃⊎ ×≃ id≃ ● *≃×
    where open Times
          open Plus

  distl : {m n o : ℕ} → Fin (m * (n + o)) ≃ Fin ((m * n) + (m * o))
  distl {m} {n} {o} = ⊎≃+ {m * n} {m * o} ● ×≃* {m} ⊎≃ ×≃* ● distlequiv ● id≃ ×≃ +≃⊎ ● *≃×
    where open Plus
          open Times

  factorzr : {n : ℕ} → Fin 0 ≃ Fin (n * 0)
  factorzr {n} = sym≃ (distzr {n})

  factorz : {m : ℕ} → Fin 0 ≃ Fin (0 * m)
  factorz {m} = sym≃ (distz {m})

  factor : {m n o : ℕ} → Fin ((m * o) + (n * o)) ≃ Fin ((m + n) * o)
  factor {m} = sym≃ (dist {m})

  factorl : {m n o : ℕ} → Fin ((m * n) + (m * o)) ≃ Fin (m * (n + o))
  factorl {m} = sym≃ (distl {m})

------------------------------------------------------------------------------
-- Summarizing... we have a commutative semiring structure

fin≃IsEquiv : IsEquivalence _fin≃_
fin≃IsEquiv = record {
  refl = id≃ ;
  sym = sym≃ ;
  trans = trans≃
  }

finPlusIsSG : IsSemigroup _fin≃_ _+_
finPlusIsSG = record {
  isEquivalence = fin≃IsEquiv ;
  assoc = λ m n o → PlusE.assocr+ {m} {n} {o} ;
  ∙-cong = PlusE._+F_
  }

finTimesIsSG : IsSemigroup _fin≃_ _*_
finTimesIsSG = record {
  isEquivalence = fin≃IsEquiv ;
  assoc = λ m n o → TimesE.assocr* {m} {n} {o} ;
  ∙-cong = TimesE._*F_
  }

finPlusIsCM : IsCommutativeMonoid _fin≃_ _+_ 0
finPlusIsCM = record {
  isSemigroup = finPlusIsSG ;
  identityˡ = λ m → id≃ ;
  comm = λ m n → PlusE.swap+ {m} {n}
  }

finTimesIsCM : IsCommutativeMonoid _fin≃_ _*_ 1
finTimesIsCM = record {
  isSemigroup = finTimesIsSG ;
  identityˡ = λ m → TimesE.unite* {m} ;
  comm = λ m n → TimesE.swap* {m} {n}
  }

finIsCSR : IsCommutativeSemiring _fin≃_ _+_ _*_ 0 1
finIsCSR = record {
  +-isCommutativeMonoid = finPlusIsCM ;
  *-isCommutativeMonoid = finTimesIsCM ;
  distribʳ = λ o m n → PlusTimesE.dist {m} {n} {o} ;
  zeroˡ = λ m → PlusTimesE.distz {m}
  }

finCSR : CommutativeSemiring Level.zero Level.zero
finCSR = record {
  Carrier = ℕ ;
  _≈_ = _fin≃_ ;
  _+_ = _+_ ;
  _*_ = _*_ ;
  0# = 0 ;
  1# = 1 ;
  isCommutativeSemiring = finIsCSR
  }

------------------------------------------------------------------------------
