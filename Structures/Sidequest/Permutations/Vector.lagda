\section{Structures.Sidequest.Permutations}

‼ THIS HAS A POSTULATE ‼

Documenting the relationship between |Vec| and |Permutation|.

The following is inspired by copumkin & vmchale's libraries.

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.Vector where

open import Level using (Level)
open import Function using (_$_)
open import DataProperties hiding (⟨_,_⟩)
open import EqualityCombinators

open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)

open import Data.Vec
open import Data.Vec.Properties using (lookup∘tabulate; lookup-allFin)
open import Data.Nat hiding (fold ; _*_)
open import Data.Fin hiding (_+_ ; fold ; _≤_)

open import Data.Sum using () renaming (map to _⊎₁_; [_,_] to either)

open import Structures.Sidequest.Permutations.Basic
\end{code}
%}}}

Note that the most straightforward implementation of |toVector′| gives us
things "backwards": Elements of |Fin n| of length |m|.
Further, this is completely different than |seeP|, as |toVector′| really gives a
way to see the action on |allFin|.

\begin{code}
toVector′ : {n m : ℕ} → Permutation n m → Vec (Fin n) m
toVector′ p = p ◈ allFin _
\end{code}

%{{{ Efforts for deletion

Attempt to tighten the bound on a Fin; i.e., |Sidequest.idris|.
\begin{code}
tighten : {m : ℕ} → Fin (suc m) →  Fin (suc m)  ⊎  Fin m
tighten {zero} zero = inj₁ zero
tighten {zero} (suc ())
tighten {suc m} zero = inj₂ zero
tighten {suc m} (suc i) = (suc ⊎₁ suc) (tighten i)

-- spec : {m : ℕ} {i : Fin (suc m)} (i<m : toℕ i Data.Nat.< m) → tighten i ≡ inj₂ (fromℕ≤ i<m)

sub1 : {m : ℕ} → Fin (suc (suc m)) → Fin (suc m)
sub1 zero    = zero
sub1 (suc i) = i

force : {m n : ℕ} → let 𝓃 = suc n in Vec (Fin (suc 𝓃)) m → Vec (Fin 𝓃) m
force = map (λ it → either sub1 Id₀ (tighten it))

-- ‼ need a relationship between q and i.
postulate
  lemma-0 : {m : ℕ} {q i : Fin (suc m)} {qs : Permutation m m}
         → let it = removeElem (suc q) (allFin (suc (suc m)))  ‼  i
            in
                either {C = λ _ → Fin (suc m)} sub1 Id₀ (tighten it)
            ≡  i
            {-
lemma-0 {m} {q} {zero} {qs} = ≡.refl
lemma-0 {zero} {q} {suc ()} {qs}
lemma-0 {suc m} {zero} {suc i} {p ∷ qs} = {!!}
lemma-0 {suc m} {suc q} {suc i} {qs} = {!!}
-}
\end{code}
%}}}

%{{{ fromVector′ ; fromVector
\begin{code}
-- \edcomm{WK}{Right argument sequence for |Permutation|?}
fromVector′ : {m n : ℕ} → m ≡ n → Vec (Fin n) m → Permutation n m
fromVector′ {0} ≡.refl []                 = []
fromVector′ {suc zero} ≡.refl (zero ∷ []) = zero ∷ []
fromVector′ {suc zero} ≡.refl (suc () ∷ [])
fromVector′ {suc (suc n)} ≡.refl (f ∷ fs) = f ∷ fromVector′ ≡.refl (force fs)

fromVector : {n : ℕ} → Vec (Fin n) n → Permutation n n
fromVector {0} []                 = []
fromVector {suc zero} (zero ∷ []) = zero ∷ []
fromVector {suc zero} (suc () ∷ [])
fromVector {suc (suc n)} (f ∷ fs) = f ∷ fromVector (force fs)
\end{code}
%}}}

%{{{ seePerm ; toVector

Notice that |Permutation n m| is similar to, but distinct from, |Vec (Fin n) m|
and |Vec (Fin m) n|.  We can use the following to directly _visualize_ a permutation
in a nicer way than using |Fin|s.

\begin{code}
seePerm′ : {n m : ℕ} → Permutation n m → Vec ℕ m
seePerm′ p = Data.Vec.map toℕ $ toVector′ p

-- We have a different application now...

toVector : {n m : ℕ} → Permutation n m → Vec (Fin m) n
toVector p = p ◇ allFin _
\end{code}

%}}}

%{{{ seePerm ; seeHelper ; seeP

\begin{code}
seePerm : {n m : ℕ} → Permutation n m → Vec ℕ n
seePerm p = Data.Vec.map toℕ $ toVector p

seeHelper :  {n : ℕ} (let 𝓃 = suc n) (ps : Permutation 𝓃 𝓃)
  → Vec ℕ 𝓃 ×  Vec ℕ 𝓃
seeHelper ps =  Data.Vec.map toℕ (toVector ps)
  , Data.Vec.map toℕ (force (ps ◇ (suc zero ∷ tabulate (λ x → suc (suc x)))))

  -- We can use the following to directly _visualize_ a permutation
  -- in a nicer way that using |Fin|s.
seeP : {n m : ℕ} → Permutation n m → Vec ℕ n
seeP [] = []
seeP (p ∷ ps) = (toℕ p) ∷ seeP ps
\end{code}
%}}}
  
%{{{ allFin specification ;; THIS NEEDS TO BE ELSEWHERE!

\begin{code}
-- |+-suc : ∀ m n → m + suc n ≡ suc (m + n)|
open import Data.Nat.Properties.Simple using (+-suc)

fsuĉ : (m {n} : ℕ) → Fin n → Fin (m + n)
fsuĉ zero i = i
fsuĉ (suc m) {n} i = suc (fsuĉ m i) -- ≡.subst Fin (+-suc m n) (fsuĉ m (suc i))

-- |{m n : ℕ} {i : Fin n}→ (m ∷ tabulate (λ x → m + x)) ‼ i ≡ m + i|
hmm : {m n : ℕ} {i : Fin n} → (tabulate (fsuĉ m) ‼ i) ≡ fsuĉ m i
hmm {m} {n} {i} =  lookup∘tabulate (fsuĉ m) i

allFin-spec : {n : ℕ} {i : Fin (suc (suc n))} → allFin _ ‼ i  ≡  i
allFin-spec {n} {i} = lookup-allFin i
\end{code}

%}}}

%{{{ from-to proof

\begin{code}
_∋_ : {a : Level} (A : Set a) (x : A) → A
A ∋ x = x

fromVector-cong : {n : ℕ} {vs ws : Vec (Fin n) n} → vs ≡ ws → fromVector vs ≡ fromVector ws
fromVector-cong = ≡.cong fromVector

postulate
  helper : {n : ℕ} (let 𝓃 = suc n) {ps : Permutation 𝓃 𝓃}
       →    force (ps ◇ (suc zero ∷ tabulate (λ x → suc (suc x))))
          ≡ toVector ps

from-to : {n : ℕ} {ps : Permutation n n} → fromVector (toVector ps) ≡ ps
from-to {0} {[]} = ≡.refl
from-to {suc zero} {zero ∷ []} = ≡.refl
from-to {suc zero} {suc () ∷ []}
-- case on |p| since |removeElem| is defined that way.
from-to {suc (suc n)} {zero ∷ ps} = ≡.cong₂ _∷_ ≡.refl (fromVector-cong helper ⟨≡≡⟩ from-to)
from-to {suc (suc n)} {suc p ∷ ps} = ≡.cong₂ _∷_ allFin-spec
     (fromVector-cong (goal p ps) ⟨≡≡⟩ from-to)
  where

    postulate
      goal : {m : ℕ} (let 𝓂 = suc m) (q : Fin 𝓂) (qs : Permutation 𝓂 𝓂)
         → force (qs ◇ (zero ∷ removeElem q (suc zero ∷ tabulate (λ x → suc (suc x)))))
         ≡ toVector qs
    -- goal {m} q (p₁ ∷ qs) = ≡.cong₂ _∷_ (lemma-0 {m} {q} {p₁} {qs} ⟨≡≡⟩ ≡.sym allFin-spec) {!!} --
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
