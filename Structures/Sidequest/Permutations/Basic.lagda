\section{Structures.Sidequest.Permutations.Basic}

%{{{ Imports
\begin{code}
module Structures.Sidequest.Permutations.Basic where

open import Level using (Level)
open import Function using (_$_)
open import DataProperties hiding (⟨_,_⟩)
open import EqualityCombinators

open import Data.Vec
open import Data.Vec.Properties using (lookup∘tabulate; lookup-allFin)
open import Data.Nat hiding (fold ; _*_)
open import Data.Fin hiding (_+_ ; fold ; _≤_)
\end{code}
%}}}

\begin{code}
infixr 5 _∷_
data Permutation : ℕ → ℕ → Set where
  []  : Permutation 0 0
  _∷_ : {n m : ℕ} (p : Fin (suc m)) (ps : Permutation n m) → Permutation (suc n) (suc m)
\end{code}

Not as heterogeneous as they may appear:

\begin{code}
homogeneity : {n m : ℕ} → Permutation n m → n ≡ m
homogeneity []        =  ≡.refl
homogeneity (p ∷ ps)  =  ≡.cong suc $ homogeneity ps
\end{code}

The heterogeneity was only included to make typing easier.

What exactly are the semantics of these things?
Insertions or deletions? See the permute operations |_◇_ ; _◈_|  below.

\edcomm{JC}{I think of |Permutation n m| as having length |n| and inhabited by things of type |Fin m|.
So you use |n| to index, and |m| for what you retrieve.}

%{{{ insert ; lookup-insert ; _◈_

|insert xs i x ≈ xs[1…i-1] ++ [x] ++ xs[i … len xs]|
( Note that this is different from |Data.Vec._[_]≔_| which updates a positional element. )

\begin{code}
insert : {n : ℕ} {a : Level} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
insert xs zero a           =  a ∷ xs
insert [] (suc ()) _
insert (x ∷ xs) (suc i) a  =  x ∷ insert xs i a
\end{code}

\begin{code}
lookup-insert : {n : ℕ} {ℓ : Level} {A : Set ℓ} {xs : Vec A n} {i : Fin (1 + n)} {a : A}
              → lookup i (insert xs i a) ≡ a
lookup-insert {xs = xs} {zero} {a}       =  _≡_.refl
lookup-insert {xs = []} {suc ()} {_}
lookup-insert {xs = x ∷ xs} {suc i} {a}  =  lookup-insert {xs = xs} {i} {a}
\end{code}

This allows us to apply a permutation to a vector.
\begin{code}
infix 6 _◈_
_◈_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A n → Vec A m
[]       ◈ []        =  []
(p ∷ ps) ◈ (x ∷ xs)  =  insert (ps ◈ xs) p x
\end{code}
\edcomm{JC}{It is also good to remember that a |Permutation| in our encoding is really a
program (i.e. a group action). Its meaning is really given by |_◈_| on vectors.
And, in that sense, a |Permutation| encodes a *sequence of inserts*.
And it is tricky in the sense that you first do all the inserts
given by the tail of the permutation, THEN you do the head insertion.}

%}}}

%{{{ removeElem ; removeElem′ ; _◇_

But that's not the only way to apply a permutation to a vector. There is
also a ``subtractive'' way to do it. Given a way to remove an element from
a Vector:
\begin{code}
removeElem : {n : ℕ} {a : Level} {A : Set a} → Fin (suc n) → Vec A (suc n) → Vec A n
removeElem {_}    zero     (_ ∷ v)  =  v
removeElem {zero} (suc ()) (_ ∷ _)
removeElem {suc n} (suc k) (x ∷ v)  =  x ∷ removeElem {n} k v

-- attempting to get better reduction behaviour --- however, this only shifts
-- the ``additional constructor required'' from |n| to |v|.
removeElem′ : {n : ℕ} {a : Level} {A : Set a} → Fin (suc n) → Vec A (suc n) → Vec A n
removeElem′ _     (_ ∷ [])  =  []
removeElem′ zero  (_ ∷ v)  =  v
removeElem′ (suc k) (x ∷ y ∷ ys)  =  x ∷ removeElem′ k (y ∷ ys)
\end{code}

We can define a different application.  But note that it goes the ``other way around'':
it applies to a |Vec A m| rather than a |Vec A n|.
\begin{code}
infix 6 _◇_
_◇_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A m → Vec A n
[] ◇ []        =  []
(p ∷ ps) ◇ xs  =  xs ‼ p  ∷  ps ◇ removeElem p xs
\end{code}
%}}}

\begin{code}
remove-insert : {n : ℕ} {ℓ : Level} {A : Set ℓ} {xs : Vec A n} {i : Fin (suc n)} {a : A}
              → removeElem i (insert xs i a) ≡ xs
remove-insert {xs = xs} {zero} {a} = ≡.refl
remove-insert {xs = []} {suc ()} {a}
remove-insert {xs = x ∷ xs} {suc i} {a} = ≡.cong (x ∷_) (remove-insert {xs = xs} {i} {a})

insert-remove-lookup : {n : ℕ} {ℓ : Level} {A : Set ℓ} {xs : Vec A (suc n)} {i : Fin (suc n)}
              → insert (removeElem i xs) i (xs ‼ i)  ≡  xs
insert-remove-lookup {xs = x ∷ xs} {zero} = ≡.refl
insert-remove-lookup {zero} {xs = x ∷ xs} {suc ()}
insert-remove-lookup {n = suc n} {xs = x ∷ xs} {suc i} = ≡.cong (x ∷_) (insert-remove-lookup {xs = xs})
\end{code}

\begin{code}
inversionTheorem : {n m : ℕ} (p : Permutation n m) {ℓ : Level} {A : Set ℓ} (xs : Vec A n)
                 → p ◇ (p ◈ xs) ≡ xs
inversionTheorem [] [] = ≡.refl
inversionTheorem (zero ∷ ps) (x ∷ xs) = ≡.cong (x ∷_) (inversionTheorem ps xs)
inversionTheorem (suc p ∷ ps) (x ∷ xs) =
  ≡.cong₂ _∷_ (lookup-insert {xs = ps ◈ xs}) 
               (≡.cong (ps ◇_) (remove-insert {xs = ps ◈ xs}) ⟨≡≡⟩ inversionTheorem ps xs)



inversionTheorem˘ : {n m : ℕ} (p : Permutation n m) {ℓ : Level} {A : Set ℓ} (xs : Vec A m)
                 → p ◈ (p ◇ xs) ≡ xs
inversionTheorem˘ [] []       = ≡.refl
inversionTheorem˘ (zero ∷ ps) (x ∷ xs) = ≡.cong (x ∷_) (inversionTheorem˘ ps xs)
inversionTheorem˘ (suc p ∷ ps) {A = A} (x ∷ xs) with homogeneity (suc p ∷ ps)
... | ≡.refl = begin
     (suc p ∷ ps) ◈ ((suc p ∷ ps) ◇ (x ∷ xs))
  ≡⟨⟩  -- Def. |◇|
     (suc p ∷ ps) ◈ (((x ∷ xs) ‼ suc p)  ∷  (ps ◇ (removeElem (suc p) (x ∷ xs))))
  ≡⟨⟩ -- Def. |◈|
     insert (ps ◈ (ps ◇ (removeElem (suc p) (x ∷ xs)))) (suc p) ((x ∷ xs) ‼ suc p)
  ≡⟨ ≡.cong (λ it → insert it _ _) (inversionTheorem˘ ps _) ⟩
     insert (removeElem (suc p) (x ∷ xs)) (suc p) ((x ∷ xs) ‼ suc p)
  ≡⟨ insert-remove-lookup {i = suc p} ⟩  
     x ∷ xs
   ∎
  where open import Relation.Binary.EqReasoning (≡.setoid (Vec A _))
\end{code}

%{{{ Identity and Reverse
\begin{code}
-- Note how we have definitional equality of indices.
Id : {n : ℕ} → Permutation n n
Id {zero}   =  []
Id {suc _}  =  zero ∷ Id

rev : {n : ℕ} → Permutation n n
rev {zero}   =  []
rev {suc n}  =  fromℕ n ∷ rev
\end{code}

In the setting of equality between vectors, over some setoid, it can be shown
that |Id| is the identity of both actions |_◇_| and |_◈_|.

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
