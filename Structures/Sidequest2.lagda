\section{Structures.Sidequest2}

%{{{ Imports
\begin{code}
module Structures.Sidequest2 where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; _∘_)
open import Function using (_$_) renaming (id to Id₀ ; _∘_ to _∘₀_)

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

%{{{ Copy of Data.Vec.Equality.Equality, then tweaked
\begin{code}
module Equality {s₁ s₂} (S : Setoid s₁ s₂) where
  open import Data.Vec using (Vec; []; _∷_; _++_; lookup)
  open import Relation.Binary.PropositionalEquality as P using ()
  open import Data.Nat using (ℕ; suc)
  open import Data.Fin using (Fin)
  open import Function using (_$_)

  private
    open module SS = Setoid S
      using () renaming (_≈_ to _≊_; Carrier to A; refl to ≊-refl)

  infix 4 _≈_

  data _≈_ : ∀ {n¹ n²} → Vec A n¹ → Vec A n² → Set s₂ where
    []-cong  : [] ≈ []
    _∷-cong_ : ∀ {x¹ n¹} {xs¹ : Vec A n¹}
                 {x² n²} {xs² : Vec A n²}
                 (x¹≈x² : x¹ ≊ x²) (xs¹≈xs² : xs¹ ≈ xs²) →
                 x¹ ∷ xs¹ ≈ x² ∷ xs²

  length-equal : ∀ {n¹ n²} {xs¹ : Vec A n¹} {xs² : Vec A n²} →
                 xs¹ ≈ xs² → n¹ P.≡ n²
  length-equal []-cong        = P.refl
  length-equal (_ ∷-cong eq₂) = P.cong suc $ length-equal eq₂

  refl : ∀ {n} (xs : Vec A n) → xs ≈ xs
  refl []       = []-cong
  refl (x ∷ xs) = SS.refl ∷-cong refl xs

  sym : ∀ {n m} {xs : Vec A n} {ys : Vec A m} → xs ≈ ys → ys ≈ xs
  sym []-cong                = []-cong
  sym (x¹≡x² ∷-cong xs¹≈xs²) = SS.sym x¹≡x² ∷-cong sym xs¹≈xs²

  trans : ∀ {n m l} {xs : Vec A n} {ys : Vec A m} {zs : Vec A l} →
          xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans []-cong            []-cong            = []-cong
  trans (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) =
    SS.trans x≈y y≈z ∷-cong trans xs≈ys ys≈zs

  _++-cong_ : ∀ {n₁¹ n₂¹} {xs₁¹ : Vec A n₁¹} {xs₂¹ : Vec A n₂¹}
                {n₁² n₂²} {xs₁² : Vec A n₁²} {xs₂² : Vec A n₂²} →
              xs₁¹ ≈ xs₁² → xs₂¹ ≈ xs₂² →
              xs₁¹ ++ xs₂¹ ≈ xs₁² ++ xs₂²
  []-cong          ++-cong eq₃ = eq₃
  (eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

  lookup-cong : {n : ℕ} (i : Fin n) {xs ys : Vec A n} → xs ≈ ys → lookup i xs ≊ lookup i ys
  lookup-cong i []-cong = ≊-refl
  lookup-cong Fin.zero (x¹≈x² ∷-cong eq) = x¹≈x²
  lookup-cong (Fin.suc i) (x¹≈x² ∷-cong eq) = lookup-cong i eq

\end{code}
%}}}

%{{{ Permutations
\begin{code}
module Permutations {ℓ c : Level} (𝒮 : Setoid c ℓ)
  where

  open Equality 𝒮 renaming (_≈_ to _≈ₖ_) public
  -- open Setoid 𝒮
  module ≈ = Setoid 𝒮
  open ≈ using (Carrier ; _≈_)
  open import Data.Vec
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold ; _≤_)  

  -- move to DataCombinators.lagda
  _‼_ : {a : Level} {A : Set a} {n : ℕ} → Vec A n → Fin n → A
  _‼_ = λ xs i → lookup i xs
\end{code}

  %{{{ Permutations datatype, insert, permute ◈


\begin{code}
  infixr 5 _∷_

  data Permutation : ℕ → ℕ → Set where
    []  : Permutation 0 0
    _∷_ : {n m : ℕ} → (p : Fin (suc m)) → (ps : Permutation n m) → Permutation (suc n) (suc m)

  homogeneity : {n m : ℕ} → Permutation n m → n ≡ m
  homogeneity [] = ≡.refl
  homogeneity (p ∷ ps) = ≡.cong suc (homogeneity ps)
\end{code}

What exactly are the semantics of these things?
Insertions!
See the |permute| operation below.

|insert xs i x ≈ xs[1…i-1] ++ [x] ++ xs[i … len xs]|
( Note that this is different from |Data.Vec._[_]≔_| which updates a positional element. )

\begin{code}
  insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
  insert xs zero a = a ∷ xs
  insert [] (suc ()) a
  insert (x ∷ xs) (suc i) a = x ∷ insert xs i a
\end{code}

This allows us to apply a permutation to a vector.
\begin{code}
  infix 6 _◈_
  _◈_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A n → Vec A m
  []       ◈ []       = []
  (p ∷ ps) ◈ (x ∷ xs) = insert (ps ◈ xs) p x
\end{code}
\edcomm{JC}{It is also good to remember that a |Permutation| in our encoding is really a
program (i.e. a group action). Its meaning is really given by |_◈_| on vectors.
And, in that sense, a |Permutation| encodes a *sequence of inserts*.
And it is tricky in the sense that you first do all the inserts
given by the tail of the permutation, THEN you do the head insertion.}

But that's not the only way to apply a permutation to a vector. There is
also a ``subtractive'' way to do it. Given a way to remove an element from
a Vector:
\begin{code}
  removeElem : {n : ℕ} {a : Level} {A : Set a} → Fin (suc n) → Vec A (suc n) → Vec A n
  removeElem {_}    zero     (x ∷ v) = v
  removeElem {zero} (suc ()) (x ∷ v)
  removeElem {suc n} (suc k) (x ∷ v) = x ∷ removeElem k v
\end{code}

We can define a different application.  But note that it goes the ``other way around'':
it applies to a |Vec A m| rather than a |Vec A n|.
\begin{code}
  infix 6 _◇_
  _◇_ : {n m : ℕ} {a : Level} {A : Set a} → Permutation n m → Vec A m → Vec A n
  [] ◇ [] = []
  (p ∷ ps) ◇ xs = xs ‼ p ∷ ps ◇ removeElem p xs
\end{code}
%}}}

  %{{{ Identity and Reverse
\begin{code}
  -- Note how we have definitional equality of indices.
  idP : {n : ℕ} → Permutation n n
  idP {zero} = []
  idP {suc _} = zero ∷ idP

  -- And its action is indeed the identity
  idP-◈ : {n : ℕ} {xs : Vec ≈.Carrier n} → idP ◈ xs ≈ₖ xs
  idP-◈ {xs = []   } = []-cong
  idP-◈ {xs = _ ∷ _} = ≈.refl ∷-cong idP-◈

  -- for both notions
  idP-◇ : {m : ℕ} {xs : Vec ≈.Carrier m} → idP ◇ xs ≈ₖ xs
  idP-◇ {xs = []} = []-cong
  idP-◇ {xs = _ ∷ _} = ≈.refl ∷-cong idP-◇
\end{code}

\begin{code}
  -- A direct implementation of reverse
  rev : {n : ℕ} → Permutation n n
  rev {zero}  = []
  rev {suc n} = fromℕ n ∷ rev
\end{code}

%}}}

The following is inspired by copumkin & vmchale's libraries.

  %{{{ Relationship between Vec and Permutation
\begin{code}
  -- Notice that |Permutation n m| is similar to, but distinct from, |Vec (Fin n) m|
  -- and |Vec (Fin m) n|.  We can use the following to directly _visualize_ a permutation
  -- in a nicer way that using |Fin|s.
  seeP : {n m : ℕ} → Permutation n m → Vec ℕ n
  seeP [] = []
  seeP (p ∷ ps) = (toℕ p) ∷ seeP ps

  -- note that the most straightforward implementation of |toVector′| gives us
  -- things "backwards": elements of |Fin n| of length |m|.
  -- Further, this is completely different than |seeP|, as |toVector′| really gives a
  -- way to see the action on |allFin|
  toVector′ : {n m : ℕ} → Permutation n m → Vec (Fin n) m
  toVector′ p = p ◈ allFin _

  seeVec : {n m : ℕ} → Permutation n m → Vec ℕ m
  seeVec p = Data.Vec.map toℕ $ toVector′ p

  -- but we have a different application now...
  toVector : {n m : ℕ} → Permutation n m → Vec (Fin m) n
  toVector p = p ◇ allFin _

  -- ToDo: Consider forming inverse of seeP.

\end{code}

\edcomm{JC}{I think of |Permutation n m| as having length |n| and inhabited by things of type |Fin m|.
So you use |n| to index, and |m| for what you retrieve.}
\begin{code}   
  open import Data.Sum using () renaming (map to _⊎₁_; [_,_] to either)
  
  -- Attempt to tighten the bound on a Fin
  idris : {m : ℕ} → Fin (suc m) → (Fin (suc m)) ⊎ (Fin m)
  idris {zero} zero = inj₁ zero
  idris {zero} (suc ())
  idris {suc m} zero = inj₂ zero
  idris {suc m} (suc i) = (suc ⊎₁ suc) (idris i)
    
  sub1 : {m : ℕ} → Fin (suc (suc m)) → Fin (suc m)
  sub1 zero    = zero
  sub1 (suc i) = i

  delete : {n m : ℕ} → Permutation (suc n) (suc m) → Fin (suc n) → Permutation n m
  delete {n} (p ∷ ps) zero = ps
  delete {zero} p (suc ())
  delete {suc n} {zero} (_ ∷ ()) (suc q)
  delete {suc n} {suc m} (zero ∷ ps) (suc q) = zero ∷ (delete ps q)
  delete {suc n} {suc m} (suc p ∷ ps) (suc q) = either sub1 Id₀ (idris (suc p)) ∷ (delete ps q)  

  delete-spec : {n : ℕ} {ps : Permutation (suc n) (suc n)} {q : Fin (suc n)}
              → {xs : Vec Carrier (suc n)}
              → delete ps q ◈ removeElem q xs   ≈ₖ   removeElem q (ps ◈ xs)
  delete-spec {n} {zero ∷ ps} {zero} {x ∷ xs} = refl _
  delete-spec {n} {suc p ∷ ps} {zero} {x ∷ xs} = {!!}
  delete-spec {zero} {p ∷ ps} {suc ()} {x ∷ xs}
  delete-spec {suc n} {zero ∷ ps} {suc q} {x ∷ xs} = ≈.refl ∷-cong delete-spec
  delete-spec {suc n} {suc p ∷ ps} {suc q} {x ∷ xs} = {!!}

  _⁇_ : {n m : ℕ} → Permutation n m → Fin n → Fin m
  ps ⁇ i = toVector ps ‼ i

  delete-lookup : {n m : ℕ} {ps : Permutation (suc n) (suc m)} {q : Fin (suc {!!})}
                → Data.Fin.raise 1 (delete ps q ⁇ {!q!}) ≡ (ps ⁇ q)
  delete-lookup = {!!}
\end{code}
compose Nil p = p
compose (i :: p) p' = (index i (toVector p')) :: (compose p (delete i p'))


%}}}
  %{{{ Inversion of permutations

\begin{code}  
  lookup-insert : {n : ℕ} (v : Vec Carrier n) (x : Carrier) (i : Fin (suc n))
                → lookup i (insert v i x) ≈ x
  lookup-insert vs x zero = ≈.refl
  lookup-insert [] x (suc ())
  lookup-insert (v ∷ vs) x (suc i) = lookup-insert vs x i

  remove-insert : {n : ℕ} (v : Vec Carrier n) (x : Carrier) (i : Fin (suc n))
                → removeElem i (insert v i x) ≈ₖ v
  remove-insert vs x zero = refl vs
  remove-insert [] x (suc ())
  remove-insert (v ∷ vs) x (suc i) = ≈.refl ∷-cong remove-insert vs x i

  remove-cong : {n : ℕ} (i : Fin (suc n)) {xs ys : Vec Carrier (suc n)}
              → xs ≈ₖ ys → removeElem i xs ≈ₖ removeElem i ys
  remove-cong zero (x¹≈x² Equality.∷-cong eq) = eq
  remove-cong {zero} (suc ()) (x¹≈x² ∷-cong eq)
  remove-cong {suc _} (suc i) {_ ∷ xs} {_ ∷ ys} (x¹≈x² Equality.∷-cong eq) =
    x¹≈x² ∷-cong remove-cong i eq

  ◇-cong₂ : {n m : ℕ} (ps : Permutation n m) {xs ys : Vec Carrier m}
          → xs ≈ₖ ys → ps ◇ xs ≈ₖ ps ◇ ys
  ◇-cong₂ ps []-cong = refl _
  ◇-cong₂ (zero ∷ ps) (x¹≈x² Equality.∷-cong eq) = x¹≈x² ∷-cong ◇-cong₂ ps eq
  ◇-cong₂ (suc p ∷ ps) eq′@(x¹≈x² Equality.∷-cong eq) =
      lookup-cong p eq ∷-cong ◇-cong₂ ps (remove-cong (suc p) eq′)

  inversionTheorem : {n m : ℕ} (p : Permutation n m)  (xs : Vec Carrier n)
                   → p ◇ (p ◈ xs) ≈ₖ xs
  inversionTheorem [] [] = []-cong
  inversionTheorem (zero ∷ ps) (x ∷ xs) = ≈.refl ∷-cong inversionTheorem ps xs
  inversionTheorem (suc p ∷ ps) (x ∷ xs) = lookup-insert (ps ◈ xs) x (suc p) ∷-cong
    trans (◇-cong₂ ps (remove-insert (ps ◈ xs) x (suc p))) (inversionTheorem ps xs)

  ◈-elimination : {n m : ℕ} (p : Permutation n m)  (xs : Vec Carrier n) (ys : Vec Carrier m)
                → p ◈ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◇ ys
  ◈-elimination p xs ys eq = trans (sym (inversionTheorem p xs)) (◇-cong₂ p eq)
\end{code}

The other form as well,
\begin{code}
  insert-remove-lookup : {n : ℕ} (v : Vec Carrier (suc n)) (i : Fin (suc n))
                → insert (removeElem i v) i (lookup i v) ≈ₖ v
  insert-remove-lookup (x ∷ v) zero = refl _
  insert-remove-lookup {zero} (x ∷ v) (suc ())
  insert-remove-lookup {suc n} (x ∷ v) (suc i) = ≈.refl ∷-cong insert-remove-lookup _ _

  insert-cong₁ : {n : ℕ} {xs ys : Vec Carrier n} {i : Fin (1 + n)} {e : Carrier}
               → xs ≈ₖ ys → insert xs i e  ≈ₖ  insert ys i e
  insert-cong₁ {i = zero} xs≈ys = ≈.refl ∷-cong xs≈ys
  insert-cong₁ {i = suc j} []-cong = refl _
  insert-cong₁ {i = suc j} (x≈y ∷-cong xs≈ys) = x≈y ∷-cong insert-cong₁ xs≈ys
  
  inversionTheorem˘ : {n m : ℕ} (p : Permutation n m)  (xs : Vec Carrier m)
                    → p ◈ (p ◇ xs) ≈ₖ xs
  inversionTheorem˘ [] [] = []-cong
  inversionTheorem˘ (zero ∷ p₁) (x ∷ xs) = ≈.refl ∷-cong inversionTheorem˘ p₁ xs
  inversionTheorem˘ (suc p ∷ p₁) (x ∷ xs)
    = trans (insert-cong₁ (inversionTheorem˘ _ _)) (insert-remove-lookup _ _)

  insert-cong₃ : {n : ℕ} {xs : Vec Carrier n} {i : Fin (1 + n)} {d e : Carrier}
               → e ≈ d → insert xs i e  ≈ₖ  insert xs i d
  insert-cong₃ {xs = []} {zero} e≈d = e≈d ∷-cong []-cong
  insert-cong₃ {xs = []} {suc ()} e≈d
  insert-cong₃ {xs = x ∷ xs} {zero} e≈d = e≈d ∷-cong refl _
  insert-cong₃ {xs = x ∷ xs} {suc i} e≈d = ≈.refl ∷-cong insert-cong₃ {_} {xs} {i} e≈d

  ◈-cong₂ : {n m : ℕ} {ps : Permutation n m} {xs ys : Vec Carrier n}
          → xs ≈ₖ ys → ps ◈ xs ≈ₖ ps ◈ ys
  ◈-cong₂ []-cong = refl _
  ◈-cong₂ {ps = p ∷ ps} (x≈y ∷-cong eqs) = trans (insert-cong₁ {i = p} (◈-cong₂ {ps = ps} eqs)) (insert-cong₃ x≈y)

  ◇-elimination : {n m : ℕ} (p : Permutation n m)  (xs : Vec Carrier m) (ys : Vec Carrier n)
                → p ◇ xs  ≈ₖ  ys   →   xs  ≈ₖ  p ◈ ys
  ◇-elimination p xs ys eq = trans (sym (inversionTheorem˘ p xs)) (◈-cong₂ eq)
\end{code}
\begin{spec}
  open import Relation.Nullary

  -- Permutations come with the obvious involution, but non-trivial implementation
  _˘ : {n m : ℕ} → Permutation n m → Permutation m n
  _˘ {zero }          []        = []
  _˘ {suc n} {suc m} pp@(p ∷ ps) = (toVector′ pp ‼ p) ∷ {!!} -- ((ps ─ i' ps ?) ˘)
    where
          i' : {i j : ℕ} → Permutation (suc i) (suc j) → Fin (suc j) → Fin (suc i)
          i' q idx = (toVector′ q) ‼ idx

  -- vmchale makes no recursive call...
\end{spec}

\begin{code}
{-
  -- Specification/characterisation of inverse: It can be used to solve equations.
  ˘-char : {n m : ℕ} {xs : Vec ≈.Carrier n} {p : Permutation n m} {ys : Vec ≈.Carrier m} → p ◈ xs ≈ₖ ys → p ˘ ◈ ys ≈ₖ xs
  ˘-char {zero} {.0} {[]} {[]} {[]} eq = eq
  ˘-char {suc n} {zero} {xs} {()} {[]} eq
  ˘-char {suc n} {suc m} {x ∷ xs} {zero ∷ p₁} {x₁ ∷ ys} (x≈y ∷-cong eq) = (≈.sym x≈y) ∷-cong (˘-char eq)
  ˘-char {suc n} {suc m} {x ∷ xs} {suc p ∷ p₁} {x₁ ∷ ys} eq = {!!}
-}
  aPerm : Permutation 5 5
  aPerm = suc (suc (suc zero)) ∷ zero ∷ suc (suc zero) ∷ zero ∷ zero ∷ []

  VecPa≡30412 : seeVec aPerm ≡ 1 ∷ 3 ∷ 4 ∷ 0 ∷ 2 ∷ []
  VecPa≡30412 = ≡.refl

  aPerm˘ : Permutation 5 5
  aPerm˘ = suc zero ∷ suc (suc zero) ∷ suc (suc zero) ∷ zero ∷ zero ∷ []

  test-inv : aPerm˘ ◈ (aPerm ◈ allFin _) ≡ allFin _
  test-inv = ≡.refl

  test-inv2 : aPerm ◇ (aPerm ◈ allFin _) ≡ allFin _
  test-inv2 = ≡.refl
\end{code}

  %{{{ cong properties

\begin{spec}
  insert-cong₂ : {n : ℕ} {xs : Seq n} {i j : Fin (1 + n)} {e : Carrier}
               → i ≡ j → insert xs i e  ≈ₖ  insert xs j e
  insert-cong₂ ≡.refl = ≈ₖ-refl

  ◈-cong₁ : {n m : ℕ} {ps qs : Permutation n m} {xs : Seq n}
          → ps ≈ₚ qs → ps ◈ xs ≈ₖ qs ◈ xs
  ◈-cong₁ eq = eq
  -- This is part of the definition of permutation equality.
\end{spec}
  %}}}

\begin{spec}
  -- Composition of permutations
  -- \edcomm{MA}{This particular form of typing is chosen so that |Permutation| acts as a morphism}
  -- type constructor for a category whose objects are natural numbers. Then this composition
  -- has the type necessary to make this into a category.
  infix 6 _⊙_
  _⊙_ : {n m r : ℕ} → Permutation n m → Permutation m r → Permutation n r
  [] ⊙ [] = []
  (p ∷ ps) ⊙ (q ∷ qs) = (toVector (q ∷ qs) ‼ p) ∷ ps ⊙ qs -- (qs at′ p) ∷ (ps ⊙ (qs ─ p))

  -- \edcomm{MA}{I made componentwise equality heterogenous in order to make the typing here more}
  -- general; yet it is not.
  ◈-compose : {n m r : ℕ} {ps : Permutation n m} {qs : Permutation m r}
            → {xs : Seq n} → (ps ⊙ qs) ◈ xs  ≈ₖ  qs ◈ (ps ◈ xs)
  ◈-compose {ps = []} {[]} {[]} = nil
  ◈-compose {ps = zero ∷ ps} {q ∷ qs} {x ∷ xs} = {!!}
  ◈-compose {ps = suc p ∷ ps} {q ∷ qs} {x ∷ xs} = {!!}
\end{spec}

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

%{{{ Interface

Permutations form a group,
\begin{code}
  infix 5 _≈₁_
  _≈₁_ : {n m : ℕ} → (a b : Permutation n m) → Set {!!}
  _≈₁_ = {!!}

  infix 6 _⊙_
  _⊙_ : {n m r : ℕ} → Permutation n m → Permutation m r → Permutation n r
  _⊙_ = {!!}

  ⊙-cong : {n m r : ℕ} {a a′ : Permutation n m} {b b′ : Permutation m r}
         → a ≈₁ a′ → b ≈₁ b′ → a ⊙ b ≈₁ a′ ⊙ b′
  ⊙-cong = {!!}

  ⊙-assoc : {n m r s : ℕ} {a : Permutation n m} {b : Permutation m r} {c : Permutation r s}
          → (a ⊙ b) ⊙ c ≈₁ a ⊙ (b ⊙ c)
  ⊙-assoc = {!!}

  ⊙-leftId : {n m : ℕ} {a : Permutation n m} → idP ⊙ a ≈₁ a
  ⊙-leftId = {!!}

  ⊙-rightId : {n m : ℕ} {a : Permutation n m} → a ⊙ idP ≈₁ a
  ⊙-rightId = {!!}

  infix 7 _˘
  _˘ : {n m : ℕ} → Permutation n m → Permutation m n
  _˘ = {!!}

  ˘-cong : {n m : ℕ} {a a′ : Permutation n m} → a ≈₁ a′ → a ˘ ≈₁ a′ ˘
  ˘-cong = {!!}

  ˘- : {n m : ℕ} {a : Permutation n m} → a ˘ ⊙ a ≈₁ idP
  ˘- = {!!}

  solve-linear-equation : {n m r : ℕ} {a : Permutation n m} {x : Permutation m r} {b : Permutation n r}
    → a ⊙ x ≈₁ b → x ≈₁ a ˘ ⊙ b
  solve-linear-equation = {!!}

  ˘-shunting : {n m : ℕ} {a : Permutation n m} {b : Permutation m n}
             → a ˘ ≈₁ b → a ≈₁ b ˘
  ˘-shunting = {!!}
\end{code}

Moreover, permutations provide a group action on vectors:
\begin{code}
  ◈-cong₁ : {n m : ℕ} {a b : Permutation n m} {xs : Vec Carrier n}
          → a ≈₁ b → a ◈ xs ≈ₖ b ◈ xs
  ◈-cong₁ = {!!}
  
  ◈-compose : {n m r : ℕ} {a : Permutation n m} {b : Permutation m r}
            → {xs : Vec Carrier n} → (a ⊙ b) ◈ xs  ≈ₖ  b ◈ (a ◈ xs)
  ◈-compose = {!!}

  ◈-solve-linear-equation : {n m : ℕ} {w : Permutation n m} {xs : Vec Carrier n} {ys : Vec Carrier m}
    → w ◈ xs ≈ₖ ys → xs ≈ₖ w ˘ ◈ ys
  ◈-solve-linear-equation {n} {m} {w} {xs} {ys} w◈x≈y
    = sym idP-◈
    ⇐  ◈-cong₁ (˘- {n} {m} {a = w})
    ⇐ sym (◈-compose {a = w} {b = w ˘} {xs = xs})
    ⇐ ◈-cong₂ {m} {n} {ps = w ˘} {w ◈ xs} {ys} w◈x≈y
    where
      infixl 4 _⇐_
      _⇐_ = trans
\end{code}

%}}}

And now we really want to use our |Permutation| to define a bag equality on lists.
But this is a bit of a pain, as |Permutation| really acts on |Vec|. But, of course,
a |List| is just a |Vec| that has forgotten its |length| (or the other way around
if you are thinking in terms of ornaments).  This type equivalence will be shown
elsewhere, so here we set things up using |Vec|.

\begin{code}
  private
    Seq = Vec ≈.Carrier

  -- equality-(of vectors)-up-to-permutation
  record _≈ₚ_ {n m : ℕ} (xs : Seq n) (ys : Seq m) : Set ℓ where
    constructor MkEq
    field
      witness : Permutation n m
      proof   : witness ◈ xs ≈ₖ ys

  ≈ₚ-refl :  {n : ℕ} {xs : Seq n} → xs ≈ₚ xs
  ≈ₚ-refl = record { witness = idP ; proof = idP-◈ }

  ≈ₚ-sym : {n m : ℕ} {xs : Seq n} {ys : Seq m} → xs ≈ₚ ys → ys ≈ₚ xs
  ≈ₚ-sym (MkEq w pf) = MkEq (w ˘) (◈-solve-linear-equation pf)

  ≈ₚ-trans : {n m r : ℕ} {xs : Seq n} {ys : Seq m} {zs : Seq r}
           → xs ≈ₚ ys → ys ≈ₚ zs → xs ≈ₚ zs
  ≈ₚ-trans (MkEq witness proof) (MkEq witness₁ proof₁) =
    MkEq (witness ⊙ witness₁)
         (trans ◈-compose (trans (◈-cong₂ proof) proof₁))

  ≈ₚ-isEquivalence : {n : ℕ} → IsEquivalence (_≈ₚ_ {n} {n})
  ≈ₚ-isEquivalence = record { refl = ≈ₚ-refl ; sym = ≈ₚ-sym ; trans = ≈ₚ-trans }

  singleton-≈ : {x y : Carrier} → x ≈ y → (x ∷ []) ≈ₚ (y ∷ [])
  singleton-≈ = λ x≈y → MkEq idP (x≈y ∷-cong []-cong)
\end{code}
%}}}

%{{{ Pesky-hole from the summer
\begin{code}
module Lemmas {l c : Level} {𝒮 : Setoid c l} (𝒞 : CommMonoid 𝒮) where

  open CommMonoid 𝒞
  open IsCommutativeMonoid isCommMonoid -- \edcomm{MA}{The field name really oughtn't be abbreviated!}

  open Setoid 𝒮
  open Equality 𝒮 renaming (_≈_ to _≈ₖ_) hiding (refl ; trans)
  -- module ≈ = Setoid 𝒮
  
  open import Data.Vec
  open import Data.Nat  hiding (fold ; _*_)

  private
    Seq = Vec Carrier

  -- fold is a setoid homomorphism

  fold : {n : ℕ} → Seq n → Carrier
  fold = foldr (λ _ → Carrier) _*_ e

  fold-cong : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong []-cong = ≈.refl
  fold-cong (x≈y ∷-cong xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

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

  open Permutations 𝒮 hiding (refl ; trans)
  open import Data.Fin  hiding (_+_ ; fold ; _≤_)  

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

  proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n n} → fold xs ≈ fold (p ◈ xs)
  proposition₁ {xs = []} {[]} = refl
  proposition₁ {xs = x ∷ xs} {zero  ∷ ps} = refl ⟨∙⟩ proposition₁
  proposition₁ {xs = x ∷ xs} {suc p ∷ ps} with ps ◈ xs | inspect (_◈_ ps) xs
  proposition₁ {_} {x ∷ xs} {suc () ∷ ps} | [] | _
  proposition₁ {_} {x ∷ xs} {suc p ∷ ps} | x′ ∷ xs′ | [ ps◈xs≈xs′ ] = begin⟨ 𝒮 ⟩
      x * fold xs
    ≈⟨ refl ⟨∙⟩ proposition₁ ⟩
      x * fold (ps ◈ xs)
    ≡⟨ ≡.cong (λ zs → x * fold zs) ps◈xs≈xs′ ⟩
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
  proposition₀ : {n : ℕ} {xs ys : Seq n} → xs ≈ₚ ys → fold xs ≈ fold ys
  proposition₀ (MkEq p p◈xs≈ys) = trans proposition₁ (fold-cong p◈xs≈ys)
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
