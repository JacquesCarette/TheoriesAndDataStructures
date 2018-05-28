\section{Bags Implemented by Sequences}

Here we use |Table| as a means to implement |Bags|. This ends up being somewhat more convenient
than using |List| directly, even though how we use them are equivalent types. One important
aspect is that the tables involved are over a |Setoid|.

%{{{ imports
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Structures.SequencesAsBags where

open import Level
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Table using (Table; permute; rearrange; lookup)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Table.Relation.Equality using (setoid)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.SetoidReasoning
open import Function.Equality using (module Π)
import Function.Inverse as Inv using (module Inverse)
open import Function.Inverse using (_↔_)
open import Function using () renaming (id to id₀; _∘_ to _∘₀_)
open import Algebra   using (CommutativeMonoid)

open import FinEquivPlusTimes using (module Plus; F0≃⊥)
open import FinEquivTypeEquiv using (module PlusE; _fin≃_)
open import TypeEquiv using (swap₊; swap₊equiv; unite₊equiv)
-- open import TypeEquivEquiv using (swap₊-nat)
open import EquivEquiv using (_≋_)
open import Equiv using (_●_; β₁; _⊎≃_; id≃; _⟨≃≃⟩_; ≐-trans; ≐-sym;
  cong∘l; cong∘r; β⊎₁)

open import Structures.CommMonoid renaming (Hom to CMArrow)

infixr 10 _⊙_

private
  _⊙_ = ≐-trans
  !_ = ≐-sym

\end{code}
%}}}

%{{{ Seq
\begin{code}
-- A “sequence” is the functional view of a list ─which are properly handled in Agda as vectors.
-- `ATable`
record Seq {a : Level} (A : Set a) : Set a where
  constructor sequence
  field
   len : ℕ
   _‼_ : Fin len → A  -- lookup operation

  -- These are of-course just |Table|s where the length is packaged into the record;
  -- thereby being somewhat more homogeneous or “untyped”.

  table : Table A len
  table = Table.tabulate _‼_

open Seq public

table˘ : {a : Level} {A : Set a} {n : ℕ} → Table A n → Seq A
table˘ {n = n} it = sequence n (lookup it)

-- Permute operation lifted from tables to sequences.
sPermute : {a : Level} {A : Set a} (T : Seq A) {m : ℕ} (p : Fin m ↔ Fin (len T)) → Seq A
sPermute T p = table˘ (permute p (table T))

infix 4 sPermute
syntax sPermute T p  =  p ◈ T

-- Table setoid on vectors of length |len T₁|.
Eq : {ℓ c : Level} (S : Setoid ℓ c) {n : ℕ} → Setoid ℓ c
Eq S {n} = setoid S n

\end{code}
%}}}

%{{{ ø ; _⊕_
MA: These need to be setoid independet, otherwise risk using ≡.setoid!
\begin{code}
∅ : {ℓ : Level} {S₀ : Set ℓ} → Seq S₀
∅ = sequence 0 λ ()

open import Data.Table.Base
import Data.List as L
open Plus -- from FinEquivPlusTimes
open PlusE -- from FinEquivTypeEquiv

infixr 6 _⊕_
_⊕_ : {ℓ : Level} {S₀ : Set ℓ} → Seq S₀ → Seq S₀ → Seq S₀
f ⊕ g = sequence (lf + lg) λ i → [ f ‼_ , g ‼_ ]′ (proj₁ +≃⊎ i)
    where
      lf = len f
      lg = len g
\end{code}
%}}}


%{{{ Sequence equality _≈ₛ_ ; BagRep
\begin{code}
module _ {ℓ c : Level} (S : Setoid ℓ c) where
  open Setoid S using () renaming (Carrier to S₀)

  infixr 3 _≈ₛ_
  record _≈ₛ_ (T₁ T₂ : Seq S₀) : Set (ℓ ⊔ c) where
    constructor _⟨π⟩_
    open Setoid (setoid S (len T₁)) -- Table setoid on vectors of length |len T₁|.
    field
      shuffle : Permutation (len T₁) (len T₂)
      eq : (table T₁) ≈ permute shuffle (table T₂)

    homogenous : len T₁ P.≡ len T₂
    homogenous = ↔⇒≡ shuffle

  open _≈ₛ_

  ≈ₛ-refl : {T : Seq S₀} → T ≈ₛ T
  ≈ₛ-refl {T} = record { shuffle = id ; eq = refl }
    where open Setoid (Eq S)

  interchange : (f : Seq S₀) {m : ℕ} (s : Permutation m (len f)) {k : Fin m}
                (let open Setoid S) → (s ◈ f) ‼ k ≈ f ‼ (s ⟨$⟩ʳ k)
  interchange f {m} s {k} = let open Setoid S in begin⟨ S ⟩
      (s ◈ f) ‼ k
    ≈⟨ refl ⟩
      table˘ (permute s (table f)) ‼ k
    ≈⟨ refl ⟩
      lookup (permute s (table f)) k
    ≈⟨ refl ⟩
      lookup (rearrange (s ⟨$⟩ʳ_) (table f) ) k
    ≈⟨ refl ⟩
      lookup (table f) (s ⟨$⟩ʳ k)
    ≈⟨ refl ⟩
      f ‼ (s ⟨$⟩ʳ k)
    ∎

  ≈ₛ-sym : {f g : Seq S₀} → f ≈ₛ g → g ≈ₛ f
  ≈ₛ-sym {f} {g} (s ⟨π⟩ f≈sg) = let open Setoid S in record
    { shuffle = flip s
    ; eq = λ k → begin⟨ S ⟩
           g ‼ k
         ≡⟨  P.sym (P.cong (g ‼_) (inverseʳ s)) ⟩
           g ‼ (s ⟨$⟩ʳ (s ⟨$⟩ˡ k))
         ≈⟨ refl ⟩
           (s ◈ g) ‼ (s ⟨$⟩ˡ k)
         ≈⟨ sym (f≈sg (s ⟨$⟩ˡ k)) ⟩
           f ‼ (s ⟨$⟩ˡ k)
         ≈⟨ refl ⟩
           (flip s ◈ f) ‼ k
         ∎
    }

  ≈ₛ-trans : {f g h : Seq S₀} → f ≈ₛ g → g ≈ₛ h → f ≈ₛ h
  ≈ₛ-trans {f} {g} {h} (s ⟨π⟩ f≈sg) (r ⟨π⟩ g≈rh) = let open Setoid S in record
    { shuffle = Inv._∘_ r s
    ; eq      = λ k → begin⟨ S ⟩
                f ‼ k
              ≈⟨ f≈sg k ⟩
                (s ◈ g) ‼ k
              ≈⟨ refl ⟩
                g ‼ (s ⟨$⟩ʳ k)
              ≈⟨ g≈rh (s ⟨$⟩ʳ k) ⟩
                (r ◈ h) ‼ (s ⟨$⟩ʳ k)
              ≈⟨ refl ⟩
                (s ◈ (r ◈ h)) ‼ k
              ∎
     }

  ≈ₛ-isEquivalence : IsEquivalence _≈ₛ_
  ≈ₛ-isEquivalence = record { refl = ≈ₛ-refl ; sym = ≈ₛ-sym ; trans = ≈ₛ-trans }

  BagSetoid : Setoid ℓ (c ⊔ ℓ)
  BagSetoid = record
    { Carrier         =   Seq S₀
    ; _≈_             =   _≈ₛ_
    ; isEquivalence   =   ≈ₛ-isEquivalence
    }
\end{code}
%}}}

%{{{ singleton ; singleton-cong
\begin{code}
  singleton : S₀ → Seq S₀
  singleton x = sequence 1 λ{ _ → x }

  open Setoid S using () renaming (_≈_ to _≈₀_)

  singleton-cong : {x y : S₀} → x ≈₀ y → singleton x ≈ₛ singleton y
  singleton-cong {x} {y} x≈y = record
    { shuffle = Inv.id
    ; eq      = λ _ → x≈y
    }
\end{code}
%}}}

%{{{ Permutation is equivalent to _fin≃_ (which is Fin n ≃ Fin m)
\begin{code}
  Perm⇒fin≃ : {m n : ℕ} → Permutation m n → m fin≃ n
  Perm⇒fin≃ p = _⟨$⟩_ (to p) , Equiv.qinv (_⟨$⟩_ (from p)) (right-inverse-of p) (left-inverse-of p)
    where open Inv.Inverse; open Function.Equality using (_⟨$⟩_)

  fin≃⇒Perm : {m n : ℕ} → m fin≃ n → Permutation m n
  fin≃⇒Perm (f , Equiv.qinv b α β) = record { to = P.→-to-⟶ f ; from = P.→-to-⟶ b
    ; inverse-of = record { left-inverse-of = β ; right-inverse-of = α } }

  ≡⇒≈₀ : {x y : S₀} → x P.≡ y → x ≈₀ y
  ≡⇒≈₀ P.refl = Setoid.refl S

\end{code}
%}}}


%{{{ holes: commutativeMonoid
\begin{code}

  [_,_]′∘swap : {ℓ ℓ′ : Level} {X Y : Set ℓ} {Z : Set ℓ′} {f : X → Z} {g : Y → Z} → (i : X ⊎ Y) → [ g , f ]′ (swap₊ i) P.≡ [ f , g ]′ i
  [_,_]′∘swap (inj₁ x) = P.refl
  [_,_]′∘swap (inj₂ y) = P.refl

  expand-swap+ : {m n : ℕ} (i : Fin (m + n)) → proj₁ (+≃⊎ {n} {m}) (proj₁ (swap+ {m}) i) P.≡ swap₊ (proj₁ +≃⊎ i)
  expand-swap+ i = P.trans (P.cong (proj₁ +≃⊎) (β₁ i)) (
                   P.trans (Equiv.isqinv.α (proj₂ +≃⊎) (proj₁ (swap₊equiv ● +≃⊎) i)) (β₁ _))

  ⊕-comm : {f g : Seq S₀} → f ⊕ g  ≈ₛ  g ⊕ f
  ⊕-comm {f} {g} = record
    { shuffle = fin≃⇒Perm (swap+ {lf} {lg})
    ; eq      = λ i → Setoid.sym S (begin⟨ S ⟩
      lookup (permute (fin≃⇒Perm (swap+ {lf})) (table (g ⊕ f))) i ≈⟨ Setoid.refl S ⟩ -- unwind lots of definitions
      [ g ‼_ , f ‼_ ]′ (proj₁ +≃⊎ (proj₁ (swap+ {lf}) i))          ≡⟨ P.cong [ g ‼_ , f ‼_ ]′ (expand-swap+ i) ⟩
      [ g ‼_ , f ‼_ ]′ (swap₊ (proj₁ +≃⊎ i))                       ≡⟨ [_,_]′∘swap {f = f ‼_} (proj₁ +≃⊎ i) ⟩
      [ f ‼_ , g ‼_ ]′ (proj₁ +≃⊎ i)                               ≈⟨ Setoid.refl S ⟩ -- rewind definitions
      lookup (table (f ⊕ g)) i ∎)
    }
    where
      lf = len f
      lg = len g

  ⊕-assoc : {f g h : Seq S₀} → (f ⊕ g) ⊕ h  ≈ₛ  f ⊕ (g ⊕ h)
  ⊕-assoc {f} {g} {h} = record
    { shuffle = fin≃⇒Perm (assocr+ {len f} {len g} {len h})
    ; eq      = λ i → begin⟨ S ⟩
      lookup (table ((f ⊕ g) ⊕ h)) i                                                             ≡⟨ P.refl ⟩
      [ (λ j → [ f ‼_ , g ‼_ ]′ (proj₁ +≃⊎ j)) , h ‼_ ]′ (proj₁ +≃⊎ i)                            ≡⟨ P.sym (absorb₂ _) ⟩
      [ [ f ‼_ , g ‼_ ]′ , h ‼_ ]′ (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i))                                   ≡⟨ P.sym (reassocl (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i))) ⟩
      [ f ‼_ , [ g ‼_ , h ‼_ ]′ ]′ (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i)))                 ≡⟨ P.sym (absorb₁ _) ⟩
      [ f ‼_ , (λ j → [ g ‼_ , h ‼_ ]′ (proj₁ +≃⊎ j)) ]′
        (gg (id≃ ⊎≃ +≃⊎) (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i))))                          ≡⟨ P.sym (P.cong [ f ‼_ , (λ j → [ g ‼_ , h ‼_ ]′ (proj₁ +≃⊎ j)) ]′ (left-cancel i)) ⟩
      [ f ‼_ , (λ j → [ g ‼_ , h ‼_ ]′ (proj₁ +≃⊎ j)) ]′ (proj₁ +≃⊎ (proj₁ (assocr+ {len f}) i))  ≡⟨ P.refl ⟩
      lookup (permute (fin≃⇒Perm (assocr+ {len f})) (table (f ⊕ g ⊕ h))) i ∎
    }
    where
    open Equiv
    open Inv.Inverse; open import Function using (_∘_)
    open TypeEquiv using (assocl₊equiv; assocr₊equiv)
    module _ where
      open P.≡-Reasoning using (begin_) renaming (_∎ to _∎≡; _≡⟨_⟩_ to _≣⟨_⟩_)
      left-cancel : {m n o : ℕ} → (i : Fin ((m + n) + o)) → proj₁ (+≃⊎ {m} {n + o}) (proj₁ (assocr+ {m} {n} {o}) i) P.≡
          gg (id≃ ⊎≃ +≃⊎) (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i)))
      left-cancel {m} {n} {o}  i = begin
        proj₁ (+≃⊎ {m} {n + o}) (proj₁ (assocr+ {m} {n} {o}) i)                                ≣⟨ P.refl ⟩
        gg ⊎≃+ (gg (assocl+ {m}) i)                                                            ≣⟨ cong∘l (gg ⊎≃+) β₂ i ⟩
        gg ⊎≃+ (gg (⊎≃+ ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎ {m}) (gg ⊎≃+ i))              ≣⟨ cong∘l (gg ⊎≃+) β₂ (gg ⊎≃+ i) ⟩
        gg ⊎≃+ (gg (assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎ {m}) (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i)))         ≣⟨ cong∘l (gg ⊎≃+) β₂ _ ⟩
        gg ⊎≃+ (gg (id≃ ⊎≃ +≃⊎ ● +≃⊎ {m}) (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i))))      ≣⟨ cong∘l (gg ⊎≃+) β₂ _ ⟩
        gg ⊎≃+ (gg (+≃⊎ {m}) (gg (id≃ ⊎≃ +≃⊎) (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i))))) ≣⟨ isqinv.β (proj₂ ⊎≃+) _ ⟩
        gg (id≃ ⊎≃ +≃⊎) (gg assocl₊equiv (gg (⊎≃+ ⊎≃ id≃) (gg ⊎≃+ i)))                         ∎≡
        -- assocl+ = ⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎ {m}
      absorb₁ : {m n o : ℕ} {D : Set ℓ} {f : Fin m → D} {g : Fin n → D} {h : Fin o → D} (i : Fin m ⊎ Fin n ⊎ Fin o ) →
                [ f , (λ j → [ g , h ]′ (proj₁ +≃⊎ j)) ]′ (gg (id≃ ⊎≃ +≃⊎) i) P.≡
                [ f , [ g , h ]′ ]′ i
      absorb₁ {f = f} {g} {h} (inj₁ x) = cong∘l [ f , (λ j → [ g , h ]′ (proj₁ +≃⊎ j)) ]′ β⊎₂ (inj₁ x)
      absorb₁ {f = f} {g} {h} (inj₂ (inj₁ x)) = P.trans
        (cong∘l [ f , (λ j → [ g , h ]′ (proj₁ +≃⊎ j)) ]′ β⊎₂ (inj₂ (inj₁ x)))
        (P.cong [ g , h ]′ (isqinv.α (proj₂ +≃⊎) (inj₁ x)))
      absorb₁ {f = f} {g} {h} (inj₂ (inj₂ y)) = P.trans
        (cong∘l [ f , (λ j → [ g , h ]′ (proj₁ +≃⊎ j)) ]′ β⊎₂ (inj₂ (inj₂ y)))
        (P.cong [ g , h ]′ (isqinv.α (proj₂ +≃⊎) (inj₂ y)))

      reassocl : {m n o : ℕ} {D : Set ℓ} {a : Fin m → D} {b : Fin n → D} {c : Fin o → D} (i : (Fin m ⊎ Fin n) ⊎ Fin o) →
        [ a , [ b , c ]′ ]′ (gg assocl₊equiv i) P.≡ [ [ a , b ]′ , c ]′ i
      reassocl (inj₁ (inj₁ x)) = P.refl
      reassocl (inj₁ (inj₂ y)) = P.refl
      reassocl (inj₂ y) = P.refl

      absorb₂ : {m n o : ℕ} {D : Set ℓ} {f : Fin m → D} {g : Fin n → D} {h : Fin o → D} (i : Fin (m + n) ⊎ Fin o ) →
                [ [ f , g ]′ , h ]′ (gg (⊎≃+ ⊎≃ id≃) i) P.≡
                [ (λ j → [ f , g ]′ (proj₁ +≃⊎ j)) , h ]′ i
      absorb₂ {f = f} {g} {h} (inj₁ x) = P.cong [ [ f , g ]′ , h ]′ (β⊎₂ (inj₁ x))
      absorb₂ {f = f} {g} {h} (inj₂ y) = P.cong [ [ f , g ]′ , h ]′ (β⊎₂ (inj₂ y))

  merge-map : {ℓ ℓ′ : Level} {B : Set ℓ} → (z : Fin 0 ⊎ B) → TypeEquiv.unite₊ {ℓ′} (Data.Sum.map (proj₁ F0≃⊥) id₀ z) P.≡ [ (λ ()) , id₀ ]′ z
  merge-map (inj₁ ())
  merge-map (inj₂ y) = P.refl

  lookup-map : {x : Seq S₀} (c : Fin 0 ⊎ Fin (len x)) →
    x ‼ ([ (λ ()) , id₀ ]′ c) P.≡ [ ∅ ‼_ , x ‼_ ]′ c
  lookup-map (inj₁ ())
  lookup-map (inj₂ y) = P.refl

  table-unite+ : {ℓ : Level} (x : Seq S₀) → Setoid._≈_ (setoid S (len (∅ ⊕ x))) (table (∅ ⊕ x)) (permute (fin≃⇒Perm unite+) (table x))
  table-unite+ {ℓ} x = λ i → begin⟨ S ⟩
    lookup (table (∅ ⊕ x)) i                                             ≡⟨ P.refl ⟩
    [ (λ () ) , x ‼_ ]′ (proj₁ +≃⊎ i)                                     ≡⟨ P.sym (lookup-map (proj₁ +≃⊎ i)) ⟩
    x ‼ ([ (λ ()) , id₀ ]′ (proj₁ +≃⊎ i))                                 ≡⟨ P.sym (P.cong (x ‼_) (merge-map (proj₁ +≃⊎ i))) ⟩
    x ‼ (TypeEquiv.unite₊ (Data.Sum.map (proj₁ F0≃⊥) id₀ (proj₁ +≃⊎ i)))  ≡⟨ P.sym (P.cong (x ‼_) ((β₁ ⊙ cong∘l (proj₁ unite₊equiv) (β₁ ⊙ cong∘r _ β⊎₁)) i)) ⟩
    x ‼ (proj₁ (unite₊equiv ● F0≃⊥ ⊎≃ id≃ ● +≃⊎)) i                       ≡⟨ P.refl ⟩
    x ‼ (Inv.Inverse.to (fin≃⇒Perm unite+) Π.⟨$⟩ i)                        ≡⟨ P.refl ⟩
    lookup (permute (fin≃⇒Perm unite+) (table x)) i ∎

  map-map : {ℓ ℓ′ ℓ′′ : Level} {A C : Set ℓ} {B D : Set ℓ′} {E : Set ℓ′′} {c : A → B} {d : C → D} {a : B → E} {b : D → E}
    (i : A ⊎ C) → [ a , b ]′ (Data.Sum.map c d i) P.≡ [ a ∘₀ c , b ∘₀ d ]′ i
  map-map (inj₁ x) = P.refl
  map-map (inj₂ y) = P.refl

  switch-map : {ℓ ℓ′ : Level} {A B : Set ℓ} {a c : A → S₀} {b d : B → S₀} →
    (∀ i → a i ≈₀ c i) → (∀ i → b i ≈₀ d i) → (∀ j → [ a , b ]′ j ≈₀ [ c , d ]′ j)
  switch-map a≐c b≐d (inj₁ x) = a≐c x
  switch-map a≐c b≐d (inj₂ y) = b≐d y

  commutativeMonoid : CommutativeMonoid ℓ (ℓ ⊔ c)
  commutativeMonoid = record
    { Carrier               =   Seq S₀
    ; _≈_                   =   _≈ₛ_
    ; _∙_                   =   _⊕_
    ; ε                     =   ∅
    ; isCommutativeMonoid   =   record
      { isSemigroup   =   record
        { isEquivalence = ≈ₛ-isEquivalence
        ; assoc = λ f g h → ⊕-assoc {f} {g} {h}
        ; ∙-cong = λ {x} {y} {u} {v} x≈y u≈v → (fin≃⇒Perm (Perm⇒fin≃ (shuffle x≈y) PlusE.+F Perm⇒fin≃ (shuffle u≈v))) ⟨π⟩
           λ i →
           let x≃y = Perm⇒fin≃ (shuffle x≈y) in
           let u≃v = Perm⇒fin≃ (shuffle u≈v) in
           let j = proj₁ +≃⊎ i in
           begin⟨ S ⟩
           [ _‼_ x , _‼_ u ]′ j
               ≈⟨ Setoid.sym S (switch-map {_} {ℓ} (λ j → Setoid.sym S (eq x≈y j)) (λ j → Setoid.sym S (eq u≈v j)) j) ⟩
           [ y ‼_ ∘₀ (proj₁ x≃y) , v ‼_ ∘₀ (proj₁ u≃v) ]′ j
              ≡⟨ P.sym (map-map (proj₁ +≃⊎ i)) ⟩
           [ _‼_ y , _‼_ v ]′ (Data.Sum.map (proj₁ x≃y) (proj₁ u≃v) j)
               ≡⟨ P.sym (P.cong [ _‼_ y , _‼_ v ]′ (Equiv.isqinv.β (proj₂ ⊎≃+) (Data.Sum.map (proj₁ x≃y) (proj₁ u≃v) j))) ⟩
           [ _‼_ y , _‼_ v ]′ (proj₁ +≃⊎ (proj₁ ⊎≃+ (Data.Sum.map (proj₁ x≃y) (proj₁ u≃v) j)))
               ≡⟨ P.sym (P.cong (λ x → [ _‼_ y , _‼_ v ]′ (proj₁ +≃⊎ x))
                       (P.trans (β₁ _)
                       (P.cong (proj₁ ⊎≃+) (P.trans (β₁ i) (β⊎₁ _))))) ⟩
           [ _‼_ y , _‼_ v ]′ (proj₁ +≃⊎ (proj₁ (x≃y PlusE.+F u≃v) i)) ∎
      }
      ; identityˡ     =   λ x → (fin≃⇒Perm unite+) ⟨π⟩ table-unite+ {ℓ} x
      ; comm          =   λ f g → ⊕-comm {f} {g}
      }
    }
\end{code}

A property useful for Functors related to commutative monoids. Phrased in terms of
tables (it will be used for Bags later). First argument explict as we do induction on it.
\begin{code}
module _ {ℓ c : Level} {S : Setoid ℓ c} (CMS : CommMonoid S) where
  open Setoid S using (_≈_) renaming (Carrier to S₀)
  open CommMonoid CMS
  open import Data.Table.Base
  open import Algebra.Operations.CommutativeMonoid (asCommutativeMonoid CMS)
  open import Algebra.Properties.CommutativeMonoid (asCommutativeMonoid CMS)

  sumₜ-homo : (m : ℕ) {n : ℕ} {f : Fin m → S₀} {g : Fin n → S₀} →
    sumₜ (table (sequence m f ⊕ sequence n g)) ≈ sumₜ (table (sequence m f)) * sumₜ (table (sequence n g))
  sumₜ-homo ℕ.zero {_} {_} {g} = ≈.sym (left-unit (sumₜ (tabulate g)))
  sumₜ-homo (ℕ.suc m) {n} {f} {g} = begin⟨ S ⟩
    sumₜ (table (sequence (ℕ.suc m) f ⊕ sequence n g))              ≈⟨ {!!} ⟩
    sumₜ (table (sequence (ℕ.suc m) f)) * sumₜ (table (sequence n g)) ∎
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
