\section{Belongs}

Rather than over-generalize to a type of locations for an arbitrary
predicate, stick to simply working with locations, and making them
into a type.

%{{{ Imports
\begin{code}
module Belongs where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary using (Setoid ; IsEquivalence ; Rel ;
  Reflexive ; Symmetric ; Transitive)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_ ; _⟨$⟩_ ; cong )
open import Function          using (_$_) renaming (id to id₀; _∘_ to _⊚_)
open import Function.Equivalence using (Equivalence)

open import Data.List     using (List; []; _++_; _∷_; map)
open import Data.Nat      using (ℕ; zero; suc)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp

open import TypeEquiv using (swap₊)
-- open import SetoidSetoid

\end{code}

Convenient syntax for when we need to specify which |Setoid|'s equality we are
talking about.

\begin{code}
infix 4 inSetoidEquiv
inSetoidEquiv : {ℓS ℓs : Level} → (S : Setoid ℓS ℓs) → (x y : Setoid.Carrier S) → Set ℓs
inSetoidEquiv = Setoid._≈_

syntax inSetoidEquiv S x y = x ≈⌊ S ⌋ y
\end{code}

A few convenient combinators for equational reasoning in |Setoid|.

\savecolumns
\begin{code}
module SetoidCombinators {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S renaming (trans to _⟨≈≈⟩_)
  _⟨≈˘≈⟩_ : {a b c : Carrier} → b ≈ a → b ≈ c → a ≈ c
  _⟨≈˘≈⟩_ = λ b≈a b≈c → sym b≈a ⟨≈≈⟩ b≈c
  _⟨≈≈˘⟩_ : {a b c : Carrier} → a ≈ b → c ≈ b → a ≈ c
  _⟨≈≈˘⟩_ = λ a≈b c≈b → a≈b ⟨≈≈⟩ sym c≈b
  _⟨≈˘≈˘⟩_ : {a b c : Carrier} → b ≈ a → c ≈ b → a ≈ c
  _⟨≈˘≈˘⟩_ = λ b≈a c≈b → b≈a ⟨≈˘≈⟩ sym c≈b
\end{code}
%}}}

The goal of this section is to capture a notion that we have an element |x|
belonging to a list |xs|.  We want to know \emph{which} |x ∈ xs| is the witness,
as there could be many |x|'s in |xs|.
Furthermore, we are in the |Setoid| setting, thus we do not care about |x| itself,
any |y| such that |x ≈ y| will do, as long as it is in the ``right'' location.

And then we want to capture the idea of when two such are equivalent --
when is it that |Belongs xs| is just as good as |Belongs ys|?

For the purposes of |CommMonoid|, all we need is some notion
of Bag Equivalence.  We will aim for that, without generalizing too much.

%{{{ \subsection{|Location| and |Membership|}
\subsection{|Location|}
|Setoid|-based variant of Any, but without the extra property.  Nevertheless,
much inspiration came from reading
|Data.List.Any| and |Data.List.Any.Properties|.

First, a notion of |Location| in a list, but suited for our purposes.
\begin{code}
module Locations {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  infix 4 _∈₀_

  open Setoid S renaming (Carrier to A)
  data _∈₀_  : A → List A → Set (ℓS ⊔ ℓs) where
    here  : {x a : A} {xs : List A} (sm : a ≈ x)   → a ∈₀ (x ∷ xs)
    there : {x a : A} {xs : List A} (pxs : a ∈₀ xs) → a ∈₀ (x ∷ xs)
  open _∈₀_ public

  infix 4 ∈₀-Setoid
  ∈₀-Setoid : Setoid.Carrier S → List (Setoid.Carrier S) → Set (ℓS ⊔ ℓs)
  ∈₀-Setoid = _∈₀_

  syntax ∈₀-Setoid S x xs = x ∈[ S ] xs
\end{code}

One instinct is go go with natural numbers directly; while this
has the ``right'' computational content, that is harder for
deduction.
Nevertheless, the 'location' function is straightforward:
\begin{code}
  toℕ : {x : A} {xs : List A} → x ∈₀ xs → ℕ
  toℕ (here _) = 0
  toℕ (there pf) = suc (toℕ pf)
\end{code}

We need to know when two locations are the same.

\begin{code}
module LocEquiv {ℓS ℓs} (S : Setoid ℓS ℓs) where
  open Setoid S renaming (Carrier to A)
  open Locations S
  infix 3 _≋_
  data _≋_ : {y y' : A} {ys : List A} (loc : y ∈₀ ys) (loc' : y' ∈₀ ys) → Set (ℓS ⊔ ℓs) where
    hereEq : {xs : List A} {x y z : A}
           → (x≈z : x ≈ z) → (y≈z : y ≈ z)
           → _≋_ (here {x = z} {x} {xs} x≈z) (here {x = z} {y} {xs} y≈z)
    thereEq : {xs : List A} {x x' z : A} {loc : x ∈₀ xs} {loc' : x' ∈₀ xs}
            → loc ≋ loc' → _≋_ (there {x = z} loc) (there {x = z} loc')
\end{code}

These are seen to be another form of natural numbers as well.

It is on purpose that |_≋_| preserves positions.
Suppose that we take the setoid of the Latin alphabet,
with |_≈_| identifying upper and lower case.
There should be 3 elements of |_≋_| for |a ∷ A ∷ a ∷ []|, not 6.
When we get to defining |BagEq|,
there will be 6 different ways in which that list, as a Bag, is equivalent to itself.

|_≋_| is an equivalence relation, and |_≡_| implies |_≋_|.
\begin{code}
  ≋-refl : {x : A} {xs : List A} {p : x ∈₀ xs} → p ≋ p
  ≋-refl {p = here a≈x} = hereEq a≈x a≈x
  ≋-refl {p = there p} = thereEq ≋-refl

  ≋-sym : {x : A} {xs : List A} {p q : x ∈₀ xs} → p ≋ q → q ≋ p
  ≋-sym (hereEq a≈x b≈x) = hereEq b≈x a≈x
  ≋-sym (thereEq eq) = thereEq (≋-sym eq)

  ≋-trans : {x : A} {xs : List A} {p q r : x ∈₀ xs}
          → p ≋ q → q ≋ r → p ≋ r
  ≋-trans (hereEq a≈x b≈x) (hereEq c≈y d≈y) = hereEq _ _
  ≋-trans (thereEq e) (thereEq f) = thereEq (≋-trans e f)

  ≡→≋ : {x : A} {xs : List A} {p q : x ∈₀ xs} → p ≡ q → p ≋ q
  ≡→≋ ≡.refl = ≋-refl
\end{code}

Furthermore, it is important to notice that |x ∈₀ xs ≋ y ∈₀ xs| implies |x ≈ y|.
\begin{code}
  open SetoidCombinators S
  ≋→≈ : {x y : A} {xs : List A} (x∈xs : x ∈₀ xs) (y∈xs : y ∈₀ xs) → x∈xs ≋ y∈xs → x ≈ y
  ≋→≈ (here sm) .(here y≈z) (hereEq .sm y≈z) = sm ⟨≈≈˘⟩ y≈z
  ≋→≈ (there xx) .(there _) (thereEq pf) = ≋→≈ xx _ pf
\end{code}
%}}}

%{{{ \subsection{Membership module}: _∈_
\subsection{Membership module}

We now have all the ingredients to show that locations (|_∈₀_|) form a |Setoid|.
\begin{code}
module Membership {ℓS ℓs} (S : Setoid ℓS ℓs) where
  infix 4 _∈_

  open Setoid S
  open Locations S
  open LocEquiv S

  _∈_ : Carrier → List Carrier → Setoid (ℓS ⊔ ℓs) (ℓS ⊔ ℓs)
  x ∈ xs = record
    { Carrier         =   x ∈₀ xs
    ; _≈_             =   _≋_
    ; isEquivalence   = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
    }

  ≡→∈ : {x : Carrier} {xs ys : List Carrier} → xs ≡ ys → (x ∈ xs) ≅ (x ∈ ys)
  ≡→∈ ≡.refl = ≅-refl
\end{code}
%}}}

%{{{ \subsection{Obsolete?}
\subsection{Obsolete}

\restorecolumns
Some currently unused definition.
|≈to x| is an equivalence-preserving mapping from |S|
to |ProofSetoid|; it maps
elements |y| of |Carrier S| to the proofs that "|x ≈ₛ y|".
In HoTT, this would be called |isContr| if we were working
with respect to propositional equality.

\begin{spec}
  ≈to : Carrier → (S ⟶ ProofSetoid ℓs (ℓS ⊔ ℓs))
  ≈to x = record
    { _⟨$⟩_ = λ s → _≈S_ {S = S} x s
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈≈⟩ i≈j  ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈≈˘⟩ i≈j ; cong = λ _ → tt } } }
\end{spec}

\begin{spec}
module MembershipUtils {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S
  open Locations S ; open Loc S


  ∈₀-subst₁ : {x y : Carrier} {xs : List Carrier} → x ≈ y → x ∈₀ xs → y ∈₀ xs
  ∈₀-subst₁ {x} {y} {.(_ ∷ _)} x≈y (here a≈x px) = here a≈x (sym x≈y ⟨≈≈⟩ px)
  ∈₀-subst₁ {x} {y} {.(_ ∷ _)} x≈y (there x∈xs) = there (∈₀-subst₁ x≈y x∈xs)

  ∈₀-subst₁-cong : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y)
                  {i j : x ∈₀ xs} → i ≋ j → ∈₀-subst₁ x≈y i ≋ ∈₀-subst₁ x≈y j
  ∈₀-subst₁-cong x≈y (hereEq px qy x≈z y≈z) = hereEq (sym x≈y ⟨≈≈⟩ px ) (sym x≈y ⟨≈≈⟩ qy) x≈z y≈z
  ∈₀-subst₁-cong x≈y (thereEq i≋j) = thereEq (∈₀-subst₁-cong x≈y i≋j)

  ∈₀-subst₁-equiv  : {x y : Carrier} {xs : List Carrier} → x ≈ y → (x ∈ xs) ≅ (y ∈ xs)
  ∈₀-subst₁-equiv {x} {y} {xs} x≈y = record
    { to = record { _⟨$⟩_ = ∈₀-subst₁ x≈y ; cong = ∈₀-subst₁-cong x≈y }
    ; from = record { _⟨$⟩_ = ∈₀-subst₁ (sym x≈y) ; cong = ∈₀-subst₁-cong′ }
    ; inverse-of = record { left-inverse-of = left-inv ; right-inverse-of = right-inv } }
    where

      ∈₀-subst₁-cong′ : ∀ {ys} {i j : y ∈₀ ys} → i ≋ j → ∈₀-subst₁ (sym x≈y) i ≋ ∈₀-subst₁ (sym x≈y) j
      ∈₀-subst₁-cong′ (hereEq px qy x≈z y≈z) = hereEq (sym (sym x≈y) ⟨≈≈⟩ px) (sym (sym x≈y) ⟨≈≈⟩ qy) x≈z y≈z
      ∈₀-subst₁-cong′ (thereEq i≋j) = thereEq (∈₀-subst₁-cong′ i≋j)

      left-inv : ∀ {ys} (x∈ys : x ∈₀ ys) → ∈₀-subst₁ (sym x≈y) (∈₀-subst₁ x≈y x∈ys) ≋ x∈ys
      left-inv (here sm px) = hereEq (sym (sym x≈y) ⟨≈≈⟩ (sym x≈y ⟨≈≈⟩ px)) px sm sm
      left-inv (there x∈ys) = thereEq (left-inv x∈ys)

      right-inv : ∀ {ys} (y∈ys : y ∈₀ ys) → ∈₀-subst₁ x≈y (∈₀-subst₁ (sym x≈y) y∈ys) ≋ y∈ys
      right-inv (here sm px) = hereEq (sym x≈y ⟨≈≈⟩ (sym (sym x≈y) ⟨≈≈⟩ px)) px sm sm
      right-inv (there y∈ys) = thereEq (right-inv y∈ys)
\end{spec}
%}}}

%{{{ \subsection{|BagEq|}
\subsection{|BagEq|}

Fundamental definition: two Bags, represented as |List Carrier| are equivalent
if and only if there exists a permutation between their |Setoid| of positions,
and this is independent of the representative.

\begin{code}
  record BagEq (xs ys : List Carrier) : Set (ℓS ⊔ ℓs) where
    constructor BE
    field
      permut : {x : Carrier} → (x ∈ xs) ≅ (x ∈ ys)
      repr-indep-to : {x x' : Carrier} {x∈xs : x ∈₀ xs} {x'∈xs : x' ∈₀ xs} →
                     (x∈xs ≋ x'∈xs) → _≅_.to (permut {x}) ⟨$⟩ x∈xs ≋ _≅_.to (permut {x'}) ⟨$⟩ x'∈xs
      repr-indep-fr : {y y' : Carrier} {y∈ys : y ∈₀ ys} {y'∈ys : y' ∈₀ ys} →
                     (y∈ys ≋ y'∈ys) → _≅_.from (permut {y}) ⟨$⟩ y∈ys ≋ _≅_.from (permut {y'}) ⟨$⟩ y'∈ys

  open BagEq

  BE-refl : {xs : List Carrier} → BagEq xs xs
  BE-refl = BE ≅-refl id₀ id₀

  BE-sym : {xs ys : List Carrier} → BagEq xs ys → BagEq ys xs
  BE-sym (BE p ind-to ind-fr) = BE (≅-sym p) ind-fr ind-to

  BE-trans : {xs ys zs : List Carrier} → BagEq xs ys → BagEq ys zs → BagEq xs zs
  BE-trans (BE p₀ to₀ fr₀) (BE p₁ to₁ fr₁) =
    BE (≅-trans p₀ p₁) (to₁ ⊚ to₀) (fr₀ ⊚ fr₁)
\end{code}

\begin{spec}
  ∈₀-Subst₂ : {x : Carrier} {xs ys : List Carrier} → BagEq xs ys → x ∈ xs ⟶ x ∈ ys
  ∈₀-Subst₂ {x} xs≅ys = _≅_.to (permut xs≅ys {x})

  ∈₀-subst₂ : {x : Carrier} {xs ys : List Carrier} → BagEq xs ys → x ∈₀ xs → x ∈₀ ys
  ∈₀-subst₂ xs≅ys x∈xs = ∈₀-Subst₂ xs≅ys ⟨$⟩ x∈xs

  ∈₀-subst₂-cong  : {x : Carrier} {xs ys : List Carrier} (xs≅ys : BagEq xs ys)
                  → {p q : x ∈₀ xs}
                  → p ≋ q
                  → ∈₀-subst₂ xs≅ys p ≋ ∈₀-subst₂ xs≅ys q
  ∈₀-subst₂-cong xs≅ys = cong (∈₀-Subst₂ xs≅ys)

  ∈₀-subst₁-elim : {x : Carrier} {xs : List Carrier} (x∈xs : x ∈₀ xs) →
    ∈₀-subst₁ refl x∈xs ≋ x∈xs
  ∈₀-subst₁-elim (here sm px) = hereEq (refl ⟨≈˘≈⟩ px) px sm sm
  ∈₀-subst₁-elim (there x∈xs) = thereEq (∈₀-subst₁-elim x∈xs)

  -- note how the back-and-forth is clearly apparent below
  ∈₀-subst₁-sym : {a b : Carrier} {xs : List Carrier} {a≈b : a ≈ b}
    {a∈xs : a ∈₀ xs} {b∈xs : b ∈₀ xs} → ∈₀-subst₁ a≈b a∈xs ≋ b∈xs →
    ∈₀-subst₁ (sym a≈b) b∈xs ≋ a∈xs
  ∈₀-subst₁-sym {a≈b = a≈b} {here sm px} {here sm₁ px₁} (hereEq _ .px₁ .sm .sm₁) = hereEq (sym (sym a≈b) ⟨≈≈⟩ px₁) px sm₁ sm
  ∈₀-subst₁-sym {a∈xs = there a∈xs} {here sm px} ()
  ∈₀-subst₁-sym {a∈xs = here sm px} {there b∈xs} ()
  ∈₀-subst₁-sym {a∈xs = there a∈xs} {there b∈xs} (thereEq pf) = thereEq (∈₀-subst₁-sym pf)

  ∈₀-subst₁-trans : {a b c : Carrier} {xs : List Carrier} {a≈b : a ≈ b}
    {b≈c : b ≈ c} {a∈xs : a ∈₀ xs} {b∈xs : b ∈₀ xs} {c∈xs : c ∈₀ xs} →
    ∈₀-subst₁ a≈b a∈xs ≋ b∈xs → ∈₀-subst₁ b≈c b∈xs ≋ c∈xs →
    ∈₀-subst₁ (a≈b ⟨≈≈⟩ b≈c) a∈xs ≋ c∈xs
  ∈₀-subst₁-trans {a≈b = a≈b} {b≈c} {here sm px} {.(here y≈z qy)} {.(here z≈w qz)} (hereEq ._ qy .sm y≈z) (hereEq ._ qz foo z≈w) = hereEq (sym (a≈b ⟨≈≈⟩ b≈c) ⟨≈≈⟩ px) qz sm z≈w
  ∈₀-subst₁-trans {a≈b = a≈b} {b≈c} {there a∈xs} {there b∈xs} {.(there _)} (thereEq pp) (thereEq qq) = thereEq (∈₀-subst₁-trans pp qq)
\end{spec}
%}}}

%{{{ \subsection{|++≅ : ⋯ → (x ∈ xs ⊎⊎ x ∈ ys) ≅ x ∈ (xs ++ ys)|}
\subsection{|++≅ : ⋯ → (x ∈ xs ⊎⊎ x ∈ ys) ≅ x ∈ (xs ++ ys)|}
\begin{code}
module ConcatTo⊎⊎ {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S renaming (Carrier to A)
  open LocEquiv S
  open Locations S
  open Membership S

  ++≅ : {xs ys : List A } {x : A} → (x ∈ xs ⊎⊎ x ∈ ys) ≅ (x ∈ (xs ++ ys))
  ++≅ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong =  ⊎→++-cong  }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = new-cong xs }
    ; inverse-of = record
      { left-inverse-of = lefty xs
      ; right-inverse-of = righty xs
      }
    }
    where
      -- ``ealier''
      ⊎→ˡ : {ws zs : List A} {x : A} → x ∈₀ ws → x ∈₀ (ws ++ zs)
      ⊎→ˡ (here a≈x) = here a≈x
      ⊎→ˡ (there p) = there (⊎→ˡ p)

      yo : {ws zs : List A} {z : A} {a b : z ∈₀ ws} → a ≋ b   →   ⊎→ˡ {ws} {zs} a  ≋  ⊎→ˡ b
      yo (hereEq _ _) = hereEq _ _
      yo (thereEq pf) = thereEq (yo pf)

      -- ``later''
      ⊎→ʳ : ∀ {x} xs {ys} → x ∈₀ ys → x ∈₀ (xs ++ ys)
      ⊎→ʳ []       p = p
      ⊎→ʳ (x ∷ xs) p = there (⊎→ʳ xs p)

      oy : {z : A} (xs : List A) {x y : z ∈₀ ys} → x ≋ y   →   ⊎→ʳ xs x  ≋  ⊎→ʳ xs y
      oy [] pf = pf
      oy (x ∷ xs) pf = thereEq (oy xs pf)

      ⊎→++ : ∀ {zs ws z} → (z ∈₀ zs ⊎ z ∈₀ ws) → z ∈₀ (zs ++ ws)
      ⊎→++      (inj₁ x) = ⊎→ˡ x
      ⊎→++ {zs} (inj₂ y) = ⊎→ʳ zs y

      ++→⊎ : ∀ xs {ys} {z} → z ∈₀ (xs ++ ys) → z ∈₀ xs ⊎ z ∈₀ ys
      ++→⊎ []             p    = inj₂ p
      ++→⊎ (x ∷ l) (here  _) = inj₁ (here _)
      ++→⊎ (x ∷ l) (there p)   = (there ⊎₁ id₀) (++→⊎ l p)

      ⊎→++-cong : {x : A} {a b : x ∈₀ xs ⊎ x ∈₀ ys} → (_≋_ ∥ _≋_) a b → ⊎→++ a ≋ ⊎→++ b
      ⊎→++-cong (left  x₁∼x₂)  =  yo x₁∼x₂
      ⊎→++-cong (right y₁∼y₂)  =  oy xs y₁∼y₂

      ∽∥∽-cong   :  {x : A} {xs ys us vs : List A}
                    (F : x ∈₀ xs → x ∈₀ us)
                    (F-cong : {p q : x ∈₀ xs} → p ≋ q → F p ≋ F q)
                    (G : x ∈₀ ys → x ∈₀ vs)
                    (G-cong : {p q : x ∈₀ ys} → p ≋ q → G p ≋ G q)
                    → {pf pf' : x ∈₀ xs ⊎ x ∈₀ ys}
                    → (_≋_ ∥ _≋_) pf pf' → (_≋_ ∥ _≋_) ( (F ⊎₁ G) pf) ((F ⊎₁ G) pf')
      ∽∥∽-cong F F-cong G G-cong (left x~₁y) = left (F-cong x~₁y)
      ∽∥∽-cong F F-cong G G-cong (right x~₂y) = right (G-cong x~₂y)

      new-cong : {x : A} (xs : List A) {i j : x ∈₀ (xs ++ ys)} → i ≋ j → (_≋_ ∥ _≋_) (++→⊎ xs i) (++→⊎ xs j)
      new-cong [] pf = right pf
      new-cong (x ∷ xs) (hereEq _ _) = left (hereEq _ _)
      new-cong (x ∷ xs) (thereEq pf) = ∽∥∽-cong there thereEq id₀ id₀ (new-cong xs pf)

      lefty : {x : A} (xs {ys} : List A) (p : x ∈₀ xs ⊎ x ∈₀ ys) → (_≋_ ∥ _≋_) (++→⊎ xs (⊎→++ p)) p
      lefty [] (inj₁ ())
      lefty [] (inj₂ p) = right ≋-refl
      lefty (x ∷ xs) (inj₁ (here _)) = left ≋-refl
      lefty (x ∷ xs) {ys} (inj₁ (there p)) with ++→⊎ xs {ys} (⊎→++ (inj₁ p)) | lefty xs {ys} (inj₁ p)
      ... | inj₁ _ | (left x~₁y) = left (thereEq x~₁y)
      ... | inj₂ _ | ()
      lefty (z ∷ zs) {ws} (inj₂ p) with ++→⊎ zs {ws} (⊎→++ {zs} (inj₂ p)) | lefty zs (inj₂ p)
      ... | inj₁ x | ()
      ... | inj₂ y | (right x~₂y) = right x~₂y

      righty : {x : A} (zs {ws} : List A) (p : x ∈₀ (zs ++ ws)) → (⊎→++ (++→⊎ zs p)) ≋ p
      righty []       {ws} p        = ≋-refl
      righty (x ∷ zs) {ws} (here _) = ≋-refl
      righty (x ∷ zs) {ws} (there p) with ++→⊎ zs p | righty zs p
      ... | inj₁ _  | res           = thereEq res
      ... | inj₂ _  | res           = thereEq res
\end{code}
%}}}

%{{{ \subsection{Bottom as a setoid} ⊥⊥ ; ⊥≅Some[] : ⊥⊥ ≅ Some P []
\subsection{Bottom as a setoid}
\begin{spec}
⊥⊥ : ∀ {ℓS ℓs} → Setoid ℓS ℓs
⊥⊥ = record
  { Carrier = ⊥
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  }
\end{spec}

\begin{spec}
module _ {ℓS ℓs ℓP ℓp : Level} {S : Setoid ℓS ℓs} {P : S ⟶ ProofSetoid ℓP ℓp} where

  ⊥≅Some[] : ⊥⊥ {(ℓS ⊔ ℓs) ⊔ ℓP} {(ℓS ⊔ ℓs) ⊔ ℓp} ≅ Some {S = S} (λ e → Setoid.Carrier (P ⟨$⟩ e)) []
  ⊥≅Some[] = record
    { to          =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; from        =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; inverse-of  =   record { left-inverse-of = λ _ → tt ; right-inverse-of = λ {()} }
    }
\end{spec}
%}}}

%{{{ \subsection{|map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)|}
\subsection{|map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)|}
\begin{spec}
map≅ : {ℓS ℓs ℓP ℓp : Level} {A B : Setoid ℓS ℓs} {P : B ⟶ ProofSetoid ℓP ℓp} →
         let P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e) in
         {f : A ⟶ B} {xs : List (Setoid.Carrier A)} →
       Some {S = A} (P₀ ⊚ (_⟨$⟩_ f)) xs ≅ Some {S = B} P₀ (map (_⟨$⟩_ f) xs)
map≅ {A = A} {B} {P} {f} = record
  { to = record { _⟨$⟩_ = map⁺ ; cong = map⁺-cong }
  ; from = record { _⟨$⟩_ = map⁻ ; cong = map⁻-cong }
  ; inverse-of = record { left-inverse-of = map⁻∘map⁺ ; right-inverse-of = map⁺∘map⁻ }
  }
  where
  open Setoid
  open Membership using (transport)
  A₀ = Setoid.Carrier A
  open Locations
  _∼_ = _≋_ {S = B}
  P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e)

  map⁺ : {xs : List A₀} → Some₀ A (P₀ ⊚ _⟨$⟩_ f) xs → Some₀ B P₀ (map (_⟨$⟩_ f) xs)
  map⁺ (here a≈x p)  = here (Π.cong f a≈x) p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : {xs : List A₀} → Some₀ B P₀ (map (_⟨$⟩_ f) xs) → Some₀ A (P₀ ⊚ (_⟨$⟩_ f)) xs
  map⁻ {[]} ()
  map⁻ {x ∷ xs} (here {b} b≈x p) = here (refl A) (Equivalence.to (Π.cong P b≈x) ⟨$⟩ p)
  map⁻ {x ∷ xs} (there p) = there (map⁻ {xs = xs} p)

  map⁺∘map⁻ : {xs : List A₀ } → (p : Some₀ B P₀ (map (_⟨$⟩_ f) xs)) → map⁺ (map⁻ p) ∼ p
  map⁺∘map⁻ {[]} ()
  map⁺∘map⁻ {x ∷ xs} (here b≈x p) = hereEq (transport B P p b≈x) p (Π.cong f (refl A)) b≈x
  map⁺∘map⁻ {x ∷ xs} (there p) = thereEq (map⁺∘map⁻ p)

  map⁻∘map⁺ : {xs : List A₀} → (p : Some₀ A (P₀ ⊚ (_⟨$⟩_ f)) xs)
            → let _∼₂_ = _≋_ {P₀ = P₀ ⊚ (_⟨$⟩_ f)} in map⁻ (map⁺ p) ∼₂ p
  map⁻∘map⁺ {[]} ()
  map⁻∘map⁺ {x ∷ xs} (here a≈x p) = hereEq (transport A (P ∘ f) p a≈x) p (refl A) a≈x
  map⁻∘map⁺ {x ∷ xs} (there p) = thereEq (map⁻∘map⁺ p)

  map⁺-cong : {ys : List A₀} {i j : Some₀ A (P₀ ⊚ _⟨$⟩_ f) ys} →  _≋_ {P₀ = P₀ ⊚ _⟨$⟩_ f} i j → map⁺ i ∼ map⁺ j
  map⁺-cong (hereEq px py x≈z y≈z) = hereEq px py (Π.cong f x≈z) (Π.cong f y≈z)
  map⁺-cong (thereEq i∼j) = thereEq (map⁺-cong i∼j)

  map⁻-cong : {ys : List A₀} {i j : Some₀ B P₀ (map (_⟨$⟩_ f) ys)} → i ∼ j → _≋_ {P₀ = P₀ ⊚ _⟨$⟩_ f} (map⁻ i) (map⁻ j)
  map⁻-cong {[]} ()
  map⁻-cong {z ∷ zs} (hereEq {x = x} {y} px py x≈z y≈z) =
    hereEq (transport B P px x≈z) (transport B P py y≈z) (refl A) (refl A)
  map⁻-cong {z ∷ zs} (thereEq i∼j) = thereEq (map⁻-cong i∼j)
\end{spec}
%}}}

%{{{ \subsection{FindLose}
\subsection{FindLose}

\begin{spec}
module FindLose {ℓS ℓs ℓP ℓp : Level} {A : Setoid ℓS ℓs}  (P : A ⟶ ProofSetoid ℓP ℓp) where
  open Membership A
  open Setoid A
  open Π
  open _≅_
  open Locations
  private
    P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e)
    Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y

  find : {ys : List Carrier} → Some₀ A P₀ ys → Support ys
  find {y ∷ ys} (here {a} a≈y p) = a , here a≈y (sym a≈y) , transport P p a≈y
  find {y ∷ ys} (there p) =  let (a , a∈ys , Pa) = find p
                             in a , there a∈ys , Pa

  lose : {ys : List Carrier} → Support ys → Some₀ A P₀ ys
  lose (y , here b≈y py , Py)  = here b≈y (Equivalence.to (Π.cong P py) Π.⟨$⟩ Py)
  lose (y , there {b} y∈ys , Py)   = there (lose (y , y∈ys , Py))
\end{spec}
%}}}

%{{{ \subsection{Σ-Setoid}
\subsection{Σ-Setoid}

\edcomm{WK}{Abstruse name!}
\edcomm{JC}{Feel free to rename.  I agree that it is not a good name.  I was more
concerned with the semantics, and then could come back to clean up once it worked.}

This is an ``unpacked'' version of |Some|, where each piece (see |Support| below) is
separated out.  For some equivalences, it seems to work with this representation.

\begin{spec}
module _ {ℓS ℓs ℓP ℓp : Level} (A : Setoid ℓS ℓs) (P : A ⟶ ProofSetoid ℓP ℓp) where
  open Membership A
  open Setoid A
  private
    P₀ : (e : Carrier) → Set ℓP
    P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e)
    Support : (ys : List Carrier) → Set (ℓS ⊔ (ℓs ⊔ ℓP))
    Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y
    squish : {x y : Setoid.Carrier A} → P₀ x → P₀ y → Set ℓp
    squish _ _ = ⊤

  open Locations
  open BagEq

  -- FIXME : this definition is still not right. ≋₀ or ≋ + ∈₀-subst₁ ?
  _∻_ : {ys : List Carrier} → Support ys → Support ys → Set ((ℓs ⊔ ℓS) ⊔ ℓp)
  (a , a∈xs , Pa) ∻ (b , b∈xs , Pb) =
    Σ (a ≈ b) (λ a≈b → a∈xs ≋₀ b∈xs × squish Pa Pb)

  Σ-Setoid : (ys : List Carrier) → Setoid ((ℓS ⊔ ℓs) ⊔ ℓP) ((ℓS ⊔ ℓs) ⊔ ℓp)
  Σ-Setoid [] = ⊥⊥ {ℓP ⊔ (ℓS ⊔ ℓs)}
  Σ-Setoid (y ∷ ys) = record
    { Carrier = Support (y ∷ ys)
    ; _≈_ = _∻_
    ; isEquivalence = record
      { refl = λ {s} → Refl {s}
      ; sym = λ {s} {t} eq → Sym {s} {t} eq
      ; trans = λ {s} {t} {u} a b → Trans {s} {t} {u} a b
      }
    }
    where
      Refl : Reflexive _∻_
      Refl {a₁ , here sm px , Pa} = refl , hereEq sm px sm px , tt
      Refl {a₁ , there a∈xs , Pa} = refl , thereEq ≋₀-refl , tt

      Sym  : Symmetric _∻_
      Sym (a≈b , a∈xs≋b∈xs , Pa≈Pb) = sym a≈b , ≋₀-sym a∈xs≋b∈xs , tt

      Trans : Transitive _∻_
      Trans (a≈b , a∈xs≋b∈xs , Pa≈Pb) (b≈c , b∈xs≋c∈xs , Pb≈Pc) = trans a≈b b≈c , ≋₀-trans a∈xs≋b∈xs b∈xs≋c∈xs , tt

  module ∻ {ys} where open Setoid (Σ-Setoid ys) public

  open FindLose P

  find-cong : {xs : List Carrier} {p q : Some₀ A P₀ xs} → p ≋ q → find p ∻ find q
  find-cong {p = .(here x≈z px)} {.(here y≈z qy)} (hereEq px qy x≈z y≈z) =
    refl , hereEq x≈z (sym x≈z) y≈z (sym y≈z) , tt
  find-cong {p = .(there _)} {.(there _)} (thereEq p≋q) =
    proj₁ (find-cong p≋q) , thereEq (proj₁ (proj₂ (find-cong p≋q))) , proj₂ (proj₂ (find-cong p≋q))

  forget-cong : {xs : List Carrier} {i j : Support xs } → i ∻ j → lose i ≋ lose j
  forget-cong {i = a₁ , here sm px , Pa} {b , here sm₁ px₁ , Pb} (i≈j , a∈xs≋b∈xs) =
    hereEq (transport P Pa px) (transport P Pb px₁) sm sm₁
  forget-cong {i = a₁ , here sm px , Pa} {b , there b∈xs , Pb} (i≈j , () , _)
  forget-cong {i = a₁ , there a∈xs , Pa} {b , here sm px , Pb} (i≈j , () , _)
  forget-cong {i = a₁ , there a∈xs , Pa} {b , there b∈xs , Pb} (i≈j , thereEq pf , Pa≈Pb) =
    thereEq (forget-cong (i≈j , pf , Pa≈Pb))

  left-inv : {zs : List Carrier} (x∈zs : Some₀ A P₀ zs) → lose (find x∈zs) ≋ x∈zs
  left-inv (here {a} {x} a≈x px) = hereEq (transport P (transport P px a≈x) (sym a≈x)) px a≈x a≈x
  left-inv (there x∈ys) = thereEq (left-inv x∈ys)

  right-inv : {ys : List Carrier} (pf : Σ y ∶ Carrier • y ∈₀ ys × P₀ y) → find (lose pf) ∻ pf
  right-inv (y , here a≈x px , Py) = trans (sym a≈x) (sym px) , hereEq a≈x (sym a≈x) a≈x px , tt
  right-inv (y , there y∈ys , Py) =
    let (α₁ , α₂ , α₃) = right-inv (y , y∈ys , Py) in
    (α₁ , thereEq α₂ , α₃)

  Σ-Some : (xs : List Carrier) → Some {S = A} P₀ xs ≅ Σ-Setoid xs
  Σ-Some [] =  ≅-sym (⊥≅Some[] {S = A} {P})
  Σ-Some (x ∷ xs) =  record
    { to = record { _⟨$⟩_ = find ; cong = find-cong }
    ; from = record { _⟨$⟩_ = lose ; cong = forget-cong }
    ; inverse-of = record
      { left-inverse-of = left-inv
      ; right-inverse-of = right-inv
      }
    }

  Σ-cong : {xs ys : List Carrier} → BagEq xs ys → Σ-Setoid xs ≅ Σ-Setoid ys
  Σ-cong {[]} {[]} iso = ≅-refl
  Σ-cong {[]} {z ∷ zs} iso = ⊥-elim (_≅_.from (⊥≅Some[] {S = A} {≈to z}) ⟨$⟩ (_≅_.from (permut iso) ⟨$⟩ here refl refl))
  Σ-cong {x ∷ xs} {[]} iso = ⊥-elim (_≅_.from (⊥≅Some[] {S = A} {≈to x}) ⟨$⟩ (_≅_.to (permut iso) ⟨$⟩ here refl refl))
  Σ-cong {x ∷ xs} {y ∷ ys} xs≅ys = record
    { to   = record { _⟨$⟩_ = xs→ys xs≅ys         ; cong = λ {i j} → xs→ys-cong xs≅ys {i} {j} }
    ; from = record { _⟨$⟩_ = xs→ys (BE-sym xs≅ys) ; cong = λ {i j} → xs→ys-cong (BE-sym xs≅ys) {i} {j} }
    ; inverse-of = record
      { left-inverse-of = λ { (z , z∈xs , Pz) → refl , ≋→≋₀ (left-inverse-of (permut xs≅ys) z∈xs) , tt }
      ; right-inverse-of = λ { (z , z∈ys , Pz) → refl , ≋→≋₀ (right-inverse-of (permut xs≅ys) z∈ys) , tt }
      }
    }
    where
      open _≅_
      xs→ys : {zs ws : List Carrier} → BagEq zs ws → Support zs → Support ws
      xs→ys eq (a , a∈xs , Pa) = (a , ∈₀-subst₂ eq a∈xs , Pa)

      --  ∈₀-subst₁-equiv  : x ≈ y → (x ∈ xs) ≅ (y ∈ xs)
      xs→ys-cong : {zs ws : List Carrier} (eq : BagEq zs ws) {i j : Support zs} →
        i ∻ j → xs→ys eq i ∻ xs→ys eq j
      xs→ys-cong eq {_ , a∈zs , _} {_ , b∈zs , _} (a≈b , pf , Pa≈Pb) =
        a≈b , repr-indep-to eq a≈b pf , tt
\end{spec}
%}}}

%{{{ \subsection{Some-cong} (∀ {x} → x ∈ xs₁ ≅ x ∈ xs₂) → Some P xs₁ ≅ Some P xs₂
\subsection{Some-cong}
This isn't quite the full-powered cong, but is all we need.

\edcomm{WK}{It has position preservation neither in the assumption (|list-rel|),
nor in the conclusion. Why did you bother with position preservation for |_≋_|?}
\edcomm{JC}{Because |_≋_| is about showing that two positions \emph{in the same
list} are equivalent.  And |list-rel| is a permutation between two lists.
I agree that |_≋_| could be ``loosened'' to be up to
permutation of elements which are |_≈_| to a given one.

But if our notion of permutation is |BagEq|, which depends on |_∈_|, which
depends on |Some|, which depends on |_≋_|. If that now depends on |BagEq|,
we've got a mutual recursion that seems unecessary.}

\begin{spec}
module _ {ℓS ℓs ℓP : Level} {A : Setoid ℓS ℓs} {P : A ⟶ ProofSetoid ℓP ℓs} where

  open Membership A
  open Setoid A
  private
    P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e)

  Some-cong : {xs₁ xs₂ : List Carrier} →
            BagEq xs₁ xs₂ →
            Some P₀ xs₁ ≅ Some P₀ xs₂
  Some-cong {xs₁} {xs₂} xs₁≅xs₂ =
    Some P₀ xs₁        ≅⟨ Σ-Some A P xs₁ ⟩
    Σ-Setoid A P xs₁   ≅⟨ Σ-cong A P xs₁≅xs₂ ⟩
    Σ-Setoid A P xs₂   ≅⟨ ≅-sym (Σ-Some A P xs₂) ⟩
    Some P₀ xs₂ ∎
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
