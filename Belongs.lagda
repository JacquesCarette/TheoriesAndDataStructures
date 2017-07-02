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
import Relation.Binary.Indexed as I

open import Function.Equality    using (Π ; _⟶_ ; id ; _∘_ ; _⟨$⟩_ ; cong )
open import Function             using (_$_; flip) renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; map; reverse)
open import Data.Nat      using (ℕ; zero; suc)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp
open import ISEquiv

open import TypeEquiv using (swap₊)
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
  open Setoid S

  infix 4 _∈₀_
  data _∈₀_  : Carrier → List Carrier → Set (ℓS ⊔ ℓs) where
    here  : {x a : Carrier} {xs : List Carrier} (sm : a ≈ x)       →   a ∈₀ (x ∷ xs)
    there : {x a : Carrier} {xs : List Carrier} (pxs : a ∈₀ xs)   →   a ∈₀ (x ∷ xs)

  open _∈₀_ public
\end{code}

One instinct is go go with natural numbers directly; while this
has the ``right'' computational content, that is harder for deduction.
Nevertheless, the 'location' function is straightforward:
\begin{code}
  toℕ : {x : Carrier} {xs : List Carrier} → x ∈₀ xs → ℕ
  toℕ (here _) = 0
  toℕ (there pf) = suc (toℕ pf)
\end{code}

We need to know when two locations are the same.

\begin{code}
module LocEquiv {ℓS ℓs} (S : Setoid ℓS ℓs) where
  open Setoid             S
  open Locations          S
  open SetoidCombinators  S

  infix 3 _≋_
  data _≋_ : {y y' : Carrier} {ys : List Carrier} (loc : y ∈₀ ys) (loc' : y' ∈₀ ys) → Set (ℓS ⊔ ℓs) where
    hereEq : {xs : List Carrier} {x y z : Carrier} (x≈z : x ≈ z) (y≈z : y ≈ z)
           → here {x = z} {x} {xs} x≈z  ≋  here {x = z} {y} {xs} y≈z
    thereEq : {xs : List Carrier} {x x' z : Carrier} {loc : x ∈₀ xs} {loc' : x' ∈₀ xs}
            → loc ≋ loc' → there {x = z} loc  ≋  there {x = z} loc'
  open _≋_ public
\end{code}

These are seen to be another form of natural numbers as well.

It is on purpose that |_≋_| preserves positions.
Suppose that we take the setoid of the Latin alphabet,
with |_≈_| identifying upper and lower case.
There should be 3 elements of |_≋_| for |a ∷ A ∷ a ∷ []|, not 6.
When we get to defining |BagEq|,
there will be 6 different ways in which that list, as a Bag, is equivalent to itself.

Furthermore, it is important to notice that we have an injectivity property:
|x ∈₀ xs ≋ y ∈₀ xs| implies |x ≈ y|.
\begin{code}
  ≋→≈ : {x y : Carrier} {xs : List Carrier} (x∈xs : x ∈₀ xs) (y∈xs : y ∈₀ xs)
       → x∈xs ≋ y∈xs → x ≈ y
  ≋→≈ (here x≈z   ) .(here y≈z) (hereEq .x≈z y≈z)                   =  x≈z ⟨≈≈˘⟩ y≈z
  ≋→≈ (there x∈xs) .(there _ ) (thereEq {loc' = loc'} x∈xs≋loc')  =  ≋→≈ x∈xs loc' x∈xs≋loc'
\end{code}
%}}}

%{{{ \subsection{Membership module}: _∈_
\subsection{Membership module}

We now have all the ingredients to show that locations (|_∈₀_|) form a |Setoid|. But
we will go one step further and show that it forms an |IndexedSetoid|.
\begin{code}
module Membership {ℓS ℓs} (S : Setoid ℓS ℓs) where
  infix 3 _♯_

  open Setoid S
  open Locations S
  open LocEquiv S

  ≋-refl : {x : Carrier} {xs : List Carrier} {p : x ∈₀ xs} → p ≋ p
  ≋-refl {p = here a≈x}   =   hereEq a≈x a≈x
  ≋-refl {p = there p}    =   thereEq ≋-refl

  ≋-sym : {l : List Carrier} {x y : Carrier} {x∈l : x ∈₀ l} {y∈l : y ∈₀ l} → x∈l ≋ y∈l → y∈l ≋ x∈l
  ≋-sym (hereEq x≈z y≈z) = hereEq _ _
  ≋-sym (thereEq pf) = thereEq (≋-sym pf)

  ≋-trans : {l : List Carrier} {x y z : Carrier} {x∈l : x ∈₀ l} {y∈l : y ∈₀ l} {z∈l : z ∈₀ l}
    → x∈l ≋ y∈l → y∈l ≋ z∈l → x∈l ≋ z∈l
  ≋-trans (hereEq x≈z y≈z) (hereEq .y≈z y≈z₁) = hereEq x≈z y≈z₁
  ≋-trans (thereEq pp) (thereEq qq) = thereEq (≋-trans pp qq)

  ≡→≋ : {x : Carrier} {xs : List Carrier} {p q : x ∈₀ xs} → p ≡ q → p ≋ q
  ≡→≋ ≡.refl = ≋-refl

  elem-of : List Carrier → I.Setoid Carrier (ℓS ⊔ ℓs) (ℓS ⊔ ℓs)
  elem-of l = record
    { Carrier = λ x → x ∈₀ l
    ; _≈_ = _≋_
    ; isEquivalence = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans } }

  _♯_ : {f₁ f₂ t₁ t₂ : Level}
         (From : I.Setoid (Setoid.Carrier S) f₁ f₂)
         (To : I.Setoid (Setoid.Carrier S) t₁ t₂) →
         Set (ℓS ⊔ ℓs ⊔ f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂)
  From ♯ To = IndexedSetoidEquivalence S From To
\end{code}
%}}}

%{{{ \subsection{Substitution}
\subsection{Substitution}

Given |x ≈ y|, we have a substitution-like operator that maps from
|x ∈₀ xs| to |y ∈₀ xs|.  Here, choose the HoTT-inspired name,
|ap-∈₀|.  We will see later that these are the essential ingredients
for showing that |♯| (at |∈₀|) is reflexive.
\begin{code}
module Substitution {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S
  open Locations S
  open LocEquiv S
  open SetoidCombinators S

  ap-∈₀ : {x y : Carrier} {xs : List Carrier} → x ≈ y → x ∈₀ xs → y ∈₀ xs
  ap-∈₀ x≈y (here a≈x) = here (x≈y ⟨≈˘≈⟩ a≈x)
  ap-∈₀ x≈y (there x∈xs) = there (ap-∈₀ x≈y x∈xs)

  ap-∈₀-cong : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y)
                  {i j : x ∈₀ xs} → i ≋ j → ap-∈₀ x≈y i ≋ ap-∈₀ x≈y j
  ap-∈₀-cong x≈y (hereEq x≈z y≈z) = hereEq (x≈y ⟨≈˘≈⟩ x≈z) (x≈y ⟨≈˘≈⟩ y≈z)
  ap-∈₀-cong x≈y (thereEq i≋j) = thereEq (ap-∈₀-cong x≈y i≋j)

  ap-∈₀-linv : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y)
    (x∈xs : x ∈₀ xs) → ap-∈₀ (sym x≈y) (ap-∈₀ x≈y x∈xs) ≋ x∈xs
  ap-∈₀-linv x≈y (here sm) = hereEq ((sym x≈y) ⟨≈˘≈⟩ (x≈y ⟨≈˘≈⟩ sm)) sm
  ap-∈₀-linv x≈y (there x∈xs) = thereEq (ap-∈₀-linv x≈y x∈xs)

  ap-∈₀-rinv : {x y : Carrier} {ys : List Carrier} (x≈y : x ≈ y)
    (y∈ys : y ∈₀ ys) → ap-∈₀ x≈y (ap-∈₀ (sym x≈y) y∈ys) ≋ y∈ys
  ap-∈₀-rinv x≈y (here sm) = hereEq (x≈y ⟨≈˘≈⟩ (sym x≈y ⟨≈˘≈⟩ sm)) sm
  ap-∈₀-rinv x≈y (there y∈ys) = thereEq (ap-∈₀-rinv x≈y y∈ys)
\end{code}
%}}}

%{{{ \subsection{|BagEq|}
\subsection{|BagEq|}

Fundamental definition: two Bags, represented as |List Carrier| are equivalent
if and only if there exists a permutation between their |Setoid| of positions,
and this is independent of the representative.  The best way to succinctly
express this is via |_♯_|.

It is very important to note that |_♯_| isn't reflective 'for free', i.e.
the proof does not involve just |id|.
\begin{code}
module BagEq {ℓS ℓs} (S : Setoid ℓS ℓs) where
  open Setoid S
  open Locations S
  open LocEquiv S
  open Membership S
  open Substitution S

  infix 3 _⇔_

  _⇔_ : (xs ys : List Carrier) → Set (ℓS ⊔ ℓs)
  xs ⇔ ys = elem-of xs ♯ elem-of ys

  ⇔-refl : {xs : List Carrier} → xs ⇔ xs
  ⇔-refl x≈y = record
    { to = record   { _⟨$⟩_ = ap-∈₀ x≈y       ; cong = ap-∈₀-cong x≈y }
    ; from = record { _⟨$⟩_ = ap-∈₀ (sym x≈y) ; cong = ap-∈₀-cong (sym x≈y) }
    ; inverse-of = record { left-inverse-of = ap-∈₀-linv x≈y ; right-inverse-of = ap-∈₀-rinv x≈y } }

  ⇔-sym : {xs ys : List Carrier} → xs ⇔ ys → ys ⇔ xs
  ⇔-sym {xs} {ys} xs⇔ys {x} {y} x≈y = record
    { to = record
      { _⟨$⟩_ = ap-⇐ xs⇔ys (sym x≈y)
      ; cong = cong (xs⇔ys $← (sym x≈y)) }
    ; from = record
      { _⟨$⟩_ = ap-⇒ xs⇔ys (sym x≈y)
      ; cong = cong (xs⇔ys $→ sym x≈y) }
    ; inverse-of = record
      { left-inverse-of = _≅_.right-inverse-of (xs⇔ys (sym x≈y))
      ; right-inverse-of = _≅_.left-inverse-of (xs⇔ys (sym x≈y)) }
    }
    where
      open ISE-Combinators S (elem-of xs) (elem-of ys)

  ⇔-trans : {xs ys zs : List Carrier} → xs ⇔ ys → ys ⇔ zs → xs ⇔ zs
  ⇔-trans {xs} {ys} {zs} xs⇔ys ys⇔zs {a} {b} a≈b = record
    { to = record
      { _⟨$⟩_ = (ap-⇒₂ ys⇔zs a≈b) ⊚ (ap-⇒₁ xs⇔ys refl)
      ; cong = cong (ys⇔zs $→₂ a≈b) ⊚ (cong (xs⇔ys $→₁ refl)) }
    ; from = record
      { _⟨$⟩_ = ap-⇐₁ xs⇔ys refl ⊚ ap-⇐₂ ys⇔zs a≈b
      ; cong = cong (xs⇔ys $←₁ refl) ⊚ cong (ys⇔zs $←₂ a≈b) }
    ; inverse-of = record
      { left-inverse-of = λ a∈xs → ≋-trans
        (cong (xs⇔ys $←₁ refl) (_≅_.left-inverse-of (ys⇔zs a≈b) (ap-⇒₁ xs⇔ys refl a∈xs)))
        (_≅_.left-inverse-of (xs⇔ys refl) a∈xs)
      ; right-inverse-of = λ b∈zs → ≋-trans
        (cong (ys⇔zs $→₂ a≈b) (_≅_.right-inverse-of (xs⇔ys refl) (ap-⇐₂ ys⇔zs a≈b b∈zs)))
        (_≅_.right-inverse-of (ys⇔zs a≈b) b∈zs) }
    }
    where
      open ISE-Combinators S (elem-of xs) (elem-of ys)
        renaming (ap-⇐ to ap-⇐₁; ap-⇒ to ap-⇒₁; _$→_ to _$→₁_; _$←_ to _$←₁_)
      open ISE-Combinators S (elem-of ys) (elem-of zs)
        renaming (ap-⇐ to ap-⇐₂; ap-⇒ to ap-⇒₂; _$→_ to _$→₂_; _$←_ to _$←₂_)

\end{code}
%}}}

%{{{ \subsection{|++≅ : ⋯ → (x ∈ xs ⊎⊎ x ∈ ys) ≅ x ∈ (xs ++ ys)|}
\subsection{|++≅ : ⋯ → (x ∈ xs ⊎⊎ x ∈ ys) ≅ x ∈ (xs ++ ys)|}
\begin{code}
module ConcatTo⊎⊎ {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S renaming (Carrier to A)
  open SetoidCombinators S
  open LocEquiv S
  open Locations S
  open Membership S
  open Substitution S

  ++≅ : {xs ys : List A } → (elem-of xs ⊎⊎ elem-of ys) ♯ (elem-of (xs ++ ys))
  ++≅ {xs} {ys} {x} {y} x≈y = record
    { to = record { _⟨$⟩_ = ⊎→++ x≈y            ; cong = ⊎→++-cong x≈y  }
    ; from = record { _⟨$⟩_ = ++→⊎ xs (sym x≈y) ; cong = ++→⊎-cong (sym x≈y) xs }
    ; inverse-of = record
      { left-inverse-of = lefty x≈y {xs}
      ; right-inverse-of = righty x≈y xs
      }
    }
    where
      -- ``ealier''
      ⊎→ˡ : {ws zs : List A} {x y : A} → x ≈ y → x ∈₀ ws → y ∈₀ (ws ++ zs)
      ⊎→ˡ x≈y (here a≈x) = here (x≈y ⟨≈˘≈⟩ a≈x)
      ⊎→ˡ x≈y (there p) = there (⊎→ˡ x≈y p)

      yo : {ws zs : List A} {z w : A} {a b : z ∈₀ ws} → (z≈w : z ≈ w) → a ≋ b → ⊎→ˡ {ws} {zs} z≈w a ≋ ⊎→ˡ z≈w b
      yo z≈w (hereEq _ _) = hereEq _ _
      yo z≈w (thereEq pf) = thereEq (yo z≈w pf)

      -- ``later''
      ⊎→ʳ : ∀ {x y} xs {ys} → x ≈ y → x ∈₀ ys → y ∈₀ (xs ++ ys)
      ⊎→ʳ []       x≈y p = ap-∈₀ x≈y p
      ⊎→ʳ (x ∷ xs) x≈y p = there (⊎→ʳ xs x≈y p)

      oy : {z w : A} (xs : List A) {x y : z ∈₀ ys} → (z≈w : z ≈ w) → x ≋ y → ⊎→ʳ xs z≈w x ≋ ⊎→ʳ xs z≈w y
      oy []       z≈w pf = ap-∈₀-cong z≈w pf
      oy (x ∷ xs) z≈w pf = thereEq (oy xs z≈w pf)

      ⊎→++ : ∀ {zs ws z₁ z₂} → z₁ ≈ z₂ → (z₁ ∈₀ zs ⊎ z₁ ∈₀ ws) → z₂ ∈₀ (zs ++ ws)
      ⊎→++      z₁≈z₂ (inj₁ x) = ⊎→ˡ z₁≈z₂ x
      ⊎→++ {zs} z₁≈z₂ (inj₂ y) = ⊎→ʳ zs z₁≈z₂ y

      ++→⊎ : ∀ xs {ys} {z} {w} → z ≈ w → z ∈₀ (xs ++ ys) → w ∈₀ xs ⊎ w ∈₀ ys
      ++→⊎ []      z≈w         p  = inj₂ (ap-∈₀ z≈w p)
      ++→⊎ (x ∷ l) z≈w (here  p) = inj₁ (here (z≈w ⟨≈˘≈⟩ p))
      ++→⊎ (x ∷ l) z≈w (there p) = (there ⊎₁ id₀) (++→⊎ l z≈w p)

      ⊎→++-cong : {x y : A} {a b : x ∈₀ xs ⊎ x ∈₀ ys}
        → (x≈y : x ≈ y) → (_≋_ ∥ _≋_) a b → ⊎→++ x≈y a ≋ ⊎→++ x≈y b
      ⊎→++-cong x≈y (left  x₁∼x₂)  =  yo x≈y x₁∼x₂
      ⊎→++-cong x≈y (right y₁∼y₂)  =  oy xs x≈y y₁∼y₂

      ∽∥∽-cong   :  {x : A} {xs ys us vs : List A}
                    (F : x ∈₀ xs → x ∈₀ us)
                    (F-cong : {p q : x ∈₀ xs} → p ≋ q → F p ≋ F q)
                    (G : x ∈₀ ys → x ∈₀ vs)
                    (G-cong : {p q : x ∈₀ ys} → p ≋ q → G p ≋ G q)
                    → {pf pf' : x ∈₀ xs ⊎ x ∈₀ ys}
                    → (_≋_ ∥ _≋_) pf pf' → (_≋_ ∥ _≋_) ( (F ⊎₁ G) pf) ((F ⊎₁ G) pf')
      ∽∥∽-cong F F-cong G G-cong (left x~₁y) = left (F-cong x~₁y)
      ∽∥∽-cong F F-cong G G-cong (right x~₂y) = right (G-cong x~₂y)

      ++→⊎-cong : {x y : A} (x≈y : x ≈ y) (xs : List A) {i j : x ∈₀ (xs ++ ys)} → i ≋ j → (_≋_ ∥ _≋_) (++→⊎ xs x≈y i) (++→⊎ xs x≈y j)
      ++→⊎-cong x≈y []        pf          = right (ap-∈₀-cong x≈y pf)
      ++→⊎-cong x≈y (_ ∷ xs) (hereEq _ _) = left (hereEq _ _)
      ++→⊎-cong x≈y (_ ∷ xs) (thereEq pf) = ∽∥∽-cong there thereEq id₀ id₀ (++→⊎-cong x≈y xs pf)

      lefty : {x y : A} (x≈y : x ≈ y) {xs ys : List A} (p : x ∈₀ xs ⊎ x ∈₀ ys) → (_≋_ ∥ _≋_) (++→⊎ xs (sym x≈y) (⊎→++ x≈y p)) p
      lefty x≈y {[]} (inj₁ ())
      lefty x≈y {[]} (inj₂ p) = right (ap-∈₀-linv x≈y p)
      lefty x≈y {_ ∷ _} (inj₁ (here _)) = left (hereEq _ _)
      lefty x≈y {_ ∷ xs} {ys} (inj₁ (there p)) with ++→⊎ xs {ys} (sym x≈y) (⊎→++ x≈y (inj₁ p)) | lefty x≈y {xs} {ys} (inj₁ p)
      ... | inj₁ _ | (left x~₁y) = left (thereEq x~₁y)
      ... | inj₂ _ | ()
      lefty x≈y {z ∷ zs} (inj₂ p) with ++→⊎ zs (sym x≈y) (⊎→++ {zs} x≈y (inj₂ p)) | lefty x≈y {zs} (inj₂ p)
      ... | inj₁ x | ()
      ... | inj₂ y | (right x~₂y) = right x~₂y

      righty : {x y : A} (x≈y : x ≈ y) (zs {ws} : List A) (p : y ∈₀ (zs ++ ws)) → (⊎→++ x≈y (++→⊎ zs (sym x≈y) p)) ≋ p
      righty x≈y []       p        = ap-∈₀-rinv x≈y p
      righty x≈y (_ ∷ zs) (here _) = hereEq _ _
      righty x≈y (_ ∷ zs) (there p) with ++→⊎ zs (sym x≈y) p | righty x≈y zs p
      ... | inj₁ _  | res           = thereEq res
      ... | inj₂ _  | res           = thereEq res
\end{code}
%}}}

\subsection{Following sections are inactive code}

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
