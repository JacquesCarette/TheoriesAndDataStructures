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

open import Function.Equality    using (Π ; _⟶_ ; id ; _∘_ ; _⟨$⟩_ ; cong )
open import Function             using (_$_; flip) renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; map; reverse)
open import Data.Nat      using (ℕ; zero; suc)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp
open import Structures.CommMonoid

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
    here  : {x a : Carrier} {xs : List Carrier} (sm : a ≈ x)      →   a ∈₀ (x ∷ xs)
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
  ≋→≈ (here x≈z   ) .(here y≈z) (hereEq .x≈z y≈z)                 =  x≈z ⟨≈≈˘⟩ y≈z
  ≋→≈ (there x∈xs) .(there _ ) (thereEq {loc' = loc'} x∈xs≋loc')  =  ≋→≈ x∈xs loc' x∈xs≋loc'
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

  ap-∈₀-eq : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y) (x∈xs : x ∈₀ xs) → x∈xs ≋ ap-∈₀ x≈y x∈xs
  ap-∈₀-eq x≈y (here sm)      =  hereEq sm (x≈y ⟨≈˘≈⟩ sm)
  ap-∈₀-eq x≈y (there x∈xs)  =  thereEq (ap-∈₀-eq x≈y x∈xs)

  ap-∈₀-refl : {x : Carrier} {xs : List Carrier} (x∈xs : x ∈₀ xs) → ap-∈₀ refl x∈xs ≋ x∈xs
  ap-∈₀-refl (Locations.here sm) = hereEq (refl ⟨≈˘≈⟩ sm) sm
  ap-∈₀-refl (Locations.there xx) = thereEq (ap-∈₀-refl xx)

  ap-∈₀-cong : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y)
                {i j : x ∈₀ xs} → i ≋ j → ap-∈₀ x≈y i  ≋  ap-∈₀ x≈y j
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

  -- functoriality: |trans| becomes composition.
  ap-∈₀-trans : {x y z : Carrier} {xs : List Carrier} {x∈xs : x ∈₀ xs}
    (x≈y : x ≈ y) (y≈z : y ≈ z) → ap-∈₀ (x≈y ⟨≈≈⟩ y≈z) x∈xs ≋ ap-∈₀ y≈z (ap-∈₀ x≈y x∈xs)
  ap-∈₀-trans {x∈xs = here sm} x≈y y≈z      =  hereEq (trans x≈y y≈z ⟨≈˘≈⟩ sm) (y≈z ⟨≈˘≈⟩ (x≈y ⟨≈˘≈⟩ sm))
  ap-∈₀-trans {x∈xs = there x∈xs} x≈y y≈z  =  thereEq (ap-∈₀-trans x≈y y≈z)
\end{code}
%}}}

%{{{ \subsection{Membership module}: _∈_
\subsection{Membership module}

We now have all the ingredients to show that locations (|_∈₀_|) form a |Setoid|.
\begin{code}
module Membership {ℓS ℓs} (S : Setoid ℓS ℓs) where
  open Setoid        S  
  open Locations     S  
  open LocEquiv      S  
  open Substitution  S  

  ≋-refl : {x : Carrier} {xs : List Carrier} {p : x ∈₀ xs} → p ≋ p
  ≋-refl {p = here a≈x}   =   hereEq a≈x a≈x
  ≋-refl {p = there p}    =   thereEq ≋-refl

  ≋-sym : {l : List Carrier} {x y : Carrier} {x∈l : x ∈₀ l} {y∈l : y ∈₀ l} → x∈l ≋ y∈l → y∈l ≋ x∈l
  ≋-sym (hereEq x≈z y≈z) = hereEq y≈z x≈z 
  ≋-sym (thereEq pf)     = thereEq (≋-sym pf)

  ≋-trans : {l : List Carrier} {x y z : Carrier} {x∈l : x ∈₀ l} {y∈l : y ∈₀ l} {z∈l : z ∈₀ l}
          → x∈l ≋ y∈l → y∈l ≋ z∈l → x∈l ≋ z∈l
  ≋-trans (hereEq x≈z y≈z) (hereEq .y≈z y≈z₁)  =  hereEq x≈z y≈z₁
  ≋-trans (thereEq pp) (thereEq qq)            =  thereEq (≋-trans pp qq)

  ≡→≋ : {x : Carrier} {xs : List Carrier} {p q : x ∈₀ xs} → p ≡ q → p ≋ q
  ≡→≋ ≡.refl = ≋-refl
\end{code}

The type |elements l| is just |∃ Carrier (λ witness → witness ∈₀ l)|, but it is more
convenient to have a dedicated name (and notation).  For now, no dedicated name will
be given to the equality.

\begin{code}
  record elements (l : List Carrier) : Set (ℓS ⊔ ℓs) where
    constructor El
    field
      {witness}  :  Carrier
      belongs    :  witness ∈₀ l

  open elements public

  lift-el : {l₁ l₂ : List Carrier} (f : {w : Carrier} → w ∈₀ l₁ → w ∈₀ l₂)
          → elements l₁ → elements l₂
  lift-el f (El l) = El (f l)

  _⟷_ : {l : List Carrier} → Rel (elements l) (ℓs ⊔ ℓS)
  (El b₁) ⟷ (El b₂) = b₁ ≋ b₂

  elem-of : List Carrier → Setoid (ℓs ⊔ ℓS) (ℓs ⊔ ℓS)
  elem-of l = record
    { Carrier         =   elements l
    ; _≈_             =   _⟷_
    ; isEquivalence   =   record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
    }
\end{code}
%}}}

%{{{ \subsection{|BagEq|}
\subsection{|BagEq|}

Fundamental definition: two Bags, represented as |List Carrier| are equivalent
if and only if there exists a permutation between their |Setoid| of positions,
and this is independent of the representative.  The best way to succinctly
express this is via |_⇔_|.

It is very important to note that |_⇔_| isn't reflective 'for free', i.e.
the proof does not involve just |id|.
\begin{code}
module BagEq {ℓS ℓs} (S : Setoid ℓS ℓs) where
  open Setoid         S  
  open Locations      S  
  open LocEquiv       S  
  open Membership     S  
  open Substitution   S  

  infix 3 _⇔_

  _⇔_ : (xs ys : List Carrier) → Set (ℓS ⊔ ℓs)
  xs ⇔ ys = elem-of xs ≅ elem-of ys

  open import Data.Product
  
  -- I could not prove |⇔| implies set-containment; i.e., |{e : Carrier} → e ∈₀ xs → e ∈₀ ys)|
  -- so trying this variant.
  -- 
  ⇔-forwards : {xs ys : List Carrier} → xs ⇔ ys
              → {e : Carrier} → e ∈₀ xs → Σ Carrier (λ e′ → e ≈ e′ × e′ ∈₀ ys)
  ⇔-forwards {xs} {ys} record { to = to ; from = from ; inverse-of = inverse-of } {e} e∈xs = {!!}
    where in-ys : elements ys
          in-ys = to ⟨$⟩ El {witness = e} e∈xs

          e′  : Carrier
          e′  = elements.witness in-ys

          e′∈ys : e′ ∈₀ ys
          e′∈ys = elements.belongs in-ys

  wrap-⇔-injective : {x y : Carrier} → (x ∷ []) ⇔ (y ∷ []) → x ≈ y
  wrap-⇔-injective {x} {y} record { to = to ; from = from ; inverse-of = inverse-of } = one-point arg
    where
      pf : elements (y ∷ [])
      pf = to ⟨$⟩ El {witness = x} (here refl)

      arg : x ∈₀ y ∷ []
      arg = {!!}

      one-point : ∀ {e} → e ∈₀ (y ∷ []) → e ≈ y
      one-point (here e≈y) = e≈y
      one-point (there ())

  ≡→⇔ : {a b : List Carrier} → a ≡ b → a ⇔ b
  ≡→⇔ ≡.refl = ≅-refl

  -- move to other setoid
  module _ (F    : List Carrier → Carrier)
           {_⊕_  : Carrier → Carrier → Carrier}
           (ind  : ∀{x xs} → F (x ∷ xs)  ≈  x ⊕ F xs)
           (pres : ∀{x s y t} → (x ∷ s) ⇔ (y ∷ t) → x ⊕ F s ≈ y ⊕ F t)
    where
     ⇔-subst :  {s t : List Carrier}
             → s ⇔ t → F s ≈ F t
     ⇔-subst {[]} {[]} pf = refl
     ⇔-subst {[]} {x ∷ t} record { to = to ; from = from ; inverse-of = inverse-of } = sure-why-not oh
       where sure-why-not : Setoid.Carrier (elem-of []) → _
             sure-why-not (El ())
             
             oh : Setoid.Carrier (elem-of [])
             oh = from ⟨$⟩ Membership.El {witness = x} (here refl)
     ⇔-subst {x ∷ s} {[]} record { to = to ; from = from ; inverse-of = inverse-of } = again uhHm
       where again : Setoid.Carrier (elem-of []) → _
             again (El ())
             
             uhHm : Setoid.Carrier (elem-of [])
             uhHm = to ⟨$⟩ El {witness = x} (here refl)
     ⇔-subst {x ∷ s} {y ∷ t} pf = trans ind (trans (pres pf) (sym ind))
\end{code}
%}}}

%{{{ \subsection{|++♯⊎S : ⋯ → (elem-of xs ⊎S elem-of ys) ≅ elem-of (xs ++ ys)|}
\subsection{|++♯⊎S : ⋯ → (elem-of xs ⊎S elem-of ys) ≅ elem-of (xs ++ ys)|}
\begin{code}
module ConcatTo⊎S {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Setoid S renaming (Carrier to A)
  open SetoidCombinators S
  open LocEquiv S
  open Locations S
  open Membership S
  open Substitution S

  ⊎S≅++ : {xs ys : List A } → (elem-of xs ⊎S elem-of ys) ≅ (elem-of (xs ++ ys))
  ⊎S≅++ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong = ⊎→++-cong }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = ++→⊎-cong xs }
    ; inverse-of = record
      { left-inverse-of = lefty
      ; right-inverse-of = righty {xs} }
    }
    where
      ⊎ˡ : ∀ {zs ws} {a : A} → a ∈₀ zs → a ∈₀ zs ++ ws
      ⊎ˡ (here sm) = here sm
      ⊎ˡ (there pf) = there (⊎ˡ pf)

      ⊎ʳ : (zs : List A) {ws : List A} {a : A} → a ∈₀ ws → a ∈₀ zs ++ ws
      ⊎ʳ []      p = p
      ⊎ʳ (x ∷ l) p = there (⊎ʳ l p)

      ⊎→++ : ∀ {zs ws} → elements zs ⊎ elements ws → elements (zs ++ ws)
      ⊎→++      (inj₁ (El w∈zs)) = El (⊎ˡ w∈zs)
      ⊎→++ {zs} (inj₂ (El w∈ws)) = El (⊎ʳ zs w∈ws)

      ⊎ˡ-cong : {zs ws : List A} {x y : elements zs} → x ⟷ y
        → ⊎ˡ {zs} {ws} (belongs x) ≋ ⊎ˡ (belongs y)
      ⊎ˡ-cong (hereEq x≈z y≈z) = hereEq x≈z y≈z
      ⊎ˡ-cong (thereEq x≋y) = thereEq (⊎ˡ-cong x≋y)

      ⊎ʳ-cong : (zs : List A) {ws : List A} {x y : elements ws} → x ⟷ y
        → ⊎ʳ zs (belongs x) ≋ ⊎ʳ zs (belongs y)
      ⊎ʳ-cong [] pf = pf
      ⊎ʳ-cong (x ∷ l) pf =  thereEq (⊎ʳ-cong l pf)

      ⊎→++-cong : {zs ws : List A} {i j : elements zs ⊎ elements ws}
        → ((λ w₁ w₂ → belongs w₁ ≋ belongs w₂) ∥ (λ w₁ w₂ → belongs w₁ ≋ belongs w₂)) i j
        → belongs (⊎→++ i) ≋ belongs (⊎→++ j)
      ⊎→++-cong      (left  ∈x≋∈y)  =  ⊎ˡ-cong ∈x≋∈y
      ⊎→++-cong {zs} (right ∈x≋∈y)  =  ⊎ʳ-cong zs ∈x≋∈y

      ∽∥∽-cong   :  {xs ys us vs : List A}
         (F : elements xs → elements us)
         (F-cong : {p : elements xs} {q : elements xs} → p ⟷ q → F p ⟷ F q)
         (G : elements ys → elements vs)
         (G-cong : {p : elements ys} {q : elements ys} → p ⟷ q → G p ⟷ G q)
         → {pf : elements xs ⊎ elements ys} {pf' : elements xs ⊎ elements ys}
         → (_⟷_ ∥ _⟷_) pf pf' → (_⟷_ ∥ _⟷_) ( (F ⊎₁ G) pf) ((F ⊎₁ G) pf')
      ∽∥∽-cong F F-cong G G-cong (left x~₁y) = left (F-cong x~₁y)
      ∽∥∽-cong F F-cong G G-cong (right x~₂y) = right (G-cong x~₂y)

      ++→⊎ : ∀ xs {ys} → elements (xs ++ ys) → elements xs ⊎ elements ys
      ++→⊎ []              p      = inj₂ p
      ++→⊎ (x ∷ l) (El (here  p)) = inj₁ (El (here p))
      ++→⊎ (x ∷ l) (El (there p)) = (lift-el there ⊎₁ id₀) (++→⊎ l (El p))

      ++→⊎-cong : (zs : List A) {ws : List A}
        {i j : elements (zs ++ ws)} → i ⟷ j
        → (_⟷_ ∥ _⟷_) (++→⊎ zs i) (++→⊎ zs j)
      ++→⊎-cong []        i≋j         = right i≋j
      ++→⊎-cong (_ ∷ xs) (hereEq _ _) = left (hereEq _ _)
      ++→⊎-cong (_ ∷ xs) (thereEq pf) = ∽∥∽-cong (lift-el there) thereEq id₀ id₀ (++→⊎-cong xs pf)

      righty : {xs ys : List A} (x : elements (xs ++ ys)) → ⊎→++ (++→⊎ xs x) ⟷ x
      righty {[]} x = ≋-refl
      righty {x ∷ xs₁} (El (here sm)) = hereEq sm sm
      righty {_ ∷ xs₁} (El (there x)) with ++→⊎ xs₁ (El x) | righty {xs₁} (El x)
      ... | inj₁ x₁∈xs₁ | ans = thereEq ans
      ... | inj₂ x₁∈ys  | ans = thereEq ans

      lefty : {xs ys : List A} (x : elements xs ⊎ elements ys) →
        (_⟷_ ∥ _⟷_) (++→⊎ xs (⊎→++ x)) x
      lefty {[]} (inj₁ (El ()))
      lefty {[]} (inj₂ y) = right ≋-refl
      lefty {_ ∷ _} (inj₁ (El (here sm))) = left (hereEq sm sm)
      lefty {_ ∷ xs₁} {ys} (inj₁ (El (there x))) with ++→⊎ xs₁ {ys} (El (⊎ˡ x))
                                                    | lefty {ys = ys} (inj₁ (El x))
      ... | inj₁ res | left ans = left (thereEq ans)
      ... | inj₂ res | ()
      lefty {x₂ ∷ xs₂} {ys} (inj₂ (El (here sm))) with ++→⊎ xs₂ (El (⊎ʳ xs₂ {ys} (here sm)))
                                                     | lefty {xs₂} {ys} (inj₂ (El (here sm)))
      ... | inj₁ res | ()
      ... | inj₂ res | right ans = right ans
      lefty {x₂ ∷ xs₂} {ys} (inj₂ (El (there x))) with ++→⊎ xs₂ (El (⊎ʳ xs₂ {ys} (there x)))
                                                     | lefty {xs₂} {ys} (inj₂ (El (there x)))
      ... | inj₁ res | ()
      ... | inj₂ res | right ans = right ans
\end{code}
%}}}

%{{{ \subsection{Bottom as a Setoid} ⊥⊥ ; ⊥⊥ ≅ elem-of []
\subsection{Bottom as a Setoid}
\begin{code}
⊥⊥ : ∀ {ℓI ℓi} → Setoid ℓI ℓi
⊥⊥ = record
    { Carrier = ⊥
    ; _≈_ = λ _ _ → ⊤
    ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    }
\end{code}

\begin{code}
module ElemOf[] {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Membership S

  elem-of-[] : Setoid.Carrier (elem-of []) → ⊥ {ℓS}
  elem-of-[] (El ())

  ⊥⊥≅elem-of-[] : ⊥⊥ {ℓS} {ℓs} ≅ (elem-of [])
  ⊥⊥≅elem-of-[] = record
    { to = record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; from = record { _⟨$⟩_ = elem-of-[] ; cong = λ { {El ()}} }
    ; inverse-of = record { left-inverse-of = λ {()} ; right-inverse-of = λ { (El () )} } }
\end{code}
%}}}

%{{{ \subsection{|elem-of| |map| properties}
\subsection{|elem-of| |map| properties}
\begin{code}
module ElemOfMap {ℓS ℓs : Level} {S T : Setoid ℓS ℓs} where
  open Setoid hiding (_≈_)
  open BagEq S
  open Membership T using (lift-el; elem-of; ≋-refl; ≋-sym; ≋-trans)
  open Membership S using (El; belongs; elements; _⟷_) renaming (elem-of to elem-ofₛ)
  open _≅_
  open LocEquiv T using (_≋_)
  open LocEquiv S renaming (_≋_ to _≋ₛ_)
  open Locations T using (_∈₀_)
  open Locations S renaming (here to hereₛ; there to thereₛ) hiding (_∈₀_)

  copy-func : {l : List (Carrier S)} (F : S ⟶ T) → (e : elements l) → (F ⟨$⟩ Membership.witness e ∈₀ map (_⟨$⟩_ F) l)
  copy-func F (El (hereₛ sm)) = Locations.here (cong F sm)
  copy-func F (El (thereₛ belongs₁)) = Locations.there (copy-func F (El belongs₁))

  record shifted-elements (F : S ⟶ T) (l : List (Carrier S)) : Set (ℓS ⊔ ℓs) where
    constructor SE
    open Setoid T using (_≈_)
    field
      elem : Membership.elements S l
      {shift-witness} : Carrier T
      sw-good : shift-witness ≈ F ⟨$⟩ Membership.witness elem

  open shifted-elements

  copy-func-cong : {l : List (Carrier S)} (F : S ⟶ T) {i j : shifted-elements F l}
    → Membership.belongs (elem i) ≋ₛ Membership.belongs (elem j)
    → copy-func F (elem i) ≋ copy-func F (elem j)
  copy-func-cong F (LocEquiv.hereEq x≈z y≈z) = LocEquiv.hereEq (cong F x≈z) (cong F y≈z)
  copy-func-cong {_ ∷ _} F {SE (El (Locations.there el₁)) g₁} {SE (El (Locations.there el₂)) g₂}
    (LocEquiv.thereEq eq) = LocEquiv.thereEq (copy-func-cong F {SE (El el₁) g₁} {SE (El el₂) g₂} eq)

  copy-unfunc : {l : List (Carrier S)} (F : S ⟶ T) {w : Carrier T} → w ∈₀ map (_⟨$⟩_ F) l → shifted-elements F l
  copy-unfunc {[]} F {w} ()
  copy-unfunc {x ∷ l} F {w} (Locations.here sm) = record
    { elem = Membership.El {witness = x} (Locations.here (refl S))
    ; sw-good = sm }
  copy-unfunc {x ∷ l} F {w} (Locations.there kk) =
    let se = copy-unfunc {l} F {w} kk in
    record { elem = Membership.El (Locations.there (belongs (elem se))) ; sw-good = sw-good se }

  copy-unfunc-cong : {l : List (Carrier S)} (F : S ⟶ T) {w₁ w₂  : Carrier T}
    → {b₁ : w₁ ∈₀ map (_⟨$⟩_ F) l} → {b₂ : w₂ ∈₀ map (_⟨$⟩_ F) l} → b₁ ≋ b₂
    → belongs (elem (copy-unfunc F b₁)) ≋ₛ belongs (elem (copy-unfunc F b₂))
  copy-unfunc-cong {[]} F ()
  copy-unfunc-cong {x ∷ l} F (LocEquiv.hereEq x≈z y≈z) = LocEquiv.hereEq (refl S) (refl S)
  copy-unfunc-cong {x ∷ l} F (LocEquiv.thereEq b₁≋b₂) = LocEquiv.thereEq (copy-unfunc-cong {l} F b₁≋b₂)

  left-inv : {l : List (Carrier S)} {F : S ⟶ T} (x : Membership.elements T (map (_⟨$⟩_ F) l)) →
    copy-func F (elem (copy-unfunc F (Membership.belongs x))) ≋ Membership.belongs x
  left-inv {[]} (Membership.El ())
  left-inv {x ∷ l} {F} (Membership.El (Locations.here sm)) = LocEquiv.hereEq (cong F (refl S)) sm
  left-inv {x ∷ l} {F} (Membership.El (Locations.there belongs₁)) = LocEquiv.thereEq (left-inv (Membership.El belongs₁))

  right-inv : {l : List (Carrier S)} {F : S ⟶ T} (se : shifted-elements F l)
    → Membership.belongs (elem (copy-unfunc F (copy-func F (elem se)))) ≋ₛ Membership.belongs (elem se)
  right-inv {[]} {F} (SE (Membership.El ()) _)
  right-inv {x ∷ l} {F} (SE (Membership.El (Locations.here sm)) sw-good₁) = LocEquiv.hereEq (refl S) sm
  right-inv {x ∷ l} {F} (SE (Membership.El (Locations.there belongs₁)) sw-good₁) = thereEq (right-inv (SE (El belongs₁) sw-good₁))

  shifted : (S ⟶ T) → List (Carrier S) → Setoid (ℓS ⊔ ℓs) _
  shifted F l = record
    { Carrier = shifted-elements F l
    ; _≈_ = λ a b → elem a ⟷ elem b
    ; isEquivalence = record
      { refl = Membership.≋-refl S
      ; sym = Membership.≋-sym S
      ; trans = Membership.≋-trans S
      }
    }

  shift-map : (F : S ⟶ T) (l : List (Carrier S)) → elem-of (map (_⟨$⟩_ F) l) ≅ shifted F l
  shift-map F l = record
    { to = record
      { _⟨$⟩_ = λ { (El belongs₁) → copy-unfunc F belongs₁}
      ; cong = copy-unfunc-cong F }
    ; from = record
      { _⟨$⟩_ = λ {x → Membership.El (copy-func F (elem x))}
      ; cong = λ {i} {j} i≈j → copy-func-cong F {i} {j} i≈j } -- need to eta expand
    ; inverse-of = record
      { left-inverse-of = left-inv
      ; right-inverse-of = right-inv }
    }

  shifted-cong : (F : S ⟶ T) {xs ys : List (Carrier S)} (xs≈ys : xs ⇔ ys) → shifted F xs ≅ shifted F ys
  shifted-cong F xs≈ys = record
    { to = record
      { _⟨$⟩_ = λ sh → record
        { elem = Membership.El (belongs (to xs≈ys ⟨$⟩ (elem sh)))
        ; shift-witness = F ⟨$⟩ Membership.witness (to xs≈ys ⟨$⟩ elem sh)
        ; sw-good = refl T
        }
      ; cong = cong (to xs≈ys) }
    ; from = record
      { _⟨$⟩_ = λ sh → record
        { elem = Membership.El (belongs (from xs≈ys ⟨$⟩ elem sh))
        ; sw-good = refl T
        }
      ; cong = cong (from xs≈ys) }
    ; inverse-of = record
      { left-inverse-of = λ sh → left-inverse-of xs≈ys (elem sh)
      ; right-inverse-of = λ sh → right-inverse-of xs≈ys (elem sh)
      }
    }

\end{code}
%}}}

%{{{ \subsection{Properties of singleton lists}
\subsection{Properties of singleton lists}
\begin{code}
module ElemOfSing {ℓS ℓs} (X : Setoid ℓS ℓs) where
  open Setoid X renaming (Carrier to X₀)
  open BagEq X
  open Membership X
  open Locations X
  open LocEquiv X
  open SetoidCombinators X

  singleton-≈ : {i j : X₀} (i≈j : i ≈ j) → (i ∷ []) ⇔ (j ∷ [])
  singleton-≈ {i} {j} i≈j = record
    { to = record { _⟨$⟩_ = ∈a→∈b i≈j ; cong = cong-to i≈j }
    ; from = record { _⟨$⟩_ = ∈a→∈b (sym i≈j) ; cong = cong-to (sym i≈j) }
    ; inverse-of = record
      { left-inverse-of = inv i≈j (sym i≈j)
      ; right-inverse-of = inv (sym i≈j) i≈j }
    }
    where
      ∈a→∈b : {a b : X₀} → a ≈ b → elements (a ∷ []) → elements (b ∷ [])
      ∈a→∈b a≈b (Membership.El (Locations.here sm)) = El (here (sm ⟨≈≈⟩ a≈b))
      ∈a→∈b _   (Membership.El (Locations.there ()))

      cong-to : {a b : X₀} → (a≈b : a ≈ b) → {∈a₁ ∈a₂ : elements (a ∷ [])}
        → belongs ∈a₁ ≋ belongs ∈a₂ → belongs (∈a→∈b a≈b ∈a₁) ≋ belongs (∈a→∈b a≈b ∈a₂)
      cong-to a≈b (LocEquiv.hereEq x≈z y≈z) = LocEquiv.hereEq (x≈z ⟨≈≈⟩ a≈b) (y≈z ⟨≈≈⟩ a≈b)
      cong-to _   (LocEquiv.thereEq ())

      inv : {a b : X₀} (a≈b : a ≈ b) (b≈a : b ≈ a) (x : elements (a ∷ [])) →
        belongs (∈a→∈b b≈a (∈a→∈b a≈b x)) ≋ belongs x
      inv a≈b b≈a (El (here sm)) = LocEquiv.hereEq ((sm ⟨≈≈⟩ a≈b) ⟨≈≈⟩ b≈a) sm
      inv a≈b b≈a (El (there ()))
\end{code}
%}}}

%{{{ \subsection{Properties of fold over list}
\subsection{Properties of fold over list}
\begin{spec}
module ElemOfFold {ℓS ℓs} (X : Setoid ℓS ℓs) where
  open Setoid X renaming (Carrier to X₀)
  open BagEq X
  open Membership X
  open Locations X
  open LocEquiv X
  open import Data.List
  open CommMonoid
  open ElemOf[] X
  open _≅_

  fold-cong : {CM : CommMonoid X} {i j : List X₀} → i ⇔ j
    → foldr (_*_ CM) (e CM) i ≈ foldr (_*_ CM) (e CM) j
  fold-cong {CM} {[]} {[]} i⇔j = refl
  fold-cong {CM} {[]} {x ∷ j} i⇔j = ⊥-elim (elem-of-[] (from i⇔j ⟨$⟩ (El (here refl))))
  fold-cong {CM} {x ∷ i} {[]} i⇔j = ⊥-elim (elem-of-[] (to i⇔j ⟨$⟩ (El (here refl))))
  fold-cong {CM} {x ∷ i} {y ∷ j} i⇔j with (to i⇔j ⟨$⟩ (El (here refl)))
  ... | El pos = {!!}
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
