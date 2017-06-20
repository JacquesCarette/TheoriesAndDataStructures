\section{Some}

%{{{ Imports
\begin{code}
module Some where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary using (Setoid ; IsEquivalence ; Rel ;
  Reflexive ; Symmetric ; Transitive)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_ ; _⟨$⟩_ ; cong )
open import Function          using (_$_) renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; map)
open import Data.Product  using (∃)
open import Data.Nat      using (ℕ; zero; suc)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp

open import TypeEquiv using (swap₊)
open import SetoidSetoid
open import Relation.Binary.Sum

infix 4 inSetoidEquiv
inSetoidEquiv : {a ℓ : Level} → (S : Setoid a ℓ) → Setoid.Carrier S → Setoid.Carrier S → Set ℓ
inSetoidEquiv = Setoid._≈_

syntax inSetoidEquiv S x y = x ≈⌊ S ⌋ y
\end{code}
%}}}

The goal of this section is to capture a notion that we have a proof
of a property |P| of an element |x| belonging to a list |xs|.  But we don't
want just any proof, but we want to know \emph{which} |x ∈ xs| is the witness.
However, we are in the |Setoid| setting, and in a setting where multiplicity
matters (i.e. we may have |x| occuring twice in |xs|, yielding two different
proofs that |P| holds). And we do not care very much about the exact |x|,
any |y| such that |x ≈ y| will do, as long as it is in the ``right'' location.

And then we want to capture the idea of when two such are equivalent --
when is it that |Some P xs| is just as good as |Some P ys|?  In fact, we'll
generalize this some more to |Some Q ys|.

For the purposes of |CommMonoid| however, all we really need is some notion
of Bag Equivalence.  However, many of the properties we need to establish
are simpler if we generalize to the situation described above.
%{{{ \subsection{|Some₀|}
\subsection{|Some₀|}
|Setoid|-based variant of Any.

Quite a bit of this is directly inspired by |Data.List.Any| and |Data.List.Any.Properties|.

\edcomm{WK}{|A ⟶ SSetoid _ _| is a pretty strong assumption.
Logical equivalence does not ask for the two morphisms back and forth to be inverse.}
\edcomm{JC}{This is pretty much directly influenced by Nisse's paper: logical equivalence
only gives Set, not Multiset, at least if used for the equivalence of over List.  To
get Multiset, we need to preserve full equivalence, i.e. capture permutations.  My reason
to use |A ⟶ SSetoid _ _| is to mesh well with the rest.  It is not cast in stone and
can potentially be weakened.}
\begin{code}
module _ {a ℓa} {S : Setoid a ℓa} (P₀ : Setoid.Carrier S → Set ℓa) where
   open Setoid S renaming (Carrier to A)
   data Some₀  : List A → Set (a ⊔ ℓa) where
     here  : {x a : A} {xs : List A} (sm : a ≈ x) (px  : P₀ a    ) → Some₀ (x ∷ xs)
     there : {x   : A} {xs : List A}              (pxs : Some₀ xs) → Some₀ (x ∷ xs)
\end{code}

Inhabitants of |Some₀| really are just locations:
|Some₀ P xs  ≅ Σ i ∶ Fin (length xs) • P (x ‼ i)|.
Thus one possibility is to go with natural numbers directly,
but that seems awkward. Nevertheless, the 'location' function
is straightforward:
\begin{code}
   toℕ : {xs : List A} → Some₀ xs → ℕ
   toℕ (here _ _) = 0
   toℕ (there pf) = suc (toℕ pf)
\end{code}

\begin{code}
module _ {a ℓa} {S : Setoid a ℓa} {P₀ : Setoid.Carrier S → Set ℓa} where
   open Setoid S renaming (Carrier to A)
   infix 3 _≋_
   data _≋_ : {xs : List A} (pf pf' : Some₀ {S = S} P₀ xs) → Set (a ⊔ ℓa) where
     hereEq : {xs : List A} {x y z : A} (px : P₀ x) (qy : P₀ y)
            → (x≈z : x ≈ z) → (y≈z : y ≈ z)
            → _≋_ (here {x = z} {x} {xs} x≈z px) (here {x = z} {y} {xs} y≈z qy)
     thereEq : {xs : List A} {x : A} {pxs : Some₀ P₀ xs} {qxs : Some₀ P₀ xs}
             → _≋_ pxs qxs → _≋_ (there {x = x} pxs) (there {x = x} qxs)
\end{code}

Notice that these another from of ``natural numbers'' whose elements are of the form
|thereEqⁿ (hereEq Px Qx)| for some |n : ℕ|.

\begin{code}
module _ {a ℓa} {S : Setoid a ℓa} {P₀ : Setoid.Carrier S → Set ℓa} where
   open Setoid S renaming (Carrier to A)
   ≋-refl : {xs : List A} {p : Some₀ {S = S} P₀ xs} → p ≋ p
   ≋-refl {p = here a≈x px} = hereEq px px a≈x a≈x
   ≋-refl {p = there p} = thereEq ≋-refl

   ≋-sym : {xs : List A} {p : Some₀ {S = S} P₀ xs} {q : Some₀ P₀ xs} → p ≋ q → q ≋ p
   ≋-sym (hereEq a≈x b≈x px py) = hereEq b≈x a≈x py px
   ≋-sym (thereEq eq) = thereEq (≋-sym eq)

   ≋-trans : {xs : List A} {p q r : Some₀ {S = S} P₀ xs}
           → p ≋ q → q ≋ r → p ≋ r
   ≋-trans (hereEq pa qb a≈x b≈x) (hereEq pc qd c≈y d≈y) = hereEq pa qd _ _
   ≋-trans (thereEq e) (thereEq f) = thereEq (≋-trans e f)

module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid ℓa ℓa) where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   Some : List Carrier → Setoid (ℓa ⊔ a) (ℓa ⊔ a)
   Some xs = record
     { Carrier         =   Some₀ {S = A} P₀ xs
     ; _≈_             =   _≋_
     ; isEquivalence   = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
     }

≡→Some : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa}
         {xs ys : List (Setoid.Carrier A)} → xs ≡ ys → Some P xs ≅ Some P ys
≡→Some {A = A} ≡.refl = ≅-refl
\end{code}
%}}}

%{{{ \subsection{Membership module}: setoid≈ ; _∈_ ; _∈₀_
\subsection{Membership module}

\savecolumns
\begin{code}
module Membership {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (trans to _⟨≈≈⟩_)

  infix 4 _∈₀_ _∈_
\end{code}

|setoid≈ x| is actually a mapping from |S| to |SSetoid _ _|; it maps
elements |y| of |Carrier S| to the setoid of "|x ≈ₛ y|".

\restorecolumns
\begin{code}
  setoid≈ : Carrier → S ⟶ SSetoid ℓ ℓ
  setoid≈ x = record
    { _⟨$⟩_ = λ (y : Carrier) → _≈S_ {A = S} x y
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈≈⟩ i≈j     ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈j → x≈j ⟨≈≈⟩ sym i≈j ; cong = λ _ → tt }
      ; inverse-of = record
        { left-inverse-of = λ _ → tt
        ; right-inverse-of = λ _ → tt
        }
      }
    }

  _∈_ : Carrier → List Carrier → Setoid (a ⊔ ℓ) (ℓ ⊔ a)
  x ∈ xs = Some (setoid≈ x) xs

  _∈₀_ : Carrier → List Carrier → Set (ℓ ⊔ a)
  x ∈₀ xs = Setoid.Carrier (x ∈ xs)

  ∈₀-subst₁ : {x y : Carrier} {xs : List Carrier} → x ≈ y → x ∈₀ xs → y ∈₀ xs
  ∈₀-subst₁ {x} {y} {.(_ ∷ _)} x≈y (here a≈x px) = here a≈x (sym x≈y ⟨≈≈⟩ px)
  ∈₀-subst₁ {x} {y} {.(_ ∷ _)} x≈y (there x∈xs) = there (∈₀-subst₁ x≈y x∈xs)

  BagEq : (xs ys : List Carrier) → Set (ℓ ⊔ a)
  BagEq xs ys = {x : Carrier} → (x ∈ xs) ≅ (x ∈ ys)


  ∈₀-Subst₂ : {x : Carrier} {xs ys : List Carrier} → BagEq xs ys → x ∈ xs ⟶ x ∈ ys
  ∈₀-Subst₂ {x} {xs} {ys} xs≅ys = _≅_.to (xs≅ys {x})

  ∈₀-subst₂ : {x : Carrier} {xs ys : List Carrier} → BagEq xs ys → x ∈₀ xs → x ∈₀ ys
  ∈₀-subst₂ xs≅ys x∈xs = ∈₀-Subst₂ xs≅ys ⟨$⟩ x∈xs

  ∈₀-subst₂-cong  : {x : Carrier} {xs ys : List Carrier} (xs≅ys : BagEq xs ys)
                  → {p q : x ∈₀ xs}
                  → p ≈⌊ x ∈ xs ⌋ q
                  → ∈₀-subst₂ xs≅ys p ≈⌊ x ∈ ys ⌋ ∈₀-subst₂ xs≅ys q
  ∈₀-subst₂-cong xs≅ys = cong (∈₀-Subst₂ xs≅ys)

{-
  ∈₀-cong₂ : {x : Carrier} {xs ys : List Carrier} → BagEq xs ys → (x ∈ xs) ≅ (x ∈ ys)
  ∈₀-cong₂ {x} {xs} {ys} xs≅ys = ?
-}
\end{code}
%}}}

%{{{ \subsection{|++≅ : ⋯ → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)|}
\subsection{|++≅ : ⋯ → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)|}
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where
  ++≅ : {xs ys : List (Setoid.Carrier A) } → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
  ++≅ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong =  ⊎→++-cong  }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = new-cong xs }
    ; inverse-of = record
      { left-inverse-of = lefty xs
      ; right-inverse-of = righty xs
      }
    }
    where
      open Setoid A
      private P₀ = λ e → Setoid.Carrier (P ⟨$⟩ e)
      _∽_ = _≋_ ; ∽-refl = ≋-refl {S = A} {P₀}

      -- ``ealier''
      ⊎→ˡ : ∀ {ws zs} → Some₀ {S = A} P₀ ws → Some₀ {S = A} P₀ (ws ++ zs)
      ⊎→ˡ (here p a≈x) = here p a≈x
      ⊎→ˡ (there p) = there (⊎→ˡ p)

      yo : {xs : List Carrier} {x y : Some₀ P₀ xs} → x ∽ y   →   ⊎→ˡ x  ∽  ⊎→ˡ y
      yo (hereEq px py _ _) = hereEq px py _ _
      yo (thereEq pf) = thereEq (yo pf)

      -- ``later''
      ⊎→ʳ : ∀ xs {ys} → Some₀ {S = A} P₀ ys → Some₀ P₀ (xs ++ ys)
      ⊎→ʳ []       p = p
      ⊎→ʳ (x ∷ xs) p = there (⊎→ʳ xs p)

      oy : (xs : List Carrier) {x y : Some₀ P₀ ys} → x ∽ y   →   ⊎→ʳ xs x  ∽  ⊎→ʳ xs y
      oy [] pf = pf
      oy (x ∷ xs) pf = thereEq (oy xs pf)

      -- |Some₀| is |++→⊎|-homomorphic, in the second argument.

      ⊎→++ : ∀ {zs ws} → (Some₀ P₀ zs ⊎ Some₀ P₀ ws) → Some₀ P₀ (zs ++ ws)
      ⊎→++      (inj₁ x) = ⊎→ˡ x
      ⊎→++ {zs} (inj₂ y) = ⊎→ʳ zs y

      ++→⊎ : ∀ xs {ys} → Some₀ P₀ (xs ++ ys) → Some₀ P₀ xs ⊎ Some₀ P₀ ys
      ++→⊎ []             p    = inj₂ p
      ++→⊎ (x ∷ l) (here  p _) = inj₁ (here p _)
      ++→⊎ (x ∷ l) (there p)   = (there ⊎₁ id₀) (++→⊎ l p)

      -- all of the following may need to change

      ⊎→++-cong : {a b : Some₀ P₀ xs ⊎ Some₀ P₀ ys} → (_∽_ ∥ _∽_) a b → ⊎→++ a ∽ ⊎→++ b
      ⊎→++-cong (left  x₁∼x₂)  =  yo x₁∼x₂
      ⊎→++-cong (right y₁∼y₂)  =  oy xs y₁∼y₂

      ∽∥∽-cong   :  {xs ys us vs : List Carrier}
                    (F : Some₀ {S = A} P₀ xs → Some₀ {S = A} P₀ us)
                    (F-cong : {p q : Some₀ P₀ xs} → p ∽ q → F p ∽ F q)
                    (G : Some₀ {S = A} P₀ ys → Some₀ {S = A} P₀ vs)
                    (G-cong : {p q : Some₀ P₀ ys} → p ∽ q → G p ∽ G q)
                    → {pf pf' : Some₀ P₀ xs ⊎ Some₀ P₀ ys}
                    → (_∽_ ∥ _∽_) pf pf' → (_∽_ ∥ _∽_) ( (F ⊎₁ G) pf) ((F ⊎₁ G) pf')
      ∽∥∽-cong F F-cong G G-cong (left x~₁y) = left (F-cong x~₁y)
      ∽∥∽-cong F F-cong G G-cong (right x~₂y) = right (G-cong x~₂y)

      new-cong : (xs : List Carrier) {i j : Some₀ P₀ (xs ++ ys)} → i ∽ j → (_∽_ ∥ _∽_) (++→⊎ xs i) (++→⊎ xs j)
      new-cong [] pf = right pf
      new-cong (x ∷ xs) (hereEq px py _ _) = left (hereEq px py _ _)
      new-cong (x ∷ xs) (thereEq pf) = ∽∥∽-cong there thereEq id₀ id₀ (new-cong xs pf)

      lefty : (xs {ys} : List Carrier) (p : Some₀ P₀ xs ⊎ Some₀ P₀ ys) → (_∽_ ∥ _∽_) (++→⊎ xs (⊎→++ p)) p
      lefty [] (inj₁ ())
      lefty [] (inj₂ p) = right ≋-refl
      lefty (x ∷ xs) (inj₁ (here px _)) = left ∽-refl
      lefty (x ∷ xs) {ys} (inj₁ (there p)) with ++→⊎ xs {ys} (⊎→++ (inj₁ p)) | lefty xs {ys} (inj₁ p)
      ... | inj₁ _ | (left x~₁y) = left (thereEq x~₁y)
      ... | inj₂ _ | ()
      lefty (z ∷ zs) {ws} (inj₂ p) with ++→⊎ zs {ws} (⊎→++ {zs} (inj₂ p)) | lefty zs (inj₂ p)
      ... | inj₁ x | ()
      ... | inj₂ y | (right x~₂y) = right x~₂y

      righty : (zs {ws} : List Carrier) (p : Some₀ P₀ (zs ++ ws)) → (⊎→++ (++→⊎ zs p)) ∽ p
      righty [] {ws} p = ∽-refl
      righty (x ∷ zs) {ws} (here px _) = ∽-refl
      righty (x ∷ zs) {ws} (there p) with ++→⊎ zs p | righty zs p
      ... | inj₁ _  | res = thereEq res
      ... | inj₂ _  | res = thereEq res
\end{code}
%}}}

%{{{ \subsection{Bottom as a setoid} ⊥⊥ ; ⊥≅Some[] : ⊥⊥ ≅ Some P []
\subsection{Bottom as a setoid}
\begin{code}
⊥⊥ : ∀ {a ℓa} → Setoid a ℓa
⊥⊥ {a} {ℓa} = record
  { Carrier = ⊥
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  }
\end{code}

\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where

  ⊥≅Some[] : ⊥⊥ {a} {ℓa} ≅ Some P []
  ⊥≅Some[] = record
    { to          =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; from        =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; inverse-of  =   record { left-inverse-of = λ _ → tt ; right-inverse-of = λ {()} }
    }
\end{code}
%}}}

%{{{ \subsection{|map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)|}
\subsection{|map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)|}
\begin{code}
map≅ : ∀ {a ℓa} {A B : Setoid a ℓa} {P : B ⟶ SSetoid ℓa ℓa} {f : A ⟶ B} {xs : List (Setoid.Carrier A)} →
       Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)
map≅ {a} {ℓa} {A} {B} {P} {f} = record
  { to = record { _⟨$⟩_ = map⁺ ; cong = map⁺-cong }
  ; from = record { _⟨$⟩_ = map⁻ ; cong = map⁻-cong }
  ; inverse-of = record { left-inverse-of = map⁻∘map⁺ ; right-inverse-of = map⁺∘map⁻ }
  }
  where
  open Setoid
  A₀ = Carrier A
  P₀ = λ e → Carrier (P ⟨$⟩ e)
  _∼_ = _≋_ {S = B} {P₀ = P₀}

  map⁺ : {xs : List A₀} → Some₀ {S = A} (P₀ ⊚ _⟨$⟩_ f) xs → Some₀ {S = B} P₀ (map (_⟨$⟩_ f) xs)
  map⁺ (here a≈x p)  = here (Π.cong f a≈x) p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : {xs : List A₀} → Some₀ {S = B} P₀ (map (_⟨$⟩_ f) xs) → Some₀ {S = A} (P₀ ⊚ (_⟨$⟩_ f)) xs
  map⁻ {[]} ()
  map⁻ {x ∷ xs} (here {b} b≈x p) = here (refl A) (_≅_.to (Π.cong P b≈x) ⟨$⟩ p)
  map⁻ {x ∷ xs} (there p) = there (map⁻ {xs = xs} p)

  -- the following definition should be moved up
  transport : {C : Setoid a ℓa} (Q : C ⟶ SSetoid ℓa ℓa) →
    let Q₀ = λ e → Carrier (Q ⟨$⟩ e) in let open Setoid C renaming (_≈_ to _≈ₐ_) in
    {a x : Carrier C} (p : Q₀ a) (a≈x : a ≈ₐ x) → Q₀ x
  transport Q p a≈x = _≅_.to (Π.cong Q a≈x) ⟨$⟩ p

  map⁺∘map⁻ : {xs : List A₀ } → (p : Some₀ P₀ (map (_⟨$⟩_ f) xs)) → map⁺ (map⁻ p) ∼ p
  map⁺∘map⁻ {[]} ()
  map⁺∘map⁻ {x ∷ xs} (here b≈x p) = hereEq (transport P p b≈x) p (Π.cong f (refl A)) b≈x
  map⁺∘map⁻ {x ∷ xs} (there p) = thereEq (map⁺∘map⁻ p)

  map⁻∘map⁺ : {xs : List A₀} → (p : Some₀ (P₀ ⊚ (_⟨$⟩_ f)) xs)
            → let _∼₂_ = _≋_ {P₀ = P₀ ⊚ (_⟨$⟩_ f)} in map⁻ (map⁺ p) ∼₂ p
  map⁻∘map⁺ {[]} ()
  map⁻∘map⁺ {x ∷ xs} (here a≈x p) = hereEq (transport (P ∘ f) p a≈x) p (refl A) a≈x
  map⁻∘map⁺ {x ∷ xs} (there p) = thereEq (map⁻∘map⁺ p)

  map⁺-cong : {ys : List A₀} {i j : Some₀ (P₀ ⊚ _⟨$⟩_ f) ys} →  _≋_ {P₀ = P₀ ⊚ _⟨$⟩_ f} i j → map⁺ i ∼ map⁺ j
  map⁺-cong (hereEq px py x≈z y≈z) = hereEq px py (Π.cong f x≈z) (Π.cong f y≈z)
  map⁺-cong (thereEq i∼j) = thereEq (map⁺-cong i∼j)

  map⁻-cong : {ys : List A₀} {i j : Some₀ P₀ (map (_⟨$⟩_ f) ys)} → i ∼ j → _≋_ {P₀ = P₀ ⊚ _⟨$⟩_ f} (map⁻ i) (map⁻ j)
  map⁻-cong {[]} ()
  map⁻-cong {z ∷ zs} (hereEq {x = x} {y} px py x≈z y≈z) =
    hereEq (transport P px x≈z) (transport P py y≈z) (refl A) (refl A)
  map⁻-cong {z ∷ zs} (thereEq i∼j) = thereEq (map⁻-cong i∼j)
\end{code}
%}}}

%{{{ \subsection{FindLose}
\subsection{FindLose}

\begin{code}
module FindLose {a ℓa : Level} {A : Setoid a ℓa}  (P : A ⟶ SSetoid ℓa ℓa) where
 open Membership A
 open Setoid A
 open Π
 open _≅_
 private
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y

 find : {ys : List Carrier} → Some₀ {S = A} P₀ ys → Support ys
 find {y ∷ ys} (here a≈x p) = y , here refl refl , {!transport P !}
 find {y ∷ ys} (there p) =  let (a , a∈ys , Pa) = find p
                            in a , there a∈ys , Pa

 lose : {ys : List Carrier} → Support ys → Some₀ {S = A} P₀ ys
 lose (y , here b≈y py , Py)  = here b≈y (_≅_.to (Π.cong P py) Π.⟨$⟩ Py)
 lose (y , there y∈ys , Py)   = there (lose (y , y∈ys , Py))
\end{code}

\edcomm{MA}{Below are old, inactive, attempts.}

\begin{spec}
 -- ``If an element of |ys| has a property |P|, then some element of |ys| has property |P|.''
 -- cf.\null{} |copy| below
 Some-Intro : {y : Carrier} {ys : List Carrier}
      → y ∈₀ ys → P₀ y → Some₀ P₀ ys
 Some-Intro {y} y∈ys Qy = lose (y , y∈ys , Qy)

 bag-as-⇒ : {xs ys : List Carrier} → BagEq xs ys → Some₀ P₀ xs → Some₀ P₀ ys
 bag-as-⇒ xs≅ys Pxs = let (x , x∈xs , Px) = find Pxs in
                       let x∈ys = to xs≅ys ⟨$⟩ x∈xs
                       in lose (x , x∈ys , Px)

 _∻₀_ : {xs : List Carrier} → Support xs → Support xs → Set ℓa
 (a , a∈xs , Pa) ∻₀ (b , b∈xs , Pb) =  Σ (a ≈ b) (λ p → a∈xs ≋ {!b∈xs!})

 find-cong₀ : {xs : List Carrier} {p q : Some₀ P₀ xs} → p ≋ q → find p ∻₀ find q
 find-cong₀ (hereEq px qy) = refl , ≋-refl
 find-cong₀ (thereEq eq) = let (fst , snd) = find-cong₀ eq in fst , thereEq snd

 private

   P⁺ : {x y : Carrier} → x ≈ y → P₀ x → P₀ y
   P⁺ x≈y = Π._⟨$⟩_ (_≅_.to (Π.cong P x≈y))

 lose-cong₀ : {xs : List Carrier} {p q : Support xs} → p ∻₀ q → lose p ≋ lose q
 lose-cong₀ {p = a , here a≈x , Pa} {b , here b≈x , Pb} (fst , hereEq .a≈x .b≈x) = hereEq (P⁺ a≈x Pa) (P⁺ b≈x Pb)
 lose-cong₀ {p = a , here a≈x , Pa} {b , there b∈ys , Pb} (fst , ())
 lose-cong₀ {p = a , there a∈xs , Pa} {b , here px , Pb} (fst , ())
 lose-cong₀ {p = a , there a∈xs , Pa} {b , there b∈ys , Pb} (a≈b , thereEq a∈xs≋b∈ys) = thereEq (lose-cong₀ (a≈b , a∈xs≋b∈ys))

 BagEq-cong≋  : {xs ys : List Carrier} (xs≅ys : BagEq xs ys) {x₁ x₂ : Carrier}
              → {x₁∈xs : x₁ ∈₀ xs} {x₂∈xs : x₂ ∈₀ xs}
              → (x₁∈xs≋x₂∈xs : x₁∈xs  ≋ x₂∈xs)
              → ∈₀-subst₂ xs≅ys x₁∈xs ≋ ∈₀-subst₂ xs≅ys x₂∈xs
 -- \edcomm{WK}{That is, |xs≅ys| preserves position-equality.}
 -- \edcomm{WK}{I don't think it has to, from the definition of |BagEq|! \unfinished}
 BagEq-cong≋ {xs} {ys} xs≅ys {x₁} {x₂} {x₁∈xs} {x₂∈xs} x₁∈xs≋x₂∈xs = {!!}



 bag-as-⇒-cong  : {xs ys : List Carrier} {xs≅ys : BagEq xs ys}
                → {p q : Some₀ P₀ xs} → p ≋ q → bag-as-⇒ xs≅ys p ≋ bag-as-⇒ xs≅ys q
 bag-as-⇒-cong {xs} {ys} {xs≅ys} {p} {q} p≋q = let
    a , a∈xs , Pa = find p
    b , b∈xs , Pb = find q
    a≈b , a∈xs≋b∈xs = find-cong₀ p≋q
    a∈ys : a ∈₀ ys
    a∈ys = ∈₀-subst₂ xs≅ys a∈xs
    b∈ys : b ∈₀ ys
    b∈ys = ∈₀-subst₂ xs≅ys b∈xs
  in let
    a∈ys≋b∈ys : a∈ys ≋ b∈ys
    a∈ys≋b∈ys = BagEq-cong≋ xs≅ys a∈xs≋b∈xs
  in lose-cong₀ (a≈b , a∈ys≋b∈ys)

module FindLoseCong {a ℓa : Level} {A : Setoid a ℓa}  {P : A ⟶ SSetoid ℓa ℓa} {Q : A ⟶ SSetoid ℓa ℓa} where
 open Membership A
 open Setoid A
 private
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   Q₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ Q e)
   PSupport = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y
   QSupport = λ ys → Σ y ∶ Carrier • y ∈₀ ys × Q₀ y

 _∻_ : {xs ys : List Carrier} → PSupport xs → QSupport ys → Set ℓa
 (a , a∈xs , Pa) ∻ (b , b∈ys , Qb) =  a ≈ b  ×  a∈xs ≋ b∈ys

 open FindLose

 find-cong : {ys : List Carrier} {p : Some₀ P₀ ys} {q : Some₀ Q₀ ys} → p ≋ q → find P p ∻ find Q q
 find-cong (hereEq px qy) = refl , ≋-refl
 find-cong (thereEq eq) = let (fst , snd) = find-cong eq in fst , thereEq snd

 private

   P⁺ : {x y : Carrier} → x ≈ y → P₀ x → P₀ y
   P⁺ x≈y = Π._⟨$⟩_ (_≅_.to (Π.cong P x≈y))

   Q⁺ : {x y : Carrier} → x ≈ y → Q₀ x → Q₀ y
   Q⁺ x≈y = Π._⟨$⟩_ (_≅_.to (Π.cong Q x≈y))

 lose-cong : {xs ys : List Carrier} {p : PSupport xs} {q : QSupport ys} → p ∻ q → lose P p ≋ lose Q q
 lose-cong {p = a , here a≈x , Pa} {b , here b≈x , Qb} (fst , hereEq .a≈x .b≈x) = hereEq (P⁺ a≈x Pa) (Q⁺ b≈x Qb)
 lose-cong {p = a , here a≈x , Pa} {b , there b∈ys , Qb} (fst , ())
 lose-cong {p = a , there a∈xs , Pa} {b , here px , Qb} (fst , ())
 lose-cong {p = a , there a∈xs , Pa} {b , there b∈ys , Qb} (a≈b , thereEq a∈xs≋b∈ys) = thereEq (lose-cong (a≈b , a∈xs≋b∈ys))


 cong-fwd : {xs ys : List Carrier} {xs≅ys : BagEq xs ys} {p : Some₀ P₀ xs} {q : Some₀ Q₀ xs}
          → p ≋ q → bag-as-⇒ P xs≅ys p ≋ bag-as-⇒ Q xs≅ys q
 cong-fwd {xs} {ys} {xs≅ys} {p} {q} p≋q = let
    a≈b , a∈xs≋b∈xs = find-cong p≋q
  in let a∈ys≋b∈ys = ≋-trans (Π.cong (_≅_.to xs≅ys) {{!!}} {{!!}} {!a∈xs≋b∈xs!}) {!!}
  in lose-cong (a≈b , a∈ys≋b∈ys)
\end{spec}

\begin{spec}
 cong-fwd {xs} {ys} {xs≅ys} {p} {q} p≋q with find P p | find Q q | find-cong p≋q
 ...| (x , x∈xs , px) | (y , y∈xs , py) | (x≈y , x∈xs≋y∈xs) = lose-cong (x≈y , goal)

   where

     open _≅_ (xs≅ys {x}) using () renaming (to to F)  -- \edcomm{WK}{Pretty horrible renamings.}
     open _≅_ (xs≅ys {y}) using () renaming (to to G)  -- \edcomm{WK}{At least without diagram or plenty of explanation.}

     F-cong : {a b : x ∈₀ xs} → a ≋ b → F ⟨$⟩ a ≋ F ⟨$⟩ b
     F-cong = Π.cong F

     G-cong : {a b : y ∈₀ xs} → a ≋ b → G ⟨$⟩ a ≋ G ⟨$⟩ b
     G-cong = Π.cong G

     To = λ {i} → Π._⟨$⟩_ (_≅_.to (xs≅ys {i}))

     -- |postulate helper : {i j : Carrier} → i ≈ j → {!To {i} ≐ To {j}!}|
     -- \edcomm{WK}{Don't activate unused postulates.}
     -- switch to john major equality in the defn of ≐ ?

     goal : F ⟨$⟩ x∈xs ≋ G ⟨$⟩ y∈xs
     goal =  ≋-trans ({! _≅_.left-inverse-of (xs≅ys {y}) y∈xs {- {x∈xs} {{!!}} {! x∈xs≋y∈xs !} -}!}) {!!}

     y∈ysT : y ∈₀ xs
     y∈ysT = y∈xs
\end{spec}

\edcomm{WK}{Indentation needs to be fixed: Always by at least two positions.}

%}}}

%{{{ \subsection{Some-cong and holes} (∀ {x} → x ∈ xs₁ ≅ x ∈ xs₂) → Some P xs₁ ≅ Some P xs₂
\subsection{Some-cong and holes}
This isn't quite the full-powered cong, but is all we need.
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where
 open Membership A
 open Setoid A
 private
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y

 _∻_ : {ys : List Carrier} → Support ys → Support ys → Set (a ⊔ ℓa)
 (a , a∈xs , Pa) ∻ (b , b∈xs , Pb) =  Σ (a ≈ b) (λ a≈b → {!!} ≋ b∈xs)

 Σ-Setoid : (ys : List Carrier) → Setoid (ℓa ⊔ a) (ℓa ⊔ a)
 Σ-Setoid ys = record
   { Carrier = Support ys
   ; _≈_ = _∻_
   ; isEquivalence = record
     { refl = λ {s} → Refl {s}
     ; sym = λ {s} {t} eq → Sym {s} {t} eq
     ; trans = λ {s} {t} {u} a b → Trans {s} {t} {u} a b
     }
   }
   where
     Refl : Reflexive _∻_
     Refl {a , a∈xs , Pa} = refl , ≋-refl

     Sym  : Symmetric _∻_
     Sym (a≈b , a∈xs≋b∈xs) = sym a≈b , {!!} -- |≋-sym a∈xs≋b∈xs|

     Trans : Transitive _∻_
     Trans (a≈b , a∈xs≋b∈xs) (b≈c , b∈xs≋c∈xs) = trans a≈b b≈c , {!!} -- |≋-trans a∈xs≋b∈xs {! b∈xs≋c∈xs !} |

 module ∻ {ys} where open Setoid (Σ-Setoid ys) public

 open FindLose P
 -- |open FindLoseCong hiding (_∻_)|

 left-inv : {ys : List Carrier} (x∈ys : Some₀ P₀ ys) → lose (find x∈ys) ≋ x∈ys
 left-inv (here a≈x px) = hereEq {!!} {!!} {!!} {!!}
 left-inv (there x∈ys) = thereEq (left-inv x∈ys)

 right-inv : {ys : List Carrier} (pf : Σ y ∶ Carrier • y ∈₀ ys × P₀ y) → find (lose pf) ∻ pf
 right-inv (y , here a≈x px , Py) = {!!} , hereEq {!!} {!!} {!!} {!!}
 right-inv (y , there y∈ys , Py) = (proj₁ (right-inv (y , y∈ys , Py))) , (thereEq (proj₂ (right-inv (y , y∈ys , Py))))

 Σ-Some : (xs : List Carrier) → Some P xs ≅ Σ-Setoid xs
 Σ-Some xs = record
   { to = record { _⟨$⟩_ = find {xs} ; cong = {!!} }
   ; from = record { _⟨$⟩_ = lose ; cong = {!!} }
   ; inverse-of = record
     { left-inverse-of = left-inv
     ; right-inverse-of = right-inv
     }
   }
\end{code}

\edcomm{MA}{Below are some old, inactive, attempts.}

\begin{spec}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where

 open Membership A
 open Setoid A
 private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

 Some-cong : {xs₁ xs₂ : List Carrier} →
           (∀ {x} → (x ∈ xs₁) ≅ (x ∈ xs₂)) →
           Some P xs₁ ≅ Some P xs₂
 Some-cong {xs₁} {xs₂} list-rel = record
  { to           =   record
     { _⟨$⟩_ = bag-as-⇒ list-rel
     ; cong = FindLoseCong.cong-fwd {P = P} {Q = P} {xs≅ys = list-rel}
     }
  ; from = record
    { _⟨$⟩_ = xs₁→xs₂ (≅-sym list-rel)
    ; cong = {! {- \unfinished -}!} }
  ; inverse-of = record
    { left-inverse-of = {! {- \unfinished -}!}
    ; right-inverse-of = {! {- \unfinished -}!}
    }
  }
  where

  open FindLose P using (bag-as-⇒ ; find)

  -- this is probably a specialized version of Respects.
  -- is also related to an uncurried version of |lose|.
  copy : ∀ {x} {ys} {Q : A ⟶ SSetoid ℓa ℓa} → x ∈₀ ys → (Setoid.Carrier (Π._⟨$⟩_ Q x)) → Some₀ (λ e → Setoid.Carrier (Q ⟨$⟩ e)) ys
  copy {Q = Q} (here p)  pf = here (_≅_.to (Π.cong Q p) ⟨$⟩ pf)
  copy         (there p) pf = there (copy p pf)

  -- \edcomm{Somebody}{this should be generalized to |qy| coming from |Q₀ x|.}
  copy-cong : {x y : Carrier} {xs ys : List Carrier} {Q : A ⟶ SSetoid ℓa ℓa}
    (px : P₀ x) (qy : Setoid.Carrier (Π._⟨$⟩_ Q y)) (x∈xs : x ∈₀ xs) (y∈ys : y ∈₀ ys) →
    (x∈xs ≋ y∈ys) → copy {Q = P} x∈xs px ≋ copy {Q = Q} y∈ys qy
  copy-cong px qy₁ (here px₁) .(here qy) (hereEq .px₁ qy) = hereEq _ _
  copy-cong px qy (there i) .(there _) (thereEq i≋j) = thereEq (copy-cong px qy _ _ i≋j)

  xs₁→xs₂ : ∀ {xs ys} →  (∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → Some₀ P₀ xs → Some₀ P₀ ys
  xs₁→xs₂ {xs} rel p =
    let pos = find {ys = xs} p in
    copy (_≅_.to rel ⟨$⟩ proj₁ (proj₂ pos)) (proj₂ (proj₂ pos))

  cong-fwd : {i j : Some₀ P₀ xs₁} →
    i ≋ j → xs₁→xs₂ list-rel i ≋ xs₁→xs₂ list-rel j
  cong-fwd {i} {j} i≋j = copy-cong _ _ _ _ {! {- \unfinished -}!}
\end{spec}

%}}}

\iffalse
\fi

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
