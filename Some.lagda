\section{Some}

%{{{ Imports
\begin{code}
module Some where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary using (Setoid ; IsEquivalence ; Rel ;
  Reflexive ; Symmetric ; Transitive)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_; _⟨$⟩_)
open import Function          using (_$_) renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; map)
open import Data.Product  using (∃)
open import Data.Nat      using (ℕ; zero; suc)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv

open import TypeEquiv using (swap₊)
open import SetoidSetoid
open import Relation.Binary.Sum

open import Relation.Binary.PropositionalEquality using (inspect)
\end{code}
%}}}

\edcomm{WK}{Goal?}

%{{{ \subsection{|Some₀|}
\subsection{|Some₀|}
Setoid based variant of Any.

Quite a bit of this is directly inspired by |Data.List.Any| and |Data.List.Any.Properties|.

\edcomm{WK}{|A ⟶ SSetoid _ _| is a pretty strong assumption.
Logical equivalence does not ask for the two morphisms back and forth to be inverse.}
\edcomm{JC}{This is pretty much directly influenced by Nisse's paper: logical equivalence
only gives Set, not Multiset, at least if used for the equivalence of over List.  To
get Multiset, we need to preserve full equivalence, i.e. capture permutations.  My reason
to use |A ⟶ SSetoid _ _| is to mesh well with the rest.  It is not cast in stone and
can potentially be weakened.}
\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid ℓa ℓa) where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   data Some₀  : List Carrier → Set (a ⊔ ℓa) where
     here  : {x : Carrier} {xs : List Carrier} (px  : P₀ x    ) → Some₀ (x ∷ xs)
     there : {x : Carrier} {xs : List Carrier} (pxs : Some₀ xs) → Some₀ (x ∷ xs)
\end{code}

Inhabitants of |Some₀| really are just locations:
|Some₀ P xs  ≅ Σ i ∶ Fin (length xs) • P (x ‼ i)|.
Thus one possibility is to go with natural numbers directly,
and entirely ignore the proof contained in a |Some₀ P xs|.
\begin{code}
   toℕ : {xs : List Carrier} → Some₀ xs → ℕ
   toℕ (here _) = 0
   toℕ (there pf) = suc (toℕ pf)

   _∼S_ : {xs : List Carrier} → Some₀ xs → Some₀ xs → Set
   s₁ ∼S s₂ = toℕ s₁ ≡ toℕ s₂
\end{code}

Instead, we choose a more direct approach: |_≋_|.  This is an extremely strong relation:
two proofs, of different properties of elements of different lists are considered related
when the ``witness'' for the property is in the same location in both lists.

\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} {Q : A ⟶ SSetoid ℓa ℓa} where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   private Q₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ Q e)

   infix 3 _≋_
   data _≋_ : {xs ys : List Carrier} (pf : Some₀ P xs) (pf' : Some₀ Q ys) → Set ℓa where
     hereEq : {xs ys : List Carrier} {x y : Carrier} (px : P₀ x) (qy : Q₀ y)
            → _≋_ (here {x = x} {xs} px) (here {x = y} {ys} qy)
     thereEq : {xs ys : List Carrier} {x y : Carrier} {pxs : Some₀ P xs} {qys : Some₀ Q ys}
             → _≋_ pxs qys → _≋_ (there {x = x} pxs) (there {x = y} qys)
\end{code}             

Notice that these another from of ``natural numbers'' whose elements are of the form
|thereEqⁿ (hereEq Px Qx)| for some |n : ℕ|.

\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where
   open Setoid A

   ≋-refl : {xs : List Carrier} {p : Some₀ P xs} → p ≋ p
   ≋-refl {p = here px} = hereEq px px
   ≋-refl {p = there p} = thereEq ≋-refl

module _ {a ℓa} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} {Q : A ⟶ SSetoid ℓa ℓa} where
   open Setoid A

   ≋-sym : {xs : List Carrier} {p : Some₀ P xs} {q : Some₀ Q xs} → p ≋ q → q ≋ p
   ≋-sym (hereEq px py) = hereEq py px
   ≋-sym (thereEq eq) = thereEq (≋-sym eq)

module _ {a ℓa} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} {Q : A ⟶ SSetoid ℓa ℓa} {R : A ⟶ SSetoid ℓa ℓa} where
   open Setoid A

   ≋-trans : {xs : List Carrier} {p : Some₀ P xs} {q : Some₀ Q xs} {r : Some₀ R xs}
           → p ≋ q → q ≋ r → p ≋ r
   ≋-trans (hereEq px py) (hereEq .py pz) = hereEq px pz
   ≋-trans (thereEq e) (thereEq f) = thereEq (≋-trans e f)

module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid ℓa ℓa) where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   Some : List Carrier → Setoid (ℓa ⊔ a) ℓa
   Some xs = record
     { Carrier         =   Some₀ P xs
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

  _∈_ : Carrier → List Carrier → Setoid (a ⊔ ℓ) ℓ
  x ∈ xs = Some (setoid≈ x) xs

  _∈₀_ : Carrier → List Carrier → Set (ℓ ⊔ a)
  x ∈₀ xs = Setoid.Carrier (x ∈ xs)

  BagEq : (xs ys : List Carrier) → Set (ℓ ⊔ a)
  BagEq xs ys = {x : Carrier} → (x ∈ xs) ≅ (x ∈ ys)
\end{code}
%}}}

%{{{ \subsection{Parallel Composition} _∥_ ; [_∥_] ; ∥-sym ; _⊎⊎_
\subsection{Parallel Composition}

To avoid absurd patterns that we do not use, when using |_⊎-Rel_|, we make this:
As such, we introduce the parallel composition of heterogeneous relations.

\begin{code}
data _∥_ {a₁ b₁ c₁ a₂ b₂ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} (_~₁_ : A₁ → B₁ → Set c₁)
  {A₂ : Set a₂} {B₂ : Set b₂} (_~₂_ : A₂ → B₂ → Set c₂)
  : A₁ ⊎ A₂ → B₁ ⊎ B₂ → Set (a₁ ⊔ b₁ ⊔ c₁ ⊔ a₂ ⊔ b₂ ⊔ c₂) where
  left  : {x : A₁} {y : B₁} (x~₁y : x ~₁ y) → (_~₁_ ∥ _~₂_) (inj₁ x) (inj₁ y)
  right : {x : A₂} {y : B₂} (x~₂y : x ~₂ y) → (_~₁_ ∥ _~₂_) (inj₂ x) (inj₂ y)

-- Non-working ``eliminator'' for this type.
[_∥_] : {a₁ b₁ c₁ a₂ b₂ c₂ ℓ : Level}
        {A₁ : Set a₁} {B₁ : Set b₁} {_~₁_ : A₁ → B₁ → Set c₁}
        {A₂ : Set a₂} {B₂ : Set b₂} {_~₂_ : A₂ → B₂ → Set c₂}
     →
        {Z : {a : A₁ ⊎ A₂} {b : B₁ ⊎ B₂} → (_~₁_ ∥ _~₂_) a b → Set ℓ}
        (F : {a : A₁} {b : B₁} (a~b : a ~₁ b) → Z (left a~b))
        (G : {a : A₂} {b : B₂} (a~b : a ~₂ b) → Z (right a~b))
     →
        {x : A₁ ⊎ A₂} {y : B₁ ⊎ B₂}
     → (x∥y : (_~₁_ ∥ _~₂_) x y)  → Z x∥y
[ F ∥ G ] (left  x~y) = F x~y
[ F ∥ G ] (right x~y) = G x~y

-- If the argument relations are symmetric then so is their parallel composition.
∥-sym : {a a′ c c′ : Level} {A : Set a} {_~_ : A → A → Set c}
  {A′ : Set a′} {_~′_ : A′ → A′ → Set c′}
  (sym₁ : {x y : A} → x ~ y → y ~ x) (sym₂ : {x y : A′} → x ~′ y → y ~′ x)
  {x y : A ⊎ A′}
  →
    (_~_ ∥ _~′_) x y → (_~_ ∥ _~′_) y x
∥-sym sym₁ sym₂ (left x~y )  =  left  (sym₁ x~y)
∥-sym sym₁ sym₂ (right x~y)  =  right (sym₂ x~y)
--
-- ought to be just: |[ left ∘ sym₁ ∥ right ∘ sym₂ ]|
---
-- Instead, I can use, with much distasteful yellow,
-- |∥-sym sym₁ sym₂ = [ (λ pf → left (sym₁ pf)) ∥ (λ pf → right (sym₂ pf)) ] |

infix 999 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊔ i₂) (i₁ ⊔ i₂ ⊔ k₁ ⊔ k₂)
A ⊎⊎ B = record
  { Carrier = A₀ ⊎ B₀
  ; _≈_ = ≈₁ ∥ ≈₂
  ; isEquivalence = record
    { refl   =  λ{ {inj₁ x} → left refl₁ ; {inj₂ x} → right refl₂ }
    ; sym    =  λ{ (left eq) → left (sym₁ eq) ; (right eq) → right (sym₂ eq)}
                -- ought to be writable as [ left ∘ sym₁ ∥ right ∘ sym₂ ]
    ; trans  =  λ{  (left  eq) (left  eqq) → left  (trans₁ eq eqq)
                  ; (right eq) (right eqq) → right (trans₂ eq eqq)
                  }
    }
  }
  where
    open Setoid A renaming (Carrier to A₀ ; _≈_ to ≈₁ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁)
    open Setoid B renaming (Carrier to B₀ ; _≈_ to ≈₂ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂)
\end{code}
%}}}

%{{{ \subsection{|⊎⊎-comm|}
\subsection{|⊎⊎-comm|}
\begin{code}
⊎⊎-comm : {a b aℓ bℓ : Level} {A : Setoid a aℓ} {B : Setoid b bℓ} → A ⊎⊎ B  ≅  B ⊎⊎ A
⊎⊎-comm {A = A} {B} = record
  { to           =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥   }
  ; from         =  record { _⟨$⟩_ = swap₊ ; cong = swap-on-∥′ }
  ; inverse-of   =  record { left-inverse-of = swap²≈∥≈id ; right-inverse-of = swap²≈∥≈id′ }
  }
  where

    open Setoid A renaming (Carrier to A₀ ; _≈_ to ≈₁ ; refl to refl₁)
    open Setoid B renaming (Carrier to B₀ ; _≈_ to ≈₂ ; refl to refl₂)

    swap-on-∥ : {i j : A₀ ⊎ B₀} → (≈₁ ∥ ≈₂) i j → (≈₂ ∥ ≈₁) (swap₊ i) (swap₊ j)
    swap-on-∥ (left  x∼₁y)  =  right x∼₁y
    swap-on-∥ (right x∼₂y)  =  left  x∼₂y

    swap²≈∥≈id : (z : A₀ ⊎ B₀) → (≈₁ ∥ ≈₂) (swap₊ (swap₊ z)) z
    swap²≈∥≈id (inj₁ _)  =  left  refl₁
    swap²≈∥≈id (inj₂ _)  =  right refl₂

    {-
       Tried to obtain the following via |∥-sym| ...
    -}

    swap-on-∥′ : {i j : B₀ ⊎ A₀} → (≈₂ ∥ ≈₁) i j → (≈₁ ∥ ≈₂) (swap₊ i) (swap₊ j)
    swap-on-∥′ (left  x~y) = right x~y
    swap-on-∥′ (right x~y) = left  x~y

    swap²≈∥≈id′ : (z : B₀ ⊎ A₀) → (≈₂ ∥ ≈₁) (swap₊ (swap₊ z)) z
    swap²≈∥≈id′ (inj₁ _)  =  left  refl₂
    swap²≈∥≈id′ (inj₂ _)  =  right refl₁
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
      _∼_ = _∼S_ P
      _∽_ = _≋_ ; ∽-refl = ≋-refl {P = P}

      -- ``ealier''
      ⊎→ˡ : ∀ {ws zs} → Some₀ P ws → Some₀ P (ws ++ zs)
      ⊎→ˡ (here p) = here p
      ⊎→ˡ (there p) = there (⊎→ˡ p)
\end{code}

The following absurd patterns are what led me to make a new type for equalities.
\edcomm{``me''}{Commented out:
\begin{spec}
      yo : {xs : List Carrier} {x y : Some₀ P xs} → x ∼ y   →   ⊎→ˡ x ~ ⊎→ˡ y
      yo {x = here px} {here px₁} Relation.Binary.PropositionalEquality.refl = ≡.refl
      yo {x = here px} {there y} ()
      yo {x = there x₁} {here px} ()
      yo {x = there x₁} {there y} pf = ≡.cong suc (yo {!!})
\end{spec}
}%edcomm

\begin{code}
      yo : {xs : List Carrier} {x y : Some₀ P xs} → x ∽ y   →   ⊎→ˡ x  ∽  ⊎→ˡ y
      yo (hereEq px py) = hereEq px py
      yo (thereEq pf) = thereEq (yo pf)

      -- ``later''
      ⊎→ʳ : ∀ xs {ys} → Some₀ P ys → Some₀ P (xs ++ ys)
      ⊎→ʳ []       p = p
      ⊎→ʳ (x ∷ xs) p = there (⊎→ʳ xs p)

      oy : (xs : List Carrier) {x y : Some₀ P ys} → x ∽ y   →   ⊎→ʳ xs x  ∽  ⊎→ʳ xs y
      oy [] pf = pf
      oy (x ∷ xs) pf = thereEq (oy xs pf)

      -- |Some₀| is |++→⊎|-homomorphic, in the second argument.

      ⊎→++ : ∀ {zs ws} → (Some₀ P zs ⊎ Some₀ P ws) → Some₀ P (zs ++ ws)
      ⊎→++      (inj₁ x) = ⊎→ˡ x
      ⊎→++ {zs} (inj₂ y) = ⊎→ʳ zs y

      ++→⊎ : ∀ xs {ys} → Some₀ P (xs ++ ys) → Some₀ P xs ⊎ Some₀ P ys
      ++→⊎ []             p  = inj₂ p
      ++→⊎ (x ∷ l) (here  p) = inj₁ (here p)
      ++→⊎ (x ∷ l) (there p) = (there ⊎₁ id₀) (++→⊎ l p)

      -- all of the following may need to change

      ⊎→++-cong : {a b : Some₀ P xs ⊎ Some₀ P ys} → (_∽_ ∥ _∽_) a b → ⊎→++ a ∽ ⊎→++ b
      ⊎→++-cong (left  x₁∼x₂)  =  yo x₁∼x₂
      ⊎→++-cong (right y₁∼y₂)  =  oy xs y₁∼y₂

      ∽∥∽-cong   :  {xs ys us vs : List Carrier}
                    → (F : Some₀ P xs → Some₀ P us) (F-cong : {p q : Some₀ P xs} → p ∽ q → F p ∽ F q)
                    → (G : Some₀ P ys → Some₀ P vs) (G-cong : {p q : Some₀ P ys} → p ∽ q → G p ∽ G q)
                    → {pf pf' : Some₀ P xs ⊎ Some₀ P ys}
                    → (_∽_ ∥ _∽_) pf pf' → (_∽_ ∥ _∽_) ( (F ⊎₁ G) pf) ((F ⊎₁ G) pf')
      ∽∥∽-cong F F-cong G G-cong (left x~₁y) = left (F-cong x~₁y)
      ∽∥∽-cong F F-cong G G-cong (right x~₂y) = right (G-cong x~₂y)

      new-cong : (xs : List Carrier) {i j : Some₀ P (xs ++ ys)} → i ∽ j → (_∽_ ∥ _∽_) (++→⊎ xs i) (++→⊎ xs j)
      new-cong [] pf = right pf
      new-cong (x ∷ xs) (hereEq px py) = left (hereEq px py)
      new-cong (x ∷ xs) (thereEq pf) = ∽∥∽-cong there thereEq id₀ id₀ (new-cong xs pf)

      lefty : (xs {ys} : List Carrier) (p : Some₀ P xs ⊎ Some₀ P ys) → (_∽_ ∥ _∽_) (++→⊎ xs (⊎→++ p)) p
      lefty [] (inj₁ ())
      lefty [] (inj₂ p) = right ≋-refl
      lefty (x ∷ xs) (inj₁ (here px)) = left ∽-refl
      lefty (x ∷ xs) {ys} (inj₁ (there p)) with ++→⊎ xs {ys} (⊎→++ (inj₁ p)) | lefty xs {ys} (inj₁ p)
      ... | inj₁ _ | (left x~₁y) = left (thereEq x~₁y)
      ... | inj₂ _ | ()
      lefty (z ∷ zs) {ws} (inj₂ p) with ++→⊎ zs {ws} (⊎→++ {zs} (inj₂ p)) | lefty zs (inj₂ p)
      ... | inj₁ x | ()
      ... | inj₂ y | (right x~₂y) = right x~₂y

      righty : (zs {ws} : List Carrier) (p : Some₀ P (zs ++ ws)) → (⊎→++ (++→⊎ zs p)) ∽ p
      righty [] {ws} p = ∽-refl
      righty (x ∷ zs) {ws} (here px) = ∽-refl
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
map≅ {A = A} {B} {P} {f} = record
  { to = record { _⟨$⟩_ = map⁺ ; cong = map⁺-cong }
  ; from = record { _⟨$⟩_ = map⁻ ; cong = map⁻-cong }
  ; inverse-of = record { left-inverse-of = map⁻∘map⁺ ; right-inverse-of = map⁺∘map⁻ }
  }
  where
  g = _⟨$⟩_ f
  A₀ = Setoid.Carrier A
  _∼_ = _≋_ {P = P}

  map⁺ : {xs : List A₀} → Some₀ (P ∘ f) xs → Some₀ P (map g xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : {xs : List A₀} → Some₀ P (map g xs) → Some₀ (P ∘ f) xs
  map⁻ {[]} ()
  map⁻ {x ∷ xs} (here p) = here p
  map⁻ {x ∷ xs} (there p) = there (map⁻ {xs = xs} p)

  map⁺∘map⁻ : {xs : List A₀ } → (p : Some₀ P (map g xs)) → map⁺ (map⁻ p) ∼ p
  map⁺∘map⁻ {[]} ()
  map⁺∘map⁻ {x ∷ xs} (here p) = hereEq p p
  map⁺∘map⁻ {x ∷ xs} (there p) = thereEq (map⁺∘map⁻ p)

  map⁻∘map⁺ : {xs : List A₀} → (p : Some₀ (P ∘ f) xs)
            → let _∼₂_ = _≋_ {P = P ∘ f} in map⁻ (map⁺ p) ∼₂ p
  map⁻∘map⁺ {[]} ()
  map⁻∘map⁺ {x ∷ xs} (here p) = hereEq p p
  map⁻∘map⁺ {x ∷ xs} (there p) = thereEq (map⁻∘map⁺ p)

  map⁺-cong : {ys : List A₀} {i j : Some₀ (P ∘ f) ys} →  _≋_ {P = P ∘ f} i j → map⁺ i ∼ map⁺ j
  map⁺-cong (hereEq px py) = hereEq px py
  map⁺-cong (thereEq i∼j) = thereEq (map⁺-cong i∼j)

  map⁻-cong : {ys : List A₀} {i j : Some₀ P (map g ys)} → i ∼ j → _≋_ {P = P ∘ f} (map⁻ i) (map⁻ j)
  map⁻-cong {[]} ()
  map⁻-cong {x ∷ ys} (hereEq px py) = hereEq px py
  map⁻-cong {x ∷ ys} (thereEq i∼j) = thereEq (map⁻-cong i∼j)
\end{code}
%}}}

\begin{code}
module FindLose {a ℓa : Level} {A : Setoid a ℓa}  (P : A ⟶ SSetoid ℓa ℓa) where
 open Membership A
 open Setoid A
 open Π
 open _≅_
 private
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y

 find : {ys : List Carrier} → Some₀ P ys → Support ys
 find {y ∷ ys} (here p) = y , here refl , p
 find {y ∷ ys} (there p) =  let (a , a∈ys , Pa) = find p
                            in a , there a∈ys , Pa

 lose : {ys : List Carrier} → Support ys → Some₀ P ys
 lose (y , here py , Py)     = here (_≅_.to (Π.cong P py) Π.⟨$⟩ Py)
 lose (y , there y∈ys , Py) = there (lose (y , y∈ys , Py))

 -- ``If an element of ys has a property P, then some element of ys has property P''
 -- cf |copy| below
 Some-Intro : {y : Carrier} {ys : List Carrier}
      → y ∈₀ ys → P₀ y → Some₀ P ys
 Some-Intro {y} y∈ys Qy = lose (y , y∈ys , Qy)

 bag-as-⇒ : {xs ys : List Carrier} → BagEq xs ys → Some₀ P xs → Some₀ P ys
 bag-as-⇒ xs≅ys Pxs = let (x , x∈xs , Px) = find Pxs in
                       let x∈ys = to xs≅ys ⟨$⟩ x∈xs
                       in lose (x , x∈ys , Px)


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

 find-cong : {ys : List Carrier} {p : Some₀ P ys} {q : Some₀ Q ys} → p ≋ q → find P p ∻ find Q q
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


 cong-fwd : {xs ys : List Carrier} {xs≅ys : BagEq xs ys} {p : Some₀ P xs} {q : Some₀ Q xs}
          → p ≋ q → bag-as-⇒ P xs≅ys p ≋ bag-as-⇒ Q xs≅ys q
 cong-fwd {xs} {ys} {xs≅ys} {p} {q} p≋q with find P p | find Q q | find-cong p≋q
 ...| (x , x∈xs , px) | (y , y∈xs , py) | (x≈y , x∈xs≋y∈xs) = lose-cong (x≈y , goal)
 
   where
   
     open _≅_ (xs≅ys {x}) using () renaming (to to F)
     open _≅_ (xs≅ys {y}) using () renaming (to to G)
     
     F-cong : {a b : x ∈₀ xs} → a ≋ b → F ⟨$⟩ a ≋ F ⟨$⟩ b
     F-cong = Π.cong F
     
     G-cong : {a b : y ∈₀ xs} → a ≋ b → G ⟨$⟩ a ≋ G ⟨$⟩ b
     G-cong = Π.cong G

     To = λ {i} → Π._⟨$⟩_ (_≅_.to (xs≅ys {i}))

     postulate helper : {i j : Carrier} → i ≈ j → {!To {i} ≐ To {j}!}
     -- switch to john major equality in the defn of ≐ ?
     goal : F ⟨$⟩ x∈xs ≋ G ⟨$⟩ y∈xs
     goal = {!Π.cong F!}
     
     y∈ysT : y ∈₀ xs
     y∈ysT = y∈xs
\end{code}

\edcomm{Somebody}{Commented out:
\begin{spec}
 bag-as-⇒ : {xs ys : List Carrier} → BagEq xs ys → Some₀ P xs → Some₀ P ys
 bag-as-⇒ xs≅ys Pxs = let (x , x∈xs , Px) = find Pxs in
                       let x∈ys = to xs≅ys ⟨$⟩ x∈xs
                       in lose (x , x∈ys , Px)
\end{spec}
}%edcomm

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

 _∻_ : {ys : List Carrier} → Support ys → Support ys → Set ℓa
 (a , a∈xs , Pa) ∻ (b , b∈xs , Pb) =  a ≈ b  ×  a∈xs ≋ b∈xs

 Σ-Setoid : (ys : List Carrier) → Setoid (ℓa ⊔ a) ℓa
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
     Sym (a≈b , a∈xs≋b∈xs) = sym a≈b , ≋-sym a∈xs≋b∈xs

     Trans : Transitive _∻_
     Trans (a≈b , a∈xs≋b∈xs) (b≈c , b∈xs≋c∈xs) = trans a≈b b≈c , ≋-trans a∈xs≋b∈xs b∈xs≋c∈xs

 module ∻ {ys} where open Setoid (Σ-Setoid ys) public

 open FindLose P
 open FindLoseCong hiding (_∻_)

 left-inv : {ys : List Carrier} (x∈ys : Some₀ P ys) → lose (find x∈ys) ≋ x∈ys
 left-inv (here px) = hereEq _ px
 left-inv (there x∈ys) = thereEq (left-inv x∈ys)

 right-inv : {ys : List Carrier} (pf : Σ y ∶ Carrier • y ∈₀ ys × P₀ y) → find (lose pf) ∻ pf
 right-inv (y , here px , Py) = (sym px) , (hereEq refl px)
 right-inv (y , there y∈ys , Py) = (proj₁ (right-inv (y , y∈ys , Py))) , (thereEq (proj₂ (right-inv (y , y∈ys , Py))))

 Σ-Some : (xs : List Carrier) → Some P xs ≅ Σ-Setoid xs
 Σ-Some xs = record
   { to = record { _⟨$⟩_ = find {xs} ; cong = find-cong }
   ; from = record { _⟨$⟩_ = lose ; cong = lose-cong }
   ; inverse-of = record
     { left-inverse-of = left-inv
     ; right-inverse-of = right-inv
     }
   }
\end{code}

\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where

 open Membership A
 open Setoid A
 private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

 Some-cong : {xs₁ xs₂ : List Carrier} →
           (∀ {x} → (x ∈ xs₁) ≅ (x ∈ xs₂)) →
           Some P xs₁ ≅ Some P xs₂
 Some-cong {xs₁} {xs₂} list-rel = record
  { to           =   record { _⟨$⟩_ = bag-as-⇒ list-rel ; cong = FindLoseCong.cong-fwd {P = P} {Q = P} } -- Yellow! \unfinished
  ; from         =   record { _⟨$⟩_ = xs₁→xs₂ (≅-sym list-rel) ; cong = {! {- \unfinished -}!} }
  ; inverse-of   =   record { left-inverse-of = {! {- \unfinished -}!} ; right-inverse-of = {! {- \unfinished -}!} }
  }
  where

  open FindLose P using (bag-as-⇒ ; find)

  -- this is probably a specialized version of Respects.
  -- is also related to an uncurried version of 'lose'.
  copy : ∀ {x} {ys} {Q : A ⟶ SSetoid ℓa ℓa} → x ∈₀ ys → (Setoid.Carrier (Π._⟨$⟩_ Q x)) → Some₀ Q ys
  copy {Q = Q} (here p)  pf = here (_≅_.to (Π.cong Q p) ⟨$⟩ pf)
  copy         (there p) pf = there (copy p pf)

  -- this should be generalized to qy coming from Q₀ x.
  copy-cong : {x y : Carrier} {xs ys : List Carrier} {Q : A ⟶ SSetoid ℓa ℓa}
    (px : P₀ x) (qy : Setoid.Carrier (Π._⟨$⟩_ Q y)) (x∈xs : x ∈₀ xs) (y∈ys : y ∈₀ ys) →
    (x∈xs ≋ y∈ys) → copy {Q = P} x∈xs px ≋ copy {Q = Q} y∈ys qy
  copy-cong px qy₁ (here px₁) .(here qy) (hereEq .px₁ qy) = hereEq _ _
  copy-cong px qy (there i) .(there _) (thereEq i≋j) = thereEq (copy-cong px qy _ _ i≋j)

  xs₁→xs₂ : ∀ {xs ys} →  (∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → Some₀ P xs → Some₀ P ys
  xs₁→xs₂ {xs} rel p =
    let pos = find {ys = xs} p in
    copy (_≅_.to rel ⟨$⟩ proj₁ (proj₂ pos)) (proj₂ (proj₂ pos))

  cong-fwd : {i j : Some₀ P xs₁} →
    i ≋ j → xs₁→xs₂ list-rel i ≋ xs₁→xs₂ list-rel j
  cong-fwd {i} {j} i≋j = copy-cong _ _ _ _ {! {- \unfinished -}!}

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
