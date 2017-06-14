\section{Some}

%{{{ Imports
\begin{code}
module Some where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary using (Setoid ; IsEquivalence ; Rel)

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

%{{{ Some₀
\subsection{|Some₀|}
Setoid based variant of Any.

Quite a bit of this is directly inspired by |Data.List.Any| and |Data.List.Any.Properties|.

\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid ℓa ℓa) where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   data Some₀  : List Carrier → Set (a ⊔ ℓa) where
     here  : {x : Carrier} {xs : List Carrier} (px  : P₀ x    ) → Some₀ (x ∷ xs)
     there : {x : Carrier} {xs : List Carrier} (pxs : Some₀ xs) → Some₀ (x ∷ xs)
\end{code}

Inhabitants of Some₀ really are just locations: |Some₀ P xs  ≅ Σ i ∶ Fin (length xs) • P (x ‼ i)|.
For now, we use a weaker operation.
\begin{code}   
   toℕ : {xs : List Carrier} → Some₀ xs → ℕ
   toℕ (here _) = 0
   toℕ (there pf) = suc (toℕ pf)
   
   -- proof irrelevance built-in here.  We only care that these are the same as members of |ℕ|
   _∼S_ : {xs : List Carrier} → Some₀ xs → Some₀ xs → Set
   s₁ ∼S s₂ = toℕ s₁ ≡ toℕ s₂

   -- A more direct approach: |_≋_|

module _ {a ℓa} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} {Q : A ⟶ SSetoid ℓa ℓa} where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)
   private Q₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ Q e)

   infix 3 _≋_
   data _≋_ : {xs ys : List Carrier} (pf : Some₀ P xs) (pf' : Some₀ Q ys) → Set where
     hereEq : {xs ys : List Carrier} {x y : Carrier} (px : P₀ x) (qy : Q₀ y)
            → _≋_ (here {x = x} {xs} px) (here {x = y} {ys} qy)
     thereEq : {xs ys : List Carrier} {x y : Carrier} {pxs : Some₀ P xs} {qys : Some₀ Q ys}
             → _≋_ pxs qys → _≋_ (there {x = x} pxs) (there {x = y} qys)

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
   
   Some : List Carrier → Setoid (ℓa ⊔ a) lzero
   Some xs = record
     { Carrier         =   Some₀ P xs
     ; _≈_             =   _≋_
     ; isEquivalence   = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
     -- |record {IsEquivalence ≡.isEquivalence}|
     }

≡→Some : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa}
         {xs ys : List (Setoid.Carrier A)} → xs ≡ ys → Some P xs ≅ Some P ys
≡→Some {A = A} ≡.refl = ≅-refl
\end{code}

%}}}

%{{{ Membership module : setoid≈ ; _∈_ ; _∈₀_
\subsection{Membership module}
\begin{code}
module Membership {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (trans to _⟨≈≈⟩_)

  infix 4 _∈₀_ _∈_

  setoid≈ : Carrier → S ⟶ SSetoid ℓ ℓ
  setoid≈ x = record
    { _⟨$⟩_ = λ y → _≈S_ {A = S} x y
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈≈⟩ i≈j     ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈j → x≈j ⟨≈≈⟩ sym i≈j ; cong = λ _ → tt }
      ; inverse-of = record
        { left-inverse-of = λ _ → tt
        ; right-inverse-of = λ _ → tt
        }
      }
    }

  _∈_ : Carrier → List Carrier → Setoid (a ⊔ ℓ) lzero
  x ∈ xs = Some (setoid≈ x) xs

  _∈₀_ : Carrier → List Carrier → Set (ℓ ⊔ a)
  x ∈₀ xs = Setoid.Carrier (x ∈ xs)
\end{code}
%}}}

%{{{ _∥_ ; [_∥_] ; ∥-sym ; _⊎⊎_
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

%{{{ ⊎⊎-comm
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

%{{{ ++≅ : ⋯ → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
\subsection{|++≅ : ⋯ → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)|}
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where
  ++≅ : {xs ys : List (Setoid.Carrier A) } → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
  ++≅ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong =  ⊎→++-cong  }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = new-cong xs } -- |{! ++→⊎-cong xs {ys} !} }|
    ; inverse-of = record
      { left-inverse-of = lefty xs -- |{! ++→⊎∘⊎→++≅id xs !}|
      ; right-inverse-of = righty xs -- |{! ⊎→++∘++→⊎≅id xs !}|
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
\begin{spec}
      yo : {xs : List Carrier} {x y : Some₀ P xs} → x ∼ y   →   ⊎→ˡ x ~ ⊎→ˡ y
      yo {x = here px} {here px₁} Relation.Binary.PropositionalEquality.refl = ≡.refl
      yo {x = here px} {there y} ()
      yo {x = there x₁} {here px} ()
      yo {x = there x₁} {there y} pf = ≡.cong suc (yo {!!})
\end{spec}

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
      ++→⊎ [] p = inj₂ p
      ++→⊎ (x ∷ l) (here p) = inj₁ (here p)
      ++→⊎ (x ∷ l) (there p) = (there ⊎₁ id₀) (++→⊎ l p)

      -- all of the following may need to change

      ⊎→++-cong : {a b : Some₀ P xs ⊎ Some₀ P ys} → (_∽_ ∥ _∽_) a b → ⊎→++ a ∽ ⊎→++ b
      ⊎→++-cong (left  x₁∼x₂)  =  yo x₁∼x₂
      ⊎→++-cong (right y₁∼y₂)  =  oy xs y₁∼y₂

      ++→⊎-cong : ∀ ws {zs} {a b : Some₀ P (ws ++ zs)} → a ≡ b → (_≡_ ∥ _≡_) (++→⊎ ws a) (++→⊎ ws b)
      ++→⊎-cong [] ≡.refl = right ≡.refl
      ++→⊎-cong (x ∷ xs) {a = here px} ≡.refl = left ≡.refl
      ++→⊎-cong (x ∷ xs) {a = there pxs} ≡.refl with ++→⊎ xs pxs | ++→⊎-cong xs {a = pxs} ≡.refl
      ...| inj₁ _ | left  ≡.refl  =  left  ≡.refl
      ...| inj₂ _ | right ≡.refl  =  right ≡.refl

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

      ++→⊎∘⊎→++≅id : ∀ zs {ws} → (pf : Some₀ P zs ⊎ Some₀ P ws) → (_≡_ ∥ _≡_) (++→⊎ zs (⊎→++ pf)) pf
      ++→⊎∘⊎→++≅id [] (inj₁ ())
      ++→⊎∘⊎→++≅id [] (inj₂ _) = right ≡.refl
      ++→⊎∘⊎→++≅id (z ∷ zs)      (inj₁ (here p)) = left ≡.refl
      ++→⊎∘⊎→++≅id (z ∷ zs) {ws} (inj₁ (there p)) with ++→⊎ zs {ws} (⊎→++ (inj₁ p)) | ++→⊎∘⊎→++≅id zs {ws} (inj₁ p)
      ... | inj₁ pp | left pp≡p = left (≡.cong there pp≡p)
      ++→⊎∘⊎→++≅id (z ∷ zs) {ws} (inj₂ p) with ++→⊎ zs {ws} (⊎→++ {zs} (inj₂ p)) | ++→⊎∘⊎→++≅id zs (inj₂ p)
      ... | inj₂ pp | right pp≡p = right pp≡p

      
      righty : (zs {ws} : List Carrier) (p : Some₀ P (zs ++ ws)) → (⊎→++ (++→⊎ zs p)) ∽ p
      righty [] {ws} p = ∽-refl
      righty (x ∷ zs) {ws} (here px) = ∽-refl
      righty (x ∷ zs) {ws} (there p) with ++→⊎ zs p | righty zs p
      ... | inj₁ _  | res = thereEq res
      ... | inj₂ _  | res = thereEq res

      ⊎→++∘++→⊎≅id : ∀ zs {ws} → (x : Some₀ P (zs ++ ws)) → ⊎→++ {zs} {ws} (++→⊎ zs x) ≡ x
      ⊎→++∘++→⊎≅id []       x = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (here p) = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (there p) with ++→⊎ zs p | ⊎→++∘++→⊎≅id zs p
      ... | inj₁ y | ≡.refl = ≡.refl
      ... | inj₂ y | ≡.refl = ≡.refl
\end{code}
%}}}

%{{{ ⊥⊥ : bottom as a setoid ; ⊥≅Some[] : ⊥⊥ ≅ Some P []
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

%{{{ map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)
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

%{{{ Some-cong : (∀ {x} → x ∈ xs₁ ≅ x ∈ xs₂) → Some P xs₁ ≅ Some P xs₂
\subsection{Some-cong and holes}
This isn't quite the full-powered cong, but is all we need.
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} {xs : List (Setoid.Carrier A)} where
 open Membership A
 open Setoid A
 private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

 record UnpackedSome : Set (ℓa ⊔ a) where
   constructor US
   field
     pt : Carrier
     belongs : pt ∈₀ xs
     prop : P₀ pt

 record _≈US_ (a b : UnpackedSome) : Set {!!} where
   constructor us-eq
   open UnpackedSome
   _∼_ = _≋_ {P = P}
   field
     ptEq : pt a ≈ pt b
     -- ∈Eq : belongs a ∼ belongs b

 Support = λ ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y

 _∻_ : {ys : List Carrier} → Support ys → Support ys → Set ℓa
 (a , a∈xs , Pa) ∻ (b , b∈xs , Pb) =  a ≈ b  ×  a∈xs ≋ b∈xs

 Σ-Setoid : (ys : List Carrier) → Setoid (ℓa ⊔ a) ℓa
 Σ-Setoid ys = record
   { Carrier = Support xs
   ; _≈_ = _∻_
   ; isEquivalence = record
     { refl = λ {s} → Refl {s}
     ; sym = λ {s} {t} eq → Sym {s} {t} eq
     ; trans = λ {s} {t} {u} a b → Trans {s} {t} {u} a b
     }
   }
   where

     Eq = _∻_

     Refl : {s : Support xs} → Eq s s
     Refl {a , a∈xs , Pa} = refl , ≋-refl

     Sym  : {s t : Support xs} → Eq s t → Eq t s
     Sym (a≈b , a∈xs≋b∈xs) = sym a≈b , ≋-sym a∈xs≋b∈xs

     Trans : {s t u : Support xs} → Eq s t → Eq t u → Eq s u
     Trans (a≈b , a∈xs≋b∈xs) (b≈c , b∈xs≋c∈xs) = trans a≈b b≈c , ≋-trans a∈xs≋b∈xs b∈xs≋c∈xs

 module ∻ {ys} where open Setoid (Σ-Setoid ys) public

 find : {ys : List Carrier} → Some₀ P ys → Σ y ∶ Carrier • y ∈₀ ys × P₀ y
 find {y ∷ ys} (here p) = y , here refl , p
 find {y ∷ ys} (there p) =  let (a , a∈ys , Pa) = find p
                            in a , there a∈ys , Pa
                            
 lose : {ys : List Carrier} → Σ y ∶ Carrier • y ∈₀ ys × P₀ y → Some₀ P ys
 lose (y , here py , Py)     = here (_≅_.to (Π.cong P py) Π.⟨$⟩ Py)
 lose (y , there y∈ys , Py) = there (lose (y , y∈ys , Py))

 rright-inv : {ys : List Carrier} (p : Σ y ∶ Carrier • y ∈₀ ys × P₀ y) → find (lose p) ∻ p
 rright-inv (y , here y≈x , Py) = sym y≈x , hereEq refl y≈x
 rright-inv (y , there y∈ys , Py) = ?

 find-cong : {ys : List Carrier} {p q : Some₀ P ys} → p ≋ q → find p ∻ find q
 find-cong (hereEq px qy) = refl , ≋-refl
 find-cong (thereEq eq) = let (fst , snd) = find-cong eq in fst , thereEq snd

 P⁺ : {x y : Carrier} → x ≈ y → P₀ x → P₀ y
 P⁺ x≈y = Π._⟨$⟩_ (_≅_.to (Π.cong P x≈y))

 postulate P⁺refl≈Id : {x : Carrier} → P⁺ (refl {x = x}) ≐ id₀

 llose-cong : {ys : List Carrier} {p q : Support ys} → p ∻ q → lose p ≋ lose q
 llose-cong {p = a , here a≈x , Pa} {b , here b≈x , Pb} (fst , hereEq .a≈x .b≈x) = hereEq (P⁺ a≈x Pa) (P⁺ b≈x Pb)
 llose-cong {p = a , here a≈x , Pa} {b , there b∈ys , Pb} (fst , ())
 llose-cong {p = a , there a∈ys , Pa} {b , here px , Pb} (fst , ())
 llose-cong {p = a , there a∈ys , Pa} {b , there b∈ys , Pb} (a≈b , thereEq a∈ys≋b∈ys) = thereEq (llose-cong (a≈b , a∈ys≋b∈ys))

 lleft-inv : (x : Some₀ P xs) → lose (find x) ≋ x
 lleft-inv (here px) rewrite P⁺refl≈Id px = ≋-refl
 lleft-inv (there pxs) with find pxs
 lleft-inv (there pxs) | y , here px , Py = thereEq {!!}
 lleft-inv (there pxs) | y , there proj₄ , Py = thereEq {!lleft-inv ?!}

 Σ-Some : Some P xs ≅ Σ-Setoid xs
 Σ-Some = record
   { to = record { _⟨$⟩_ = find {xs} ; cong = find-cong }
   ; from = record { _⟨$⟩_ = lose ; cong = llose-cong }
   ; inverse-of = record
     { left-inverse-of = lleft-inv
     ; right-inverse-of = rright-inv
     }
   }
   where
   _∼_ = _∼S_ P
   lose-cong : ∀ {ys : List Carrier} {a b : Σ Carrier (λ x → x ∈₀ ys × P₀ x)} → let i = proj₁ a in let j = proj₁ b in
       let i∈ys = proj₁ (proj₂ a) in let j∈ys = proj₁ (proj₂ b) in
       i ≈ j × toℕ (setoid≈ i) i∈ys ≡ toℕ (setoid≈ j) j∈ys × ((Π._⟨$⟩_ P i) ≅ (Π._⟨$⟩_ P j)) → lose {ys} a ∼ lose b
   lose-cong {_} {a₁ , here {x} px , Pa} {b , here px₁ , Pb} (i≈j , _ , Pi≅Pj) = ≡.refl
   lose-cong {_} {a₁ , here px , Pa} {b , there b∈xs , Pb} (i≈j , () , Pi≅Pj)
   lose-cong {_} {a₁ , there a∈xs , Pa} {b , here px , Pb} (i≈j , () , Pi≅Pj)
   lose-cong {_} {a₁ , there a∈xs , Pa} {b , there b∈xs , Pb} (i≈j , xx , Pi≅Pj) =
     ≡.cong suc (lose-cong {a = a₁ , a∈xs , Pa} {b , b∈xs , Pb} (i≈j , suc-inj xx , Pi≅Pj))

   left-inv : ∀ {ys} (x : Some₀ P ys) → toℕ P (lose (find x)) ≡ toℕ P x
   left-inv (here px) = ≡.refl
   left-inv (there x₁) = ≡.cong suc (left-inv x₁)
\end{code}

\begin{spec}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid ℓa ℓa} where

 open Membership A
 open Setoid A
 private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

 Some-cong : {xs₁ xs₂ : List Carrier} →
           (∀ {x} → (x ∈ xs₁) ≅ (x ∈ xs₂)) →
           Some P xs₁ ≅ Some P xs₂ 
 Some-cong {xs₁} {xs₂} list-rel = record
  { to           =   record { _⟨$⟩_ = xs₁→xs₂ list-rel ; cong = {!!} }
  ; from         =   record { _⟨$⟩_ = xs₁→xs₂ (≅-sym list-rel) ; cong = {!!} }
  ; inverse-of   =   record { left-inverse-of = left-inv list-rel ; right-inverse-of = {!!} }
  }
  where
    
  copy : ∀ {x} {ys} → x ∈₀ ys → P₀ x → Some₀ P ys
  copy (here p) pf = here (_≅_.to (Π.cong P p) ⟨$⟩ pf)
  copy (there p) pf = there (copy p pf)
  
  xs₁→xs₂ : ∀ {xs ys} →  (∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → Some₀ P xs → Some₀ P ys
  xs₁→xs₂ {[]} _ ()
  xs₁→xs₂ {x ∷ xs}      rel (here p) = copy (_≅_.to rel ⟨$⟩ here (Setoid.refl A)) p
  xs₁→xs₂ {x ∷ xs} {ys} rel (there p) = 
    let pos = find p in copy (_≅_.to rel ⟨$⟩ there (proj₁ (proj₂ pos))) (proj₂ (proj₂ pos))
    
  left-inv : ∀ {xs ys} → (rel : ∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → (∀ y → xs₁→xs₂ (≅-sym rel) (xs₁→xs₂ rel y) ≡ y)
  left-inv {[]} rel ()
  left-inv {x ∷ xs} rel (here p) with _≅_.to rel ⟨$⟩ here refl | inspect (_⟨$⟩_ (_≅_.to rel)) (here refl)
  ... | here pp | [ eq ] = {!!}
  ... | there qq | [ eq ] = {!!}
  left-inv {x ∷ xs} rel (there p) = {!!}
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
