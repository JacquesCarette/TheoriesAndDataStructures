\module{Some}

%{{{ Imports
\begin{code}
module Some where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary using (Setoid)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_; _⟨$⟩_)
open import Function          using (_$_) renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; map)
open import Data.Product using (∃)

open import EqualityCombinators
open import DataProperties
open import SetoidEquiv

open import TypeEquiv using (swap₊)
open import SetoidSetoid
open import Relation.Binary.Sum -- using (_⊎-setoid_)
\end{code}
%}}}

%{{{ Some₀
Setoid based variant of Any.
The definition is 'wrong' in the sense the target of P
really should be a 'Setoid of types',
and not one necessarily with |_≡_| as its equivalence.
We really need an 'interpretable setoid',
i.e., one which has |⟦_⟧ : Carrier → Set p|
\edcomm{WK}{also known as ``universe''},
as I don't know how to otherwise say that the target |Setoid|
must have a type as a Carrier.

Quite a bit of this is directly inspired
by |Data.List.Any| and |Data.List.Any.Properties|.

\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid ℓa ℓa) where
   open Setoid A
   private P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   data Some₀  : List Carrier → Set (a ⊔ ℓa) where
     here  : {x : Carrier} {xs : List Carrier} (px  : P₀ x    ) → Some₀ (x ∷ xs)
     there : {x : Carrier} {xs : List Carrier} (pxs : Some₀ xs) → Some₀ (x ∷ xs)

   _≈E_ : (x y : Carrier) → Setoid ℓa ℓa
   _≈E_ x y = record
     { Carrier         =   x ≈ y
     ; _≈_             =   λ _ _ → ⊤
     ; isEquivalence   =   record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
     }

   Some : List Carrier → Setoid (a ⊔ ℓa) (a ⊔ ℓa)
   Some xs = record
     { Carrier         =   Some₀ xs
     ; _≈_             =   _≡_ -- TODO, this is what needs changed next to fill
     ; isEquivalence   =   ≡.isEquivalence
     }

≡→Some : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid {!!} {!!}}
         {xs ys : List (Setoid.Carrier A)} → xs ≡ ys → Some P xs ≅ Some P ys
≡→Some {A = A} ≡.refl = ≅-refl
\end{code}
%}}}

%{{{ Membership module : setoid≈ ; _∈_ ; _∈₀_
\begin{code}
module Membership {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (trans to _⟨≈≈⟩_)

  infix 4 _∈₀_ _∈_

  setoid≈ : Carrier → S ⟶ SSetoid ℓ ℓ
  setoid≈ x = record
    { _⟨$⟩_ = λ y → _≈S_ {A = S} x y   -- This is an ``evil'' which will be amended in time.
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈≈⟩ i≈j     ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈j → x≈j ⟨≈≈⟩ sym i≈j ; cong = λ _ → tt }
      ; inverse-of = record
        { left-inverse-of = λ _ → tt
        ; right-inverse-of = λ _ → tt
        }
      }
    }

  _∈₀_ : Carrier → List Carrier → Set (ℓ ⊔ a)
  x ∈₀ xs = Some₀ (setoid≈ x) xs

  _∈_ : Carrier → List Carrier → Setoid (a ⊔ ℓ) (a ⊔ ℓ)
  x ∈ xs = Some (setoid≈ x) xs

\end{code}
%}}}

%{{{ _∥_ ; [_∥_] ; ∥-sym ; _⊎⊎_
\begin{code}
open import Relation.Binary using (Rel)

-- To avoid absurd patterns that we do not use, when using |_⊎-Rel_|, we make this:
-- As such, we introduce the parallel composition of heterogeneous relations.
-- This may be better named |_⊎̇_|?
data _∥_ {a₁ b₁ c₁ a₂ b₂ c₂ : Level}
  {A₁ : Set a₁} {B₁ : Set b₁} (_~₁_ : A₁ → B₁ → Set c₁)
  {A₂ : Set a₂} {B₂ : Set b₂} (_~₂_ : A₂ → B₂ → Set c₂)
  : A₁ ⊎ A₂ → B₁ ⊎ B₂ → Set (a₁ ⊔ b₁ ⊔ c₁ ⊔ a₂ ⊔ b₂ ⊔ c₂) where
  left  : {x : A₁} {y : B₁} (x~₁y : x ~₁ y) → (_~₁_ ∥ _~₂_) (inj₁ x) (inj₁ y)
  right : {x : A₂} {y : B₂} (x~₂y : x ~₂ y) → (_~₁_ ∥ _~₂_) (inj₂ x) (inj₂ y)

-- Before we move on, let us mention the eliminator for this type.
[_∥_] : {a₁ b₁ c₁ a₂ b₂ c₂ ℓ : Level}
        {A₁ : Set a₁} {B₁ : Set b₁} {_~₁_ : A₁ → B₁ → Set c₁}
        {A₂ : Set a₂} {B₂ : Set b₂} {_~₂_ : A₂ → B₂ → Set c₂}
     →
        {Z : Set ℓ}
        (F : {a : A₁} {b : B₁} → a ~₁ b → Z)
        (G : {a : A₂} {b : B₂} → a ~₂ b → Z)
     →
        {x : A₁ ⊎ A₂} {y : B₁ ⊎ B₂}
     → (_~₁_ ∥ _~₂_) x y  → Z
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
-- ought to be just: [ left ∘ sym₁ ∥ right ∘ sym₂ ]
---

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
       Tried to obtain the following via ∥-sym| ...
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
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid {!!} {!!}} where
  ++≅ : {xs ys : List (Setoid.Carrier A) } → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
  ++≅ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong = ⊎→++-cong }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = ++→⊎-cong xs }
    ; inverse-of = record
      { left-inverse-of = ++→⊎∘⊎→++≅id xs
      ; right-inverse-of = ⊎→++∘++→⊎≅id xs
      }
    }
    where

      -- ``ealier''
      ⊎→ˡ : ∀ {ws zs} → Some₀ P ws → Some₀ P (ws ++ zs)
      ⊎→ˡ (here p) = here p
      ⊎→ˡ (there p) = there (⊎→ˡ p)

      -- ``later''
      ⊎→ʳ : ∀ xs {ys} → Some₀ P ys → Some₀ P (xs ++ ys)
      ⊎→ʳ []        p = p
      ⊎→ʳ (x ∷ xs₁) p = there (⊎→ʳ xs₁ p)
      
      ⊎→++ : ∀ {zs ws} → (Some₀ P zs ⊎ Some₀ P ws) → Some₀ P (zs ++ ws)
      ⊎→++      (inj₁ x) = ⊎→ˡ x
      ⊎→++ {zs} (inj₂ y) = ⊎→ʳ zs y
      
      ++→⊎ : ∀ xs {ys} → Some₀ P (xs ++ ys) → Some₀ P xs ⊎ Some₀ P ys
      ++→⊎ [] p = inj₂ p
      ++→⊎ (x ∷ l) (here p) = inj₁ (here p)
      ++→⊎ (x ∷ l) (there p) = (there ⊎₁ id₀) (++→⊎ l p)

      -- all of the following may need to change

      ⊎→++-cong : {a b : Some₀ P xs ⊎ Some₀ P ys} → (_≡_ ∥ _≡_) a b → ⊎→++ a ≡ ⊎→++ b
      ⊎→++-cong (left  ≡.refl)  =  ≡.refl
      ⊎→++-cong (right ≡.refl)  =  ≡.refl

      ++→⊎-cong : ∀ ws {zs} {a b : Some₀ P (ws ++ zs)} → a ≡ b → (_≡_ ∥ _≡_) (++→⊎ ws a) (++→⊎ ws b)
      ++→⊎-cong [] ≡.refl = right ≡.refl
      ++→⊎-cong (x ∷ xs) {a = here px} ≡.refl = left ≡.refl
      ++→⊎-cong (x ∷ xs) {a = there pxs} ≡.refl with ++→⊎ xs pxs | ++→⊎-cong xs {a = pxs} ≡.refl
      ...| inj₁ _ | left  ≡.refl  =  left  ≡.refl
      ...| inj₂ _ | right ≡.refl  =  right ≡.refl

      ++→⊎∘⊎→++≅id : ∀ zs {ws} → (pf : Some₀ P zs ⊎ Some₀ P ws) → (_≡_ ∥ _≡_) (++→⊎ zs (⊎→++ pf)) pf
      ++→⊎∘⊎→++≅id [] (inj₁ ())
      ++→⊎∘⊎→++≅id [] (inj₂ _) = right ≡.refl
      ++→⊎∘⊎→++≅id (z ∷ zs)      (inj₁ (here p)) = left ≡.refl
      ++→⊎∘⊎→++≅id (z ∷ zs) {ws} (inj₁ (there p)) with ++→⊎ zs {ws} (⊎→++ (inj₁ p)) | ++→⊎∘⊎→++≅id zs {ws} (inj₁ p)
      ... | inj₁ pp | left pp≡p = left (≡.cong there pp≡p)
      ++→⊎∘⊎→++≅id (z ∷ zs) {ws} (inj₂ p) with ++→⊎ zs {ws} (⊎→++ {zs} (inj₂ p)) | ++→⊎∘⊎→++≅id zs (inj₂ p)
      ... | inj₂ pp | right pp≡p = right pp≡p

      ⊎→++∘++→⊎≅id : ∀ zs {ws} → (x : Some₀ P (zs ++ ws)) → ⊎→++ {zs} {ws} (++→⊎ zs x) ≡ x
      ⊎→++∘++→⊎≅id []       x = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (here p) = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (there p) with ++→⊎ zs p | ⊎→++∘++→⊎≅id zs p
      ... | inj₁ y | ≡.refl = ≡.refl
      ... | inj₂ y | ≡.refl = ≡.refl
\end{code}
%}}}

%{{{ ⊥⊥ : bottom as a setoid ; ⊥≅Some[] : ⊥⊥ ≅ Some P []
\begin{code}
⊥⊥ : ∀ {a ℓa} → Setoid a ℓa
⊥⊥ {a} {ℓa} = record
  { Carrier = ⊥
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  }
\end{code}

\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid {!!} {!!}} where

  ⊥≅Some[] : ⊥⊥ {a} {ℓa} ≅ Some P []
  ⊥≅Some[] = record
    { to          =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; from        =   record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; inverse-of  =   record { left-inverse-of = λ _ → tt ; right-inverse-of = λ {()} }
    }
\end{code}
%}}}

%{{{ map≅ : ⋯→ Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)
\begin{code}
map≅ : ∀ {a ℓa} {A B : Setoid a ℓa} {P : B ⟶ SSetoid {!!} {!!}} {f : A ⟶ B} {xs : List (Setoid.Carrier A)} →
       Some (P ∘ f) xs ≅ Some P (map (_⟨$⟩_ f) xs)
map≅ {A = A} {B} {P} {f} = record
  { to = record { _⟨$⟩_ = map⁺ ; cong = λ { ≡.refl → ≡.refl } }
  ; from = record { _⟨$⟩_ = map⁻ ; cong = λ { ≡.refl → ≡.refl } }
  ; inverse-of = record { left-inverse-of = map⁻∘map⁺ ; right-inverse-of = map⁺∘map⁻ } }
  where
  g = _⟨$⟩_ f
  A₀ = Setoid.Carrier A
  map⁺ : {xs : List A₀} → Some₀ (P ∘ f) xs → Some₀ P (map g xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : {xs : List A₀} → Some₀ P (map g xs) → Some₀ (P ∘ f) xs
  map⁻ {[]} ()
  map⁻ {x ∷ xs} (here p) = here p
  map⁻ {x ∷ xs} (there p) = there (map⁻ {xs = xs} p)

  map⁺∘map⁻ : {xs : List A₀ } → (p : Some₀ P (map g xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {[]} ()
  map⁺∘map⁻ {x ∷ xs} (here p) = ≡.refl
  map⁺∘map⁻ {x ∷ xs} (there p) = ≡.cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : {xs : List A₀} → (p : Some₀ (P ∘ f) xs) → map⁻ (map⁺ p) ≡ p
  map⁻∘map⁺ {[]} ()
  map⁻∘map⁺ {x ∷ xs} (here p) = ≡.refl
  map⁻∘map⁺ {x ∷ xs} (there p) = ≡.cong there (map⁻∘map⁺ p)
\end{code}
%}}}

%{{{ Some-cong : (∀ {x} → x ∈ xs₁ ≅ x ∈ xs₂) → Some P xs₁ ≅ Some P xs₂
This isn't quite the full-powered cong, but is all we need.
\begin{code}
module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid {!!} {!!}} where

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
    
  copy : ∀ {x} {ys} → x ∈₀ ys → Setoid.Carrier (P ⟨$⟩ x) → Some₀ P ys
  copy (here p) pf = here (_≅_.to (Π.cong P p) ⟨$⟩ pf)
  copy (there p) pf = there (copy p pf)
  
  find : ∀ {xs} → Some₀ P xs → ∃ (λ x → (x ∈₀ xs) × P₀ x)
  find {[]} ()
  find {x ∷ xs} (here p) = x , here (Setoid.refl A) , p
  find {x ∷ xs} (there p) = 
    let pos = find p in proj₁ pos , there (proj₁ (proj₂ pos)) , proj₂ (proj₂ pos)
    
  xs₁→xs₂ : ∀ {xs ys} →  (∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → Some₀ P xs → Some₀ P ys
  xs₁→xs₂ {[]} _ ()
  xs₁→xs₂ {x ∷ xs}      rel (here {.x} p) = copy {x} (_≅_.to rel ⟨$⟩ here (Setoid.refl A)) p
  xs₁→xs₂ {x ∷ xs} {ys} rel (there {.x} {.xs} p) = 
    let pos = find p in copy (_≅_.to rel ⟨$⟩ there (proj₁ (proj₂ pos))) (proj₂ (proj₂ pos))
    
  left-inv : ∀ {xs ys} → (rel : ∀ {x} → (x ∈ xs) ≅ (x ∈ ys)) → (∀ y → xs₁→xs₂ (≅-sym rel) (xs₁→xs₂ rel y) ≡ y)
  left-inv {[]} rel ()
  left-inv {x ∷ xs} rel (here p) with _≅_.to (rel {x}) ⟨$⟩ (here (Setoid.refl A))
  ... | here q = {!!}
  ... | there q = {!!}
  left-inv {x ∷ xs} rel (there p) = {!!}
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
