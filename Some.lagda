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
Setoid based variant of Any.  The definition is 'wrong' in the sense the target of P
really should be a 'Setoid of types', and not one necessarily with ≡ as its equivalence.
We really need an 'interpretable setoid', i.e. one which has ⟦_⟧ : Carrier → Set p,
as I don't know how to otherwise say that the target Setoid must have a type as a Carrier.

Quite a bit of this is directly inspired by Data.List.Any and Data.List.Any.Properties.

\begin{code}
module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid {ℓa} {ℓa}) where
   open Setoid A renaming (Carrier to A₀ ; _≈_ to _≈ₐ_)
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   data Some₀  : List A₀ → Set (a ⊔ ℓa) where
     here  : ∀ {x xs} (px  : P₀ x) → Some₀ (x ∷ xs)
     there : ∀ {x xs} (pxs : Some₀ xs) → Some₀ (x ∷ xs)

   _≈E_ : (x y : A₀) → Setoid ℓa ℓa
   _≈E_ x y =
     record { Carrier = x ≈ₐ y ; _≈_ = λ _ _ → ⊤
         ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }

   Some : List (Setoid.Carrier A) → Setoid (a ⊔ ℓa) (a ⊔ ℓa)
   Some xs = record
     { Carrier = Some₀ xs
     ; _≈_ = _≡_ -- TODO, this is what needs changed next to fill
     ; isEquivalence = ≡.isEquivalence
     }
\end{code}
%}}}

%{{{ Membership module : setoid≈ ; _∈ₛ_
\begin{code}
module Membership {a ℓ} (S : Setoid a ℓ) where
  private
    open module  S = Setoid S renaming
      (Carrier to A; _≈_ to _≈ₛ_; trans to _⟨≈ₛ⟩_ ; reflexive to ≡→≈)

  infix 4 _∈ₛ_ _∈_

  setoid≈ : A → S ⟶ SSetoid {ℓ} {ℓ}
  setoid≈ x = record
    { _⟨$⟩_ = λ y → _≈S_ {A = S} x y   -- This is an ``evil'' which will be amended in time.
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈ₛ⟩ i≈j         ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈j → x≈j ⟨≈ₛ⟩ (S.sym i≈j) ; cong = λ _ → tt }
      ; inverse-of = record
        { left-inverse-of = λ _ → tt
        ; right-inverse-of = λ _ → tt } } }

  _∈ₛ_ : A → List A → Set (ℓ ⊔ a)
  x ∈ₛ xs = Some₀ (setoid≈ x) xs

  _∈_ : A → List A → Setoid (a ⊔ ℓ) (a ⊔ ℓ)
  x ∈ xs = Some (setoid≈ x) xs

\end{code}
%}}}

\begin{code}
≡→Some : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid} {xs ys : List (Setoid.Carrier A)} →
  xs ≡ ys → Some P xs ≅ Some P ys
≡→Some {A = A} ≡.refl =
  let open Setoid A renaming (refl to refl≈) in
  record { to = id ; from = id ; inverse-of = record { left-inverse-of = λ _ → ≡.refl ; right-inverse-of = λ _ → ≡.refl } }
\end{code}

Some useful stuff about union of setoids commuting, and the ⊥ Setoid
\begin{code}
infix 1 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊔ i₂) (i₁ ⊔ i₂ ⊔ k₁ ⊔ k₂)
A ⊎⊎ B = A ⊎-setoid B

⊎-comm : {a b aℓ bℓ : Level} {A : Setoid a aℓ} {B : Setoid b bℓ} → (A ⊎⊎ B) ≅ (B ⊎⊎ A)
⊎-comm {A = A} {B} = record
  { to = record { _⟨$⟩_ = swap₊ ; cong = cong-i≈j }
  ; from = record { _⟨$⟩_ = swap₊ ; cong = cong′-i≈j }
  ; inverse-of = record { left-inverse-of = swapswap ; right-inverse-of = swapswap′ } }
  where
    A₀ = Setoid.Carrier A
    B₀ = Setoid.Carrier B
    _≈₁_ = Setoid._≈_ A
    _≈₂_ = Setoid._≈_ B
    cong-i≈j : {i j : A₀ ⊎ B₀} → (_⊎-Rel_ _≈₁_ _≈₂_ i j) → _⊎-Rel_ _≈₂_ _≈₁_ (swap₊ i) (swap₊ j)
    cong-i≈j (⊎ʳ.₁∼₂ ())
    cong-i≈j (⊎ʳ.₁∼₁ x∼₁y) = ⊎ʳ.₂∼₂ x∼₁y
    cong-i≈j (⊎ʳ.₂∼₂ x∼₂y) = ⊎ʳ.₁∼₁ x∼₂y
    -- cong′ could really be "the same" as cong-i≈j, but that can be done later
    cong′-i≈j : {i j : B₀ ⊎ A₀} → (_⊎-Rel_ _≈₂_ _≈₁_ i j) → _⊎-Rel_ _≈₁_ _≈₂_ (swap₊ i) (swap₊ j)
    cong′-i≈j (⊎ʳ.₁∼₂ ())
    cong′-i≈j (⊎ʳ.₁∼₁ x∼₁y) = ⊎ʳ.₂∼₂ x∼₁y
    cong′-i≈j (⊎ʳ.₂∼₂ x∼₂y) = ⊎ʳ.₁∼₁ x∼₂y
    swapswap : (z : A₀ ⊎ B₀) → _⊎-Rel_ _≈₁_ _≈₂_ (swap₊ (swap₊ z)) z
    swapswap (inj₁ x) = ⊎ʳ.₁∼₁ (Setoid.refl A)
    swapswap (inj₂ y) = ⊎ʳ.₂∼₂ (Setoid.refl B)
    swapswap′ : (z : B₀ ⊎ A₀) → _⊎-Rel_ _≈₂_ _≈₁_ (swap₊ (swap₊ z)) z
    swapswap′ (inj₁ x) = ⊎ʳ.₁∼₁ (Setoid.refl B)
    swapswap′ (inj₂ y) = ⊎ʳ.₂∼₂ (Setoid.refl A)

⊥⊥ : ∀ {a ℓa} → Setoid a ℓa
⊥⊥ {a} {ℓa} = record { Carrier = ⊥ ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }

module _ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid} where
  ++≅ : {xs ys : List (Setoid.Carrier A) } → (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
  ++≅ {xs} {ys} = record
    { to = record { _⟨$⟩_ = ⊎→++ ; cong = cong-to }
    ; from = record { _⟨$⟩_ = ++→⊎ xs ; cong = cong-from xs }
    ; inverse-of = record
      { left-inverse-of = ++→⊎∘⊎→++≅id xs
      ; right-inverse-of = ⊎→++∘++→⊎≅id xs } }
    where
      ⊎→ˡ : ∀ {ws zs} → Some₀ P ws → Some₀ P (ws ++ zs)
      ⊎→ˡ (here p) = here p
      ⊎→ˡ (there p) = there (⊎→ˡ p)
      ⊎→ʳ : ∀ xs {ys} → Some₀ P ys → Some₀ P (xs ++ ys)
      ⊎→ʳ []        p = p
      ⊎→ʳ (x ∷ xs₁) p = there (⊎→ʳ xs₁ p)
      ⊎→++ : ∀ {zs ws} → (Some₀ P zs ⊎ Some₀ P ws) → Some₀ P (zs ++ ws)
      ⊎→++ (inj₁ x) = ⊎→ˡ x
      ⊎→++ {zs} (inj₂ y) = ⊎→ʳ zs y
      ++→⊎ : ∀ xs {ys} → Some₀ P (xs ++ ys) → Some₀ P xs ⊎ Some₀ P ys
      ++→⊎ [] p = inj₂ p
      ++→⊎ (x ∷ l) (here p) = inj₁ (here p)
      ++→⊎ (x ∷ l) (there p) = (there ⊎₁ id₀) (++→⊎ l p)

      -- all of the following may need to change
      cong-to : {a b : Some₀ P xs ⊎ Some₀ P ys} → _⊎-Rel_ _≡_ _≡_ a b → ⊎→++ a ≡ ⊎→++ b
      cong-to (⊎ʳ.₁∼₂ ())
      cong-to (⊎ʳ.₁∼₁ ≡.refl) = ≡.refl
      cong-to (⊎ʳ.₂∼₂ ≡.refl) = ≡.refl
      
      cong-from : ∀ ws {zs} {a b : Some₀ P (ws ++ zs)} → a ≡ b → _⊎-Rel_ _≡_ _≡_ (++→⊎ ws a) (++→⊎ ws b)
      cong-from [] ≡.refl = ⊎ʳ.₂∼₂ ≡.refl
      cong-from (x ∷ xs) {a = here  p} ≡.refl = ⊎ʳ.₁∼₁ ≡.refl
      cong-from (x ∷ xs) {zs} {a = there p} ≡.refl with ++→⊎ xs p | cong-from xs {a = p} ≡.refl
      ... | inj₁ z | ⊎ʳ.₁∼₁ ≡.refl = ⊎ʳ.₁∼₁ ≡.refl
      ... | inj₂ z | ⊎ʳ.₂∼₂ ≡.refl = ⊎ʳ.₂∼₂ ≡.refl

      ++→⊎∘⊎→++≅id : ∀ zs {ws} → (x : Some₀ P zs ⊎ Some₀ P ws) → _⊎-Rel_ _≡_ _≡_ (++→⊎ zs (⊎→++ x)) x
      ++→⊎∘⊎→++≅id []           (inj₁ ())
      ++→⊎∘⊎→++≅id []           (inj₂ y) = ⊎ʳ.₂∼₂ ≡.refl
      ++→⊎∘⊎→++≅id (x ∷ l)      (inj₁ (here p)) = ⊎ʳ.₁∼₁ ≡.refl
      ++→⊎∘⊎→++≅id (x ∷ l) {ws} (inj₁ (there p)) with ++→⊎ l {ws} (⊎→++ (inj₁ p)) | ++→⊎∘⊎→++≅id l {ws} (inj₁ p)
      ... | inj₁ pf | ⊎ʳ.₁∼₁ ≡.refl = ⊎ʳ.₁∼₁ ≡.refl
      ... | inj₂ pf | ()
      ++→⊎∘⊎→++≅id (x ∷ l) {ws} (inj₂ y) with ++→⊎ l {ws} (⊎→++ {l} (inj₂ y)) | ++→⊎∘⊎→++≅id l (inj₂ y)
      ... | inj₁ _ | ⊎ʳ.₁∼₂ ()
      ... | inj₂ _ | ⊎ʳ.₂∼₂ ≡.refl = ⊎ʳ.₂∼₂ ≡.refl

      ⊎→++∘++→⊎≅id : ∀ zs {ws} → (x : Some₀ P (zs ++ ws)) → ⊎→++ {zs} {ws} (++→⊎ zs x) ≡ x
      ⊎→++∘++→⊎≅id []       x = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (here p) = ≡.refl
      ⊎→++∘++→⊎≅id (x ∷ zs) (there p) with ++→⊎ zs p | ⊎→++∘++→⊎≅id zs p
      ... | inj₁ y | ≡.refl = ≡.refl
      ... | inj₂ y | ≡.refl = ≡.refl

  ⊥≅Some[] : ⊥⊥ {a} {ℓa} ≅ Some P []
  ⊥≅Some[] = record
    { to = record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; from = record { _⟨$⟩_ = λ {()} ; cong = λ { {()} } }
    ; inverse-of = record { left-inverse-of = λ _ → tt ; right-inverse-of = λ {()} } }

map≅ : ∀ {a ℓa} {A B : Setoid a ℓa} {P : B ⟶ SSetoid} {f : A ⟶ B} {xs : List (Setoid.Carrier A)} →
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

-- This isn't quite the full-powered cong, but is all we need.
Some-cong : ∀ {a ℓ} {A : Setoid a ℓ} {P : A ⟶ SSetoid} {xs₁ xs₂ : List (Setoid.Carrier A)} →
           let open Membership A in
           (∀ {x} → (x ∈ xs₁) ≅ (x ∈ xs₂)) →
           Some P xs₁ ≅ Some P xs₂
Some-cong {A = A} {P} {xs₁} {xs₂} list-rel = record
  { to = record { _⟨$⟩_ = xs₁→xs₂ list-rel ; cong = {!!} }
  ; from = record { _⟨$⟩_ = xs₁→xs₂ (≅-sym list-rel) ; cong = {!!} }
  ; inverse-of = record { left-inverse-of = left-inv list-rel ; right-inverse-of = {!!} } }
  where
  open Membership A
  copy : ∀ {x} {ys} → Setoid.Carrier (x ∈ ys) → Setoid.Carrier (P ⟨$⟩ x) → Some₀ P ys
  copy (here p) pf = here (_≅_.to (Π.cong P p) ⟨$⟩ pf)
  copy (there p) pf = there (copy p pf)
  find : ∀ {xs} → Some₀ P xs → ∃ (λ x → Setoid.Carrier (x ∈ xs) × Setoid.Carrier (P ⟨$⟩ x))
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
