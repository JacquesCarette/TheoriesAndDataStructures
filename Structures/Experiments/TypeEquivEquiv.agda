{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Level
open import Equiv
  using (≐-refl; ≐-sym; ≐-trans; sym≃;
    _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv; gg;
    β⊎₁; β⊎₂; β₁; β₂; cong∘l; cong∘r; cong₂∘; β×₁; β×₂)
open import TypeEquiv
  using (unite₊equiv; uniti₊equiv; unite₊′equiv; uniti₊′equiv;
    assocr₊equiv; assocl₊equiv; swap₊equiv;
    unite⋆equiv; uniti⋆equiv; unite⋆′equiv; uniti⋆′equiv;
    assocr⋆equiv; assocl⋆equiv; swap⋆equiv;
    distlequiv; factorlequiv; distequiv; factorequiv;
    distzrequiv; factorzrequiv; distzequiv; factorzequiv)
open import EquivEquiv

open import DataProperties using (⊥; ⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; _×_; proj₁)
open import Function using (_∘_)

open import Data.Sum.Properties2
  using (id⊎id∼id; ⊎∘∼∘⊎; _⊎∼_;
    unite₊-coh; uniti₊-coh; unite₊′-coh; uniti₊′-coh;
    assocr₊-wf; assocl₊-wf;
    triangle⊎-left; triangle⊎-right;
    pentagon⊎-right; pentagon⊎-left;
    swap₊-coh; unite₊-swap-coh-left; unite₊-swap-coh-right;
    hexagon⊎-right; hexagon⊎-left)

open import Data.Product.Properties2
  using (id×id∼id; ×∘∼∘×; _×∼_;
    unite⋆-coh; uniti⋆-coh; unite⋆′-coh; uniti⋆′-coh;
    assocr⋆-wf; assocl⋆-wf;
    triangle×-left; triangle×-right;
    pentagon×-right; pentagon×-left;
    swap⋆-coh;  unite⋆-swap-coh-left; unite⋆-swap-coh-right;
    hexagon×-right; hexagon×-left)

open import Data.SumProd.Properties -- TODO: list them

-- some local abbreviations to make life nicer
infixr 10 _⊙_

private
  _⊙_ = ≐-trans
  !_ = ≐-sym

-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

-- TODO: quite possibly, everything here should be abstract, as
-- it shouldn't be useful to look into the structure of the proofs,
-- but just that they do, indeed exist.  That and the proofs are in
-- fact rather boring, consisting of explicit sequences of
-- unveil --> delegate to lower level -> veil
-- operations.
----
-- equivalences for the ⊎ structure

[id,id]≋id : ∀ {A B : Set} → id≃ {A = A} ⊎≃ id≃ {A = B} ≋ id≃
[id,id]≋id = eq (β⊎₁ ⊙ id⊎id∼id) (β⊎₂ ⊙ id⊎id∼id)

-- ● and ⊎≃ commute.

⊎●≋●⊎ : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ⊎≃ (i ● g) ≋ (h ⊎≃ i) ● (f ⊎≃ g)
⊎●≋●⊎ =
  eq (β⊎₁ ⊙ β₁ ⊎∼ β₁ ⊙ ⊎∘∼∘⊎ ⊙ ! cong₂∘ β⊎₁ β⊎₁ ⊙ ! β₁)
     (β⊎₂ ⊙ β₂ ⊎∼ β₂ ⊙ ⊎∘∼∘⊎ ⊙ ! cong₂∘ β⊎₂ β⊎₂ ⊙ ! β₂)

-- ≋ has, predictably, an additive structure as well

_⊎≋_ : {A B C D : Set} {f h : A ≃ B} {g i : C ≃ D} → f ≋ h → g ≋ i →
  f ⊎≃ g ≋ h ⊎≃ i
f≋h ⊎≋ g≋i =
  eq (β⊎₁ ⊙ (f≡ f≋h) ⊎∼ (f≡ g≋i) ⊙ ! β⊎₁)
     (β⊎₂ ⊙ (g≡ f≋h) ⊎∼ (g≡ g≋i) ⊙ ! β⊎₂)
  where open _≋_

-- strangely, this is not needed by Rig Category.  However, it
-- belongs to the structure of a Monoidal Groupoid (I think!  Should
-- be checked), and is quite useful on its own.

sym≃-distrib⊎ : ∀ {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  sym≃ (f ⊎≃ g) ≋ sym≃ f ⊎≃ sym≃ g
sym≃-distrib⊎ = -- note how the proof mixes ₁ and ₂ !
  eq (β⊎₂ ⊙ ! β⊎₁) (β⊎₁ ⊙ ! β⊎₂)

-- Use '-nat' to signify that operation induces a
-- natural transformation, and that the induced operation
-- satisfies the naturality condition thus encoded

unite₊-nat : ∀ {A B} {f : A ≃ B} {g : ⊥ ≃ ⊥} →
  unite₊equiv ● (g ⊎≃ f) ≋ f ● unite₊equiv
unite₊-nat {g = g} =
  eq (β₁ ⊙ cong∘l (proj₁ unite₊equiv) β⊎₁ ⊙ unite₊-coh ⊙ ! β₁)
       (β₂ ⊙ cong∘r (gg unite₊equiv) β⊎₂ ⊙ uniti₊-coh {g = gg g} ⊙ ! β₂)

uniti₊-nat : ∀ {A B} {f : A ≃ B} {g : ⊥ ≃ ⊥} →
  uniti₊equiv ● f ≋ (g ⊎≃ f) ● uniti₊equiv
uniti₊-nat {g = g} =
  eq (β₁ ⊙ ! uniti₊-coh {g = proj₁ g} ⊙ ! cong∘r (proj₁ uniti₊equiv) β⊎₁ ⊙ ! β₁)
       (β₂ ⊙ ! unite₊-coh ⊙ ! cong∘l (gg uniti₊equiv) β⊎₂ ⊙ ! β₂)

unite₊′-nat : ∀ {A B} {f : A ≃ B} {g : ⊥ ≃ ⊥} →
  unite₊′equiv ● (f ⊎≃ g) ≋ f ● unite₊′equiv
unite₊′-nat {g = g} =
  eq (β₁ ⊙ cong∘l (proj₁ unite₊′equiv) β⊎₁ ⊙ unite₊′-coh ⊙ ! β₁)
     (β₂ ⊙ cong∘r (gg unite₊′equiv) β⊎₂ ⊙ uniti₊′-coh {g = gg g} ⊙ ! β₂)

uniti₊′-nat : ∀ {A B} {f : A ≃ B} {g : ⊥ ≃ ⊥} →
  uniti₊′equiv ● f ≋ (f ⊎≃ g) ● uniti₊′equiv
uniti₊′-nat {g = g} =
  eq (β₁ ⊙ ! uniti₊′-coh {g = proj₁ g} ⊙ ! cong∘r (proj₁ uniti₊′equiv) β⊎₁ ⊙ ! β₁)
       (β₂ ⊙ ! unite₊′-coh ⊙ ! cong∘l (gg uniti₊′equiv) β⊎₂ ⊙ ! β₂)

assocr₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr₊equiv ● ((f₀ ⊎≃ f₁) ⊎≃ f₂) ≋ (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ● assocr₊equiv
assocr₊-nat {A} {B} {C} {D} {E} {F} {f₀} {f₁} {f₂} =
  let assocrDEF = proj₁ (assocr₊equiv {A = D} {E} {F}) in
  let assocrABC = proj₁ (assocr₊equiv {A = A} {B} {C}) in
  let assoclDEF = gg (assocr₊equiv {A = D} {E} {F}) in
  let assoclABC = gg (assocr₊equiv {A = A} {B} {C}) in
  eq (β₁ ⊙ cong∘l assocrDEF (β⊎₁ ⊙ (β⊎₁ ⊎∼ ≐-refl)) ⊙
           assocr₊-wf ⊙
           ! cong∘r assocrABC (≐-refl ⊎∼ β⊎₁) ⊙
           ! cong∘r assocrABC β⊎₁ ⊙ ! β₁)
     (β₂ ⊙ cong∘r assoclDEF (β⊎₂ {f = f₀ ⊎≃ f₁} {f₂}) ⊙
           cong∘r assoclDEF (β⊎₂ ⊎∼ ≐-refl) ⊙
           assocl₊-wf ⊙
          ! cong∘l assoclABC (≐-refl ⊎∼ β⊎₂) ⊙
          ! cong∘l assoclABC (β⊎₂ {f = f₀} {f₁ ⊎≃ f₂}) ⊙ ! β₂)

assocl₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl₊equiv ● (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ≋ ((f₀ ⊎≃ f₁) ⊎≃ f₂) ● assocl₊equiv
assocl₊-nat {A} {B} {C} {D} {E} {F} {f₀} {f₁} {f₂} =
  let assoclDEF = proj₁ (assocl₊equiv {A = D} {E} {F}) in
  let assoclABC = proj₁ (assocl₊equiv {A = A} {B} {C}) in
  let assocrDEF = gg (assocl₊equiv {A = D} {E} {F}) in
  let assocrABC = gg (assocl₊equiv {A = A} {B} {C}) in
  eq (β₁ ⊙ cong∘l assoclDEF β⊎₁ ⊙
           cong∘l assoclDEF (≐-refl ⊎∼ β⊎₁) ⊙
           ! assocl₊-wf ⊙
           ! cong∘r assoclABC (β⊎₁ ⊎∼ ≐-refl) ⊙
           ! cong∘r assoclABC β⊎₁ ⊙ ! β₁)
     (β₂ ⊙ cong∘r assocrDEF (β⊎₂ {f = f₀} {f₁ ⊎≃ f₂}) ⊙
           cong∘r assocrDEF (≐-refl ⊎∼ β⊎₂) ⊙
           ! assocr₊-wf ⊙
           ! cong∘l assocrABC (β⊎₂ ⊎∼ ≐-refl) ⊙
           ! cong∘l assocrABC (β⊎₂ {f = f₀ ⊎≃ f₁} {f₂}) ⊙ ! β₂)

-- often called 'triangle'
unite-assocr₊-coh : ∀ {A B : Set} →
  unite₊′equiv ⊎≃ id≃ ≋ (id≃ ⊎≃ unite₊equiv) ● assocr₊equiv {A = A} {⊥} {B}
unite-assocr₊-coh = -- eq triangle⊎-right triangle⊎-left
  eq (β⊎₁ ⊙ triangle⊎-right ⊙ ! (β₁ ⊙ cong∘r (proj₁ assocr₊equiv) β⊎₁))
     (β⊎₂ ⊙ triangle⊎-left ⊙ ! (β₂ ⊙ cong∘l (gg assocr₊equiv) β⊎₂))

-- often called 'pentagon'
assocr₊-coh : ∀ {A B C D : Set} →
  assocr₊equiv {A = A} {B} {C ⊎ D} ● assocr₊equiv ≋
  (id≃ ⊎≃ assocr₊equiv) ● assocr₊equiv ● (assocr₊equiv ⊎≃ id≃)
assocr₊-coh = -- eq pentagon⊎-right pentagon⊎-left
 eq (β₁ ⊙ pentagon⊎-right ⊙
     ! (β₁ ⊙ cong₂∘ β⊎₁ β₁ ⊙
        cong∘l ((proj₁ id≃ ⊎→ proj₁ assocr₊equiv) ∘ proj₁ assocr₊equiv) β⊎₁))
    (β₂ ⊙ pentagon⊎-left ⊙
     ! (β₂ ⊙ cong₂∘ β₂ β⊎₂ ⊙
        cong∘r (gg assocr₊equiv ∘ (gg id≃ ⊎→ gg assocr₊equiv)) β⊎₂))

swap₊-nat : {A B C D : Set} {f : A ≃ C} {g : B ≃ D} →
  swap₊equiv ● (f ⊎≃ g) ≋ (g ⊎≃ f) ● swap₊equiv
swap₊-nat =
  eq (β₁ ⊙ cong∘l (proj₁ swap₊equiv) β⊎₁ ⊙ swap₊-coh ⊙
        ! (β₁ ⊙ cong∘r (proj₁ swap₊equiv) β⊎₁))
     (β₂ ⊙ cong∘r (gg swap₊equiv) β⊎₂ ⊙ ! swap₊-coh ⊙
        ! (β₂ ⊙ cong∘l (gg swap₊equiv) β⊎₂))

-- also called 'triangle', but better to call it 'unit coherence'
unite₊l-coh : {A : Set} →
  unite₊equiv {A = A} ≋ unite₊′equiv ● swap₊equiv
unite₊l-coh =
  eq (unite₊-swap-coh-right ⊙ ! β₁) (unite₊-swap-coh-left ⊙ ! β₂)

-- often called 'hexagon'
assocr₊-swap₊-coh : ∀ {A B C : Set} →
  assocr₊equiv {A = B} {C} {A} ● swap₊equiv ● assocr₊equiv {A = A} {B} {C} ≋
  id≃ ⊎≃ swap₊equiv ● assocr₊equiv {A = B} {A} {C} ● swap₊equiv ⊎≃ id≃
assocr₊-swap₊-coh {A} {B} {C} = -- eq hexagon⊎-right hexagon⊎-left
  let assocrBCA = proj₁ (assocr₊equiv {A = B} {C} {A}) in
  let assocrABC = proj₁ (assocr₊equiv {A = A} {B} {C}) in
  let assocrBAC = proj₁ (assocr₊equiv {A = B} {A} {C}) in
  let swapAC = proj₁ id≃ ⊎→ proj₁ (swap₊equiv {A = A} {C}) in
  let assoclBCA = gg (assocr₊equiv {A = B} {C} {A}) in
  let assoclABC = gg (assocr₊equiv {A = A} {B} {C}) in
  let assoclBAC = gg (assocr₊equiv {A = B} {A} {C}) in
  let swapCA = gg id≃ ⊎→ gg (swap₊equiv {A = A} {C}) in
  eq (β₁ ⊙ cong∘l assocrBCA β₁ ⊙ hexagon⊎-right ⊙
      ! (β₁ ⊙ cong₂∘ β⊎₁ β₁ ⊙ cong∘l (swapAC ∘ assocrBAC) β⊎₁))
     (β₂ ⊙ cong∘r assoclBCA β₂ ⊙ hexagon⊎-left ⊙
      ! (β₂ ⊙ cong₂∘ β₂ β⊎₂ ⊙ cong∘r (assoclBAC ∘ swapCA) β⊎₂))

-- and in the opposite direction

assocl₊-swap₊-coh : ∀ {A B C : Set} →
  assocl₊equiv {A = A} {B} {C} ● swap₊equiv ● assocl₊equiv {A = B} {C} {A} ≋
  swap₊equiv ⊎≃ id≃ ● assocl₊equiv {A = B} {A} {C} ● id≃ ⊎≃ swap₊equiv
assocl₊-swap₊-coh {A} {B} {C} = -- eq hexagon⊎-left hexagon⊎-right
  let assoclBCA = proj₁ (assocl₊equiv {A = B} {C} {A}) in
  let assoclABC = proj₁ (assocl₊equiv {A = A} {B} {C}) in
  let assoclBAC = proj₁ (assocl₊equiv {A = B} {A} {C}) in
  let swapBA = proj₁ (swap₊equiv {A = B} {A}) ⊎→ proj₁ id≃ in
  let assocrBCA = gg (assocl₊equiv {A = B} {C} {A}) in
  let assocrABC = gg (assocl₊equiv {A = A} {B} {C}) in
  let assocrBAC = gg (assocl₊equiv {A = B} {A} {C}) in
  let swapAB = gg (swap₊equiv {A = B} {A}) ⊎→ proj₁ id≃ in
  eq (β₁ ⊙ (cong∘l assoclABC β₁ ⊙ hexagon⊎-left) ⊙
      ! (β₁ ⊙ cong₂∘ β⊎₁ β₁ ⊙ cong∘l (swapBA ∘ assoclBAC) β⊎₁))
     (β₂ ⊙ cong∘r assocrABC β₂ ⊙ hexagon⊎-right ⊙
      ! (β₂ ⊙ cong₂∘ β₂ β⊎₂ ⊙ cong∘r (assocrBAC ∘ swapAB) β⊎₂))

-- equivalences for the × structure

id×id≋id : ∀ {A B : Set} → id≃ {A = A} ×≃ id≃ {A = B} ≋ id≃
id×id≋id = eq (β×₁ ⊙ id×id∼id) (β×₂ ⊙ id×id∼id)

×●≋●× : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ×≃ (i ● g) ≋ (h ×≃ i) ● (f ×≃ g)
×●≋●× {f = f , qinv f⁻¹ _ _} {g , qinv g⁻¹ _ _} {h , qinv h⁻¹ _ _} {i , qinv i⁻¹ _ _} =
  eq (β×₁ ⊙ β₁ ×∼ β₁ ⊙ (×∘∼∘× {f = f} {g} {h} {i}) ⊙ ! cong₂∘ β×₁ β×₁ ⊙ ! β₁)
     (β×₂ ⊙ β₂ ×∼ β₂ ⊙ (×∘∼∘× {f = h⁻¹} {i⁻¹} {f⁻¹} {g⁻¹}) ⊙ ! cong₂∘ β×₂ β×₂ ⊙ ! β₂)

_×≋_ :  ∀ {A B C D : Set} {f g : A ≃ B} {h i : C ≃ D} →
  f ≋ g → h ≋ i → f ×≃ h ≋ g ×≃ i
e₁ ×≋ e₂ = eq (β×₁ ⊙ (f≡ e₁) ×∼ (f≡ e₂) ⊙ ! β×₁)
              (β×₂ ⊙ (g≡ e₁) ×∼ (g≡ e₂) ⊙ ! β×₂)
  where open _≋_

sym≃-distrib× : ∀ {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  sym≃ (f ×≃ g) ≋ sym≃ f ×≃ sym≃ g
sym≃-distrib× = -- note how the proof mixes ₁ and ₂ !
  eq (β×₂ ⊙ ! β×₁) (β×₁ ⊙ ! β×₂)


unite⋆-nat : ∀ {A B} {f : A ≃ B} {g : ⊤ {zero} ≃ ⊤} →
  unite⋆equiv {_} {zero} ● (g ×≃ f) ≋ f ● unite⋆equiv
unite⋆-nat = -- eq unite⋆-coh uniti⋆-coh
  eq (β₁ ⊙ cong∘l (proj₁ unite⋆equiv) β×₁ ⊙ unite⋆-coh ⊙ ! β₁)
     (β₂ ⊙ cong∘r (gg unite⋆equiv) β×₂ ⊙ uniti⋆-coh ⊙ ! β₂)

uniti⋆-nat : ∀ {A B} {f : A ≃ B} {g : ⊤ {zero} ≃ ⊤} →
  uniti⋆equiv {_} {zero} ● f ≋ (g ×≃ f) ● uniti⋆equiv
uniti⋆-nat = -- flip-sym≋ unite⋆-nat
  eq (β₁ ⊙ ! uniti⋆-coh ⊙ ! cong∘r (proj₁ uniti⋆equiv) β×₁ ⊙ ! β₁)
     (β₂ ⊙ ! unite⋆-coh ⊙ ! cong∘l (gg uniti⋆equiv) β×₂ ⊙ ! β₂)

unite⋆′-nat : ∀ {A B} {f : A ≃ B} {g : ⊤ {zero} ≃ ⊤} →
  unite⋆′equiv {_} {zero} ● (f ×≃ g) ≋ f ● unite⋆′equiv
unite⋆′-nat = -- eq unite⋆′-coh uniti⋆′-coh
  eq (β₁ ⊙ cong∘l (proj₁ unite⋆′equiv) β×₁ ⊙ unite⋆′-coh ⊙ ! β₁)
     (β₂ ⊙ cong∘r (gg unite⋆′equiv) β×₂ ⊙ uniti⋆′-coh ⊙ ! β₂)

uniti⋆′-nat : ∀ {A B} {f : A ≃ B} {g : ⊤ {zero} ≃ ⊤} →
  uniti⋆′equiv ● f ≋ (f ×≃ g) ● uniti⋆′equiv
uniti⋆′-nat = -- flip-sym≋ unite⋆′-nat
  eq (β₁ ⊙ ! uniti⋆′-coh ⊙ ! cong∘r (proj₁ uniti⋆′equiv) β×₁ ⊙ ! β₁)
     (β₂ ⊙ ! unite⋆′-coh ⊙ ! cong∘l (gg uniti⋆′equiv) β×₂ ⊙ ! β₂)

assocr⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr⋆equiv ● ((f₀ ×≃ f₁) ×≃ f₂) ≋ (f₀ ×≃ (f₁ ×≃ f₂)) ● assocr⋆equiv
assocr⋆-nat {A} {B} {C} {D} {E} {F} {f₀} {f₁} {f₂} = -- eq assocr⋆-wf assocl⋆-wf
  let assocrDEF = proj₁ (assocr⋆equiv {D} {E} {F}) in
  let assocrABC = proj₁ (assocr⋆equiv {A} {B} {C}) in
  let assoclDEF = gg (assocr⋆equiv {D} {E} {F}) in
  let assoclABC = gg (assocr⋆equiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l assocrDEF β×₁ ⊙
           cong∘l assocrDEF (β×₁ ×∼ ≐-refl) ⊙
           assocr⋆-wf ⊙
           ! cong∘r assocrABC (≐-refl ×∼ β×₁) ⊙
           ! cong∘r assocrABC β×₁ ⊙ ! β₁)
     (β₂ ⊙ cong∘r assoclDEF (β×₂ {f = f₀ ×≃ f₁} {f₂}) ⊙
           cong∘r assoclDEF (β×₂ ×∼ ≐-refl) ⊙
           assocl⋆-wf ⊙
          ! cong∘l assoclABC (≐-refl ×∼ β×₂) ⊙
          ! cong∘l assoclABC (β×₂ {f = f₀} {f₁ ×≃ f₂}) ⊙ ! β₂)
assocl⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl⋆equiv ● (f₀ ×≃ (f₁ ×≃ f₂)) ≋ ((f₀ ×≃ f₁) ×≃ f₂) ● assocl⋆equiv
assocl⋆-nat {A} {B} {C} {D} {E} {F} {f₀} {f₁} {f₂}  = -- flip-sym≋ assocr⋆-nat
  let assoclDEF = proj₁ (assocl⋆equiv {D} {E} {F}) in
  let assoclABC = proj₁ (assocl⋆equiv {A} {B} {C}) in
  let assocrDEF = gg (assocl⋆equiv {D} {E} {F}) in
  let assocrABC = gg (assocl⋆equiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l assoclDEF β×₁ ⊙
           cong∘l assoclDEF (≐-refl ×∼ β×₁) ⊙
           ! assocl⋆-wf ⊙
           ! cong∘r assoclABC (β×₁ ×∼ ≐-refl) ⊙
           ! cong∘r assoclABC β×₁ ⊙ ! β₁)
     (β₂ ⊙ cong∘r assocrDEF (β×₂ {f = f₀} {f₁ ×≃ f₂}) ⊙
           cong∘r assocrDEF (≐-refl ×∼ β×₂) ⊙
           ! assocr⋆-wf ⊙
           ! cong∘l assocrABC (β×₂ ×∼ ≐-refl) ⊙
           ! cong∘l assocrABC (β×₂ {f = f₀ ×≃ f₁} {f₂}) ⊙ ! β₂)

-- often called 'triangle'

unite-assocr⋆-coh : ∀ {A B : Set} →
  unite⋆′equiv ×≃ id≃ ≋ (id≃ ×≃ unite⋆equiv) ● assocr⋆equiv {A} {⊤} {B}
unite-assocr⋆-coh =
  eq (β×₁ ⊙ triangle×-right ⊙ ! (β₁ ⊙ cong∘r (proj₁ assocr⋆equiv) β×₁))
     (β×₂ ⊙ triangle×-left ⊙ ! (β₂ ⊙ cong∘l (gg assocr⋆equiv) β×₂))

-- often called 'pentagon'

assocr⋆-coh : ∀ {A B C D : Set} →
  assocr⋆equiv {A} {B} {C × D} ● assocr⋆equiv ≋
  (id≃ ×≃ assocr⋆equiv) ● assocr⋆equiv ● (assocr⋆equiv ×≃ id≃)
assocr⋆-coh =
 eq (β₁ ⊙ pentagon×-right ⊙
     ! (β₁ ⊙ cong₂∘ β×₁ β₁ ⊙
        cong∘l ((proj₁ id≃ ×→ proj₁ assocr⋆equiv) ∘ proj₁ assocr⋆equiv) β×₁))
    (β₂ ⊙ pentagon×-left ⊙
     ! (β₂ ⊙ cong₂∘ β₂ β×₂ ⊙
        cong∘r (gg assocr⋆equiv ∘ (gg id≃ ×→ gg assocr⋆equiv)) β×₂))

swap⋆-nat : {A B C D : Set} {f : A ≃ C} {g : B ≃ D} →
  swap⋆equiv ● (f ×≃ g) ≋ (g ×≃ f) ● swap⋆equiv
swap⋆-nat =
  eq (β₁ ⊙ cong∘l (proj₁ swap⋆equiv) β×₁ ⊙ swap⋆-coh ⊙
        ! (β₁ ⊙ cong∘r (proj₁ swap⋆equiv) β×₁))
     (β₂ ⊙ cong∘r (gg swap⋆equiv) β×₂ ⊙ ! swap⋆-coh ⊙
        ! (β₂ ⊙ cong∘l (gg swap⋆equiv) β×₂))

-- also called 'triangle', but better to call it 'unit coherence'
unite⋆l-coh : {A : Set} →
  unite⋆equiv {A = A} ≋ unite⋆′equiv ● swap⋆equiv
unite⋆l-coh =
  eq (unite⋆-swap-coh-right ⊙ ! β₁) (unite⋆-swap-coh-left ⊙ ! β₂)

-- often called 'hexagon'

assocr⋆-swap⋆-coh : ∀ {A B C : Set} →
  assocr⋆equiv {A = B} {C} {A} ● swap⋆equiv ● assocr⋆equiv {A = A} {B} {C} ≋
  id≃ ×≃ swap⋆equiv ● assocr⋆equiv {A = B} {A} {C} ● swap⋆equiv ×≃ id≃
assocr⋆-swap⋆-coh {A} {B} {C} =
  let assocrBCA = proj₁ (assocr⋆equiv {A = B} {C} {A}) in
  let assocrABC = proj₁ (assocr⋆equiv {A = A} {B} {C}) in
  let assocrBAC = proj₁ (assocr⋆equiv {A = B} {A} {C}) in
  let swapAC = proj₁ id≃ ×→ proj₁ (swap⋆equiv {A = A} {C}) in
  let assoclBCA = gg (assocr⋆equiv {A = B} {C} {A}) in
  let assoclABC = gg (assocr⋆equiv {A = A} {B} {C}) in
  let assoclBAC = gg (assocr⋆equiv {A = B} {A} {C}) in
  let swapCA = gg id≃ ×→ gg (swap⋆equiv {A = A} {C}) in
  eq (β₁ ⊙ cong∘l assocrBCA β₁ ⊙ hexagon×-right ⊙
      ! (β₁ ⊙ cong₂∘ β×₁ β₁ ⊙ cong∘l (swapAC ∘ assocrBAC) β×₁))
     (β₂ ⊙ cong∘r assoclBCA β₂ ⊙ hexagon×-left ⊙
      ! (β₂ ⊙ cong₂∘ β₂ β×₂ ⊙ cong∘r (assoclBAC ∘ swapCA) β×₂))

-- and in the opposite direction

assocl⋆-swap⋆-coh : ∀ {A B C : Set} →
  assocl⋆equiv {A} {B} {C} ● swap⋆equiv ● assocl⋆equiv {B} {C} {A} ≋
  swap⋆equiv ×≃ id≃ ● assocl⋆equiv {B} {A} {C} ● id≃ ×≃ swap⋆equiv
assocl⋆-swap⋆-coh {A} {B} {C} =
  let assoclBCA = proj₁ (assocl⋆equiv {B} {C} {A}) in
  let assoclABC = proj₁ (assocl⋆equiv {A} {B} {C}) in
  let assoclBAC = proj₁ (assocl⋆equiv {B} {A} {C}) in
  let swapBA = proj₁ (swap⋆equiv {B} {A}) ×→ proj₁ id≃ in
  let assocrBCA = gg (assocl⋆equiv {B} {C} {A}) in
  let assocrABC = gg (assocl⋆equiv {A} {B} {C}) in
  let assocrBAC = gg (assocl⋆equiv {B} {A} {C}) in
  let swapAB = gg (swap⋆equiv {B} {A}) ×→ proj₁ id≃ in
  eq (β₁ ⊙ (cong∘l assoclABC β₁ ⊙ hexagon×-left) ⊙
      ! (β₁ ⊙ cong₂∘ β×₁ β₁ ⊙ cong∘l (swapBA ∘ assoclBAC) β×₁))
     (β₂ ⊙ cong∘r assocrABC β₂ ⊙ hexagon×-right ⊙
      ! (β₂ ⊙ cong₂∘ β₂ β×₂ ⊙ cong∘r (assocrBAC ∘ swapAB) β×₂))

-- distributivity

distl-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  distlequiv ● (f ×≃ (g ⊎≃ h)) ≋ ((f ×≃ g) ⊎≃ (f ×≃ h)) ● distlequiv
distl-nat {A} {B} {C} {D} {E} {F} {f} {g} {h} = -- eq distl-coh factorl-coh
  let distlDEF = proj₁ (distlequiv {D} {E} {F}) in
  let distlABC = proj₁ (distlequiv {A} {B} {C}) in
  let factorlDEF = gg (distlequiv {D} {E} {F}) in
  let factorlABC = gg (distlequiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l distlDEF (β×₁ ⊙ (≐-refl ×∼ β⊎₁)) ⊙
      distl-coh ⊙
      ! (β₁ ⊙ cong∘r distlABC (β⊎₁ ⊙ (β×₁ ⊎∼ β×₁))))
      --
     (β₂ ⊙ cong∘r factorlDEF (β×₂ {f = f} {g ⊎≃ h} ⊙ (≐-refl ×∼ β⊎₂)) ⊙
      factorl-coh ⊙
      ! (β₂ ⊙ cong∘l factorlABC (β⊎₂ {f = f ×≃ g} {f ×≃ h} ⊙ (β×₂ ⊎∼ β×₂))))

factorl-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
   factorlequiv ● ((f ×≃ g) ⊎≃ (f ×≃ h)) ≋ (f ×≃ (g ⊎≃ h)) ● factorlequiv
factorl-nat {A} {B} {C} {D} {E} {F} {f} {g} {h} = -- flip-sym≋ distl-nat
  let factorlDEF = proj₁ (factorlequiv {D} {E} {F}) in
  let factorlABC = proj₁ (factorlequiv {A} {B} {C}) in
  let distlDEF = gg (factorlequiv {D} {E} {F}) in
  let distlABC = gg (factorlequiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l factorlDEF (β⊎₁ ⊙ (β×₁ ⊎∼ β×₁)) ⊙
      ! factorl-coh ⊙
      ! (β₁ ⊙ cong∘r factorlABC (β×₁ ⊙ (≐-refl ×∼ β⊎₁)) ))
     --
     (β₂ ⊙ cong∘r distlDEF (β⊎₂ {f = f ×≃ g} {f ×≃ h} ⊙ (β×₂ ⊎∼ β×₂)) ⊙
     ! distl-coh ⊙
     ! (β₂ ⊙ cong∘l distlABC (β×₂ {f = f} {g ⊎≃ h} ⊙ (≐-refl ×∼ β⊎₂))))

dist-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  distequiv ● ((f ⊎≃ g) ×≃ h) ≋ ((f ×≃ h) ⊎≃ (g ×≃ h)) ● distequiv
dist-nat {A} {B} {C} {D} {E} {F} {f} {g} {h} = -- eq dist-coh factor-coh
  let distDEF = proj₁ (distequiv {D} {E} {F}) in
  let distABC = proj₁ (distequiv {A} {B} {C}) in
  let factorDEF = gg (distequiv {D} {E} {F}) in
  let factorABC = gg (distequiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l distDEF (β×₁ ⊙ (β⊎₁ ×∼ ≐-refl)) ⊙
      dist-coh ⊙
      ! (β₁ ⊙ cong∘r distABC (β⊎₁ ⊙ (β×₁ ⊎∼ β×₁))))
      --
     (β₂ ⊙ cong∘r factorDEF (β×₂ {f = f ⊎≃ g} {h} ⊙ (β⊎₂ ×∼ ≐-refl)) ⊙
      factor-coh ⊙
      ! (β₂ ⊙ cong∘l factorABC (β⊎₂ {f = f ×≃ h} {g ×≃ h} ⊙ (β×₂ ⊎∼ β×₂))))

factor-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  factorequiv ● ((f ×≃ h) ⊎≃ (g ×≃ h)) ≋ ((f ⊎≃ g) ×≃ h) ● factorequiv
factor-nat {A} {B} {C} {D} {E} {F} {f} {g} {h} = -- flip-sym≋ dist-nat
  let factorDEF = proj₁ (factorequiv {D} {E} {F}) in
  let factorABC = proj₁ (factorequiv {A} {B} {C}) in
  let distDEF = gg (factorequiv {D} {E} {F}) in
  let distABC = gg (factorequiv {A} {B} {C}) in
  eq (β₁ ⊙ cong∘l factorDEF (β⊎₁ ⊙ (β×₁ ⊎∼ β×₁)) ⊙
      ! factor-coh ⊙
      ! (β₁ ⊙ cong∘r factorABC (β×₁ ⊙ (β⊎₁ ×∼ ≐-refl)) ))
     --
     (β₂ ⊙ cong∘r distDEF (β⊎₂ {f = f ×≃ h} {g ×≃ h} ⊙ (β×₂ ⊎∼ β×₂)) ⊙
     ! dist-coh ⊙
     ! (β₂ ⊙ cong∘l distABC (β×₂ {f = f ⊎≃ g} {h} ⊙ (β⊎₂ ×∼ ≐-refl))))

-- note how we don't use id≃ but an arbitrary ⊥ ≃ ⊥.
-- because this law under-specifies f and g, we need to
-- be explicit in our calls

distzr-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  distzrequiv ● (f ×≃ g) ≋ g ● distzrequiv
distzr-nat {f = (f , qinv h _ _)} {(_ , qinv g _ _)} =
  -- eq (distzr-coh {f = f}) (factorzr-coh {f = h} {g})
  eq (β₁ ⊙ cong∘l (proj₁ distzrequiv) β×₁ ⊙ distzr-coh {f = f} ⊙ ! β₁)
     (β₂ ⊙ cong∘r (gg distzrequiv) β×₂ ⊙ factorzr-coh {f = h} {g} ⊙ ! β₂)

factorzr-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  factorzrequiv ● g ≋ (f ×≃ g) ● factorzrequiv
factorzr-nat {f = f , qinv f⁻¹ _ _} {g , _} = -- flip-sym≋ (distzr-nat {f = sym≃ f})
  eq (β₁ ⊙ ! (factorzr-coh {f = f} {g}) ⊙
     ! (β₁ ⊙ cong∘r (proj₁ factorzrequiv) β×₁) )
     --
     (β₂ ⊙ ! (distzr-coh {f = f⁻¹}) ⊙
     ! (β₂ ⊙ cong∘l (gg factorzrequiv) β×₂))

-- same comment as above

distz-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ {zero} ≃ ⊥} →
  distzequiv ● (g ×≃ f) ≋ g ● distzequiv
distz-nat {f = (f , qinv h _ _)} {(_ , qinv g _ _)} =
  eq (β₁ ⊙ cong∘l (proj₁ distzequiv) β×₁ ⊙ distz-coh {f = f} ⊙ ! β₁)
     (β₂ {ℓ′ = zero} ⊙ cong∘r (gg distzequiv) β×₂ ⊙ factorz-coh {f = h} {g} ⊙ ! β₂)

factorz-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ {zero} ≃ ⊥} →
  factorzequiv ● g ≋ (g ×≃ f) ● factorzequiv
factorz-nat {f = (f , qinv f⁻¹ _ _)} {g , _} =
  eq (β₁ ⊙ (! (factorz-coh {f = f} {g})) ⊙
        ! (β₁ ⊙ cong∘r (proj₁ factorzequiv) β×₁))
     (β₂ {ℓ′ = zero} ⊙ (! (distz-coh {f = f⁻¹})) ⊙ ! (β₂ ⊙ cong∘l (gg factorzequiv) β×₂))

-- some equivalences for which there are two 'obvious'
-- programs, but are in fact equivalent.  Named after
-- the types which are witnessed to be equivalent.

A×[B⊎C]≃[A×C]⊎[A×B] : {A B C : Set} →
  distlequiv ● (id≃ {A = A} ×≃ swap₊equiv {A = B} {C}) ≋ swap₊equiv ● distlequiv
A×[B⊎C]≃[A×C]⊎[A×B] = -- eq A×[B⊎C]→[A×C]⊎[A×B] [A×C]⊎[A×B]→A×[B⊎C]
  eq (β₁ ⊙ cong∘l (proj₁ distlequiv) β×₁ ⊙ A×[B⊎C]→[A×C]⊎[A×B] ⊙ ! β₁)
     (β₂ ⊙ cong∘r (gg distlequiv) β×₂ ⊙ [A×C]⊎[A×B]→A×[B⊎C] ⊙ ! β₂)

[A⊎B]×C≃[C×A]⊎[C×B] : {A B C : Set} →
  (swap⋆equiv ⊎≃ swap⋆equiv) ● distequiv ≋ distlequiv ● swap⋆equiv {A = A ⊎ B} {C}
[A⊎B]×C≃[C×A]⊎[C×B] = -- eq [A⊎B]×C→[C×A]⊎[C×B] [C×A]⊎[C×B]→[A⊎B]×C
  eq (β₁ ⊙ cong∘r (proj₁ distequiv) β⊎₁ ⊙ [A⊎B]×C→[C×A]⊎[C×B] ⊙ ! β₁)
     (β₂ ⊙ cong∘l (gg distequiv) β⊎₂ ⊙ [C×A]⊎[C×B]→[A⊎B]×C ⊙ ! β₂)

[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D : {A B C D : Set} →
  (distequiv ⊎≃ id≃) ● distequiv ● (assocl₊equiv {A = A} {B} {C} ×≃ id≃ {A = D}) ≋
  assocl₊equiv ● (id≃ ⊎≃ distequiv) ● distequiv
[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D = -- eq [A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D [A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D
  eq (β₁ ⊙ cong₂∘ β⊎₁ (β₁ ⊙ cong∘l (proj₁ distequiv) β×₁) ⊙
      [A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D ⊙
      ! (β₁ ⊙ cong∘l (proj₁ assocl₊equiv) (β₁ ⊙ cong∘r (proj₁ distequiv) β⊎₁)))
      --
     (β₂ ⊙ cong₂∘ (β₂ ⊙ cong∘r (gg distequiv) β×₂) β⊎₂ ⊙
      [A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D ⊙
      ! (β₂ ⊙ cong∘r (gg assocl₊equiv) (β₂ ⊙ cong∘l (gg distequiv) β⊎₂)))

A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D : {A B C D : Set} →
  distlequiv ● assocl⋆equiv {A} {B} {C ⊎ D} ≋
  (assocl⋆equiv ⊎≃ assocl⋆equiv) ● distlequiv ● (id≃ ×≃ distlequiv)
A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D =
  eq (β₁ ⊙ A×B×[C⊎D]→[A×B]×C⊎[A×B]×D ⊙
      ! (β₁ ⊙ cong₂∘ β⊎₁ (β₁ ⊙ cong∘l (proj₁ distlequiv) β×₁)))
     (β₂ ⊙ [A×B]×C⊎[A×B]×D→A×B×[C⊎D] ⊙
      ! (β₂ ⊙ cong₂∘ (β₂ ⊙ cong∘r (gg distlequiv) β×₂) β⊎₂))

0×0≃0 : {ℓ : Level} → distzequiv {ℓ} {ℓ} ≋ distzrequiv
0×0≃0 = eq 0×0→0 0→0×0

0×[A⊎B]≃0 : {A B : Set} →
  distzequiv ≋ unite₊equiv ● (distzequiv ⊎≃ distzequiv) ● distlequiv {⊥} {A} {B}
0×[A⊎B]≃0 =
  eq (0×[A⊎B]→0 ⊙
      ! (β₁ ⊙ cong∘l (proj₁ unite₊equiv) (β₁ ⊙ cong∘r (proj₁ distlequiv) β⊎₁)))
     (0→0×[A⊎B] ⊙
     ! (β₂ ⊙ cong∘r (gg unite₊equiv) (β₂ ⊙ cong∘l (gg distlequiv) β⊎₂)))

0×1≃0 : {ℓ ℓ′ : Level} → unite⋆′equiv {ℓ} {ℓ′} ≋ distzequiv
0×1≃0 = eq 0×1→0 0→0×1

A×0≃0 : {A : Set} → distzrequiv {A = A} ≋ distzequiv ● swap⋆equiv
A×0≃0 = eq (A×0→0 ⊙ ! β₁) (0→A×0 {_} {zero} ⊙ ! β₂)

0×A×B≃0 : {A B : Set} →
  distzequiv ≋ distzequiv ● (distzequiv ×≃ id≃) ● assocl⋆equiv {A = ⊥} {A} {B}
0×A×B≃0 =
  let distzB = proj₁ distzequiv in
  let factorzA = gg distzequiv in
  eq (0×A×B→0 ⊙
      ! (β₁ ⊙ cong∘l distzB (β₁ ⊙ cong∘r (proj₁ assocl⋆equiv) β×₁)))
     (0→0×A×B ⊙
       ! (β₂ ⊙ cong∘r factorzA (β₂ ⊙ cong∘l (gg assocl⋆equiv) β×₂)))

A×0×B≃0 : {A B : Set} →
  distzrequiv ● (id≃ ×≃ distzequiv)  ≋
  distzequiv ● (distzrequiv ×≃ id≃) ● assocl⋆equiv {A = A} {⊥} {B}
A×0×B≃0 =
  eq (β₁ ⊙ cong∘l (proj₁ distzrequiv) β×₁ ⊙ A×0×B→0 ⊙
      ! (β₁ ⊙ cong∘l (proj₁ distzequiv)
                     (β₁ ⊙ cong∘r (proj₁ assocl⋆equiv) β×₁)))
     (β₂ ⊙ cong∘r (gg distzrequiv) β×₂ ⊙  0→A×0×B ⊙
      ! (β₂ ⊙ cong∘r (gg distzequiv)
                      (β₂ ⊙ cong∘l (gg assocl⋆equiv) β×₂)))

A×[0+B]≃A×B : {A B : Set} →
  (id≃ {A = A} ×≃ unite₊equiv {A = B}) ≋ unite₊equiv ● (distzrequiv ⊎≃ id≃) ● distlequiv
A×[0+B]≃A×B =
  eq (β×₁ ⊙ A×[0+B]→A×B ⊙
      ! (β₁ ⊙ cong∘l (proj₁ unite₊equiv) (β₁ ⊙ cong∘r (proj₁ distlequiv) β⊎₁)))
     (β×₂ ⊙ A×B→A×[0+B] ⊙
      ! (β₂ ⊙ cong∘r (gg unite₊equiv) (β₂ ⊙ cong∘l (gg distlequiv) β⊎₂)))

1×[A⊎B]≃A⊎B : {A B : Set} →
  unite⋆equiv ≋ (unite⋆equiv ⊎≃ unite⋆equiv) ● distlequiv {A = ⊤} {A} {B}
1×[A⊎B]≃A⊎B =
  eq (1×[A⊎B]→A⊎B ⊙ ! (β₁ ⊙ cong∘r (proj₁ distlequiv) β⊎₁))
     (A⊎B→1×[A⊎B] ⊙ ! (β₂ ⊙ cong∘l (gg distlequiv) β⊎₂))

[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D : {A B C D : Set} →
  assocl₊equiv ● (distequiv ⊎≃ distequiv) ● distlequiv ≋
  (assocl₊equiv ⊎≃ id≃) ● ((id≃ ⊎≃ swap₊equiv) ⊎≃ id≃) ●
     (assocr₊equiv ⊎≃ id≃) ● assocl₊equiv ●
        (distlequiv ⊎≃ distlequiv) ● distequiv {A} {B} {C ⊎ D}
[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D =
  eq (β₁ ⊙ cong∘l (proj₁ assocl₊equiv)
                  (β₁ ⊙ cong∘r (proj₁ distlequiv) β⊎₁) ⊙
      [A⊎B]×[C⊎D]→[[A×C⊎B×C]⊎A×D]⊎B×D ⊙
      ! (β₁ ⊙ cong₂∘ β⊎₁ (β₁ ⊙ cong₂∘ (β⊎₁ ⊙ (β⊎₁ ⊎∼ ≐-refl))
              (β₁ ⊙ cong₂∘ β⊎₁ (β₁ ⊙ cong∘l (proj₁ assocl₊equiv)
                    (β₁ ⊙ cong∘r (proj₁ distequiv) β⊎₁))))))
      --
     (β₂ ⊙ cong∘r (gg assocl₊equiv) (β₂ ⊙ cong∘l (gg distlequiv) β⊎₂) ⊙
      [[A×C⊎B×C]⊎A×D]⊎B×D→[A⊎B]×[C⊎D] ⊙
      ! (β₂ ⊙ cong₂∘
          (β₂ ⊙ cong₂∘
            (β₂ ⊙ cong₂∘
              (β₂ ⊙ cong∘r (gg assocl₊equiv) (β₂ ⊙ cong∘l (gg distequiv) β⊎₂))
              β⊎₂)
            (β⊎₂ {f = id≃ ⊎≃ swap₊equiv} ⊙ (β⊎₂ ⊎∼ ≐-refl)))
          β⊎₂))

------------------------------------------------------------------------------
-- also useful

[g+1]●[1+f]≋g+f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f) ≋ g ⊎≃ f
[g+1]●[1+f]≋g+f {f = f} {g} = begin (
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f)
    ≋⟨ sym≋ ⊎●≋●⊎ ⟩
  (g ● id≃) ⊎≃ (id≃ ● f)
    ≋⟨ rid≋ ⊎≋ lid≋ ⟩
  g ⊎≃ f ∎)
  where open ≋-Reasoning

-- same proof as above, just written compactly

[1+f]●[g+1]≋g+f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (id≃ ⊎≃ f) ● (g ⊎≃ id≃) ≋ g ⊎≃ f
[1+f]●[g+1]≋g+f = trans≋ (sym≋ ⊎●≋●⊎) (lid≋ ⊎≋ rid≋)

-- put then together

[g+1]●[1+f]≋[1+f]●[g+1] : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f) ≋ (id≃ ⊎≃ f) ● (g ⊎≃ id≃)
[g+1]●[1+f]≋[1+f]●[g+1] = trans≋ [g+1]●[1+f]≋g+f (sym≋ [1+f]●[g+1]≋g+f)

--

[g*1]●[1*f]≋g*f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ×≃ id≃) ● (id≃ ×≃ f) ≋ g ×≃ f
[g*1]●[1*f]≋g*f {f = f} {g} = begin (
  (g ×≃ id≃) ● (id≃ ×≃ f)
    ≋⟨ sym≋ ×●≋●× ⟩
  (g ● id≃) ×≃ (id≃ ● f)
    ≋⟨ rid≋ ×≋ lid≋ ⟩
  g ×≃ f ∎)
  where open ≋-Reasoning

[1*f]●[g*1]≋g*f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (id≃ ×≃ f) ● (g ×≃ id≃) ≋ g ×≃ f
[1*f]●[g*1]≋g*f = trans≋ (sym≋ ×●≋●×) (lid≋ ×≋ rid≋)

[g*1]●[1*f]≋[1*f]●[g*1] : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ×≃ id≃) ● (id≃ ×≃ f) ≋ (id≃ ×≃ f) ● (g ×≃ id≃)
[g*1]●[1*f]≋[1*f]●[g*1] = trans≋ [g*1]●[1*f]≋g*f (sym≋ [1*f]●[g*1]≋g*f)


------------------------------------------------------------------------------
