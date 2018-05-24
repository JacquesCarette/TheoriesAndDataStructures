{-# OPTIONS --without-K #-}

module VectorLemmas where

open import Level using (Level)

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n)
open import Data.Nat.Properties.Simple using (+-comm; +-right-identity)

open import Data.Fin using (Fin; zero; suc; inject+; raise; reduce≥)
open import Data.Fin.Properties using (toℕ-injective)

open import Data.Vec
  using (Vec; []; _∷_; lookup; tabulate)
  renaming (map to mapV; _++_ to _++V_; concat to concatV)
open import Data.Vec.Properties
  using (lookup∘tabulate; tabulate∘lookup; tabulate-∘; lookup-++-≥)

open import Function using (id; _∘_; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong; cong₂; proof-irrelevance;
         module ≡-Reasoning)

open import FinNatLemmas using (toℕ-invariance)
open import SubstLemmas using (subst-subst)
open import FiniteFunctions using (finext)

------------------------------------------------------------------------------
-- Lemmas about map and tabulate

-- to make things look nicer

_!!_ : ∀ {m} {A : Set} → Vec A m → Fin m → A
v !! i = lookup i v

-- this is actually in Data.Vec.Properties, but over an arbitrary
-- Setoid.  Specialize

map-id : ∀ {a n} {A : Set a} (xs : Vec A n) → mapV id xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (_∷_ x) (map-id xs)

map-++-commute : ∀ {a b m n} {A : Set a} {B : Set b}
                 (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                 mapV f (xs ++V ys) ≡ mapV f xs ++V mapV f ys
map-++-commute f []       = refl
map-++-commute f (x ∷ xs) = cong (λ z → f x ∷ z) (map-++-commute f  xs)

-- this is too, but is done "point free", this version is more convenient

map-∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) → (xs : Vec A n) →
        mapV (f ∘ g) xs ≡ (mapV f ∘ mapV g) xs
map-∘ f g [] = refl
map-∘ f g (x ∷ xs) = cong (_∷_ (f (g x))) (map-∘ f g xs)

-- this looks trivial, why can't I find it?

lookup-map : ∀ {a b} {n : ℕ} {A : Set a} {B : Set b} →
  (i : Fin n) → (f : A → B) →
  (v : Vec A n) → lookup i (mapV f v) ≡ f (lookup i v)
lookup-map {n = 0} () _ _
lookup-map {n = suc n} zero f (x ∷ v) = refl
lookup-map {n = suc n} (suc i) f (x ∷ v) = lookup-map i f v

-- These are 'generalized' lookup into left/right parts of a Vector which
-- does not depend on the values in the Vector at all.

look-left : ∀ {m n} {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
  (i : Fin m) → (f : A → C) → (g : B → C) → (vm : Vec A m) → (vn : Vec B n) →
  lookup (inject+ n i) (mapV f vm ++V mapV g vn) ≡ f (lookup i vm)
look-left {0} () _ _ _ _
look-left {suc _} zero f g (x ∷ vm) vn = refl
look-left {suc _} (suc i) f g (x ∷ vm) vn = look-left i f g vm vn

look-right : ∀ {m n} {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
  (i : Fin n) → (f : A → C) → (g : B → C) → (vm : Vec A m) → (vn : Vec B n) →
  lookup (raise m i) (mapV f vm ++V mapV g vn) ≡ g (lookup i vn)
look-right {zero} i f g [] vm = lookup-map i g vm
look-right {suc m} {0} () _ _ _ _
look-right {suc m} {suc n} i f g (x ∷ vn) vm = look-right i f g vn vm

-- variant

left!! : ∀ {m n} {C : Set} →
  (i : Fin m) → (f : Fin m → C) → {g : Fin n → C} →
  (tabulate f ++V tabulate g) !! (inject+ n i) ≡ f i
left!! {zero} () _
left!! {suc _} zero f = refl
left!! {suc _} (suc i) f = left!! i (f ∘ suc)

right!! : ∀ {m n} {C : Set} →
  (i : Fin n) → {f : Fin m → C} → (g : Fin n → C) →
  (tabulate f ++V tabulate g) !! (raise m i) ≡ g i
right!! {zero} i g = lookup∘tabulate g i
right!! {suc _} {0} () _
right!! {suc m} {suc _} i g = right!! {m} i g

-- similar to lookup-++-inject+ from library

lookup-++-raise : ∀ {m n} {a : Level} {A : Set a} →
  (vm : Vec A m) (vn : Vec A n) (i : Fin n) →
  lookup (raise m i) (vm ++V vn) ≡ lookup i vn
lookup-++-raise {0} vn vm i =
  begin (lookup i (vn ++V vm)
           ≡⟨ lookup-++-≥ vn vm i z≤n ⟩
         lookup (reduce≥ i z≤n) vm
            ≡⟨ refl ⟩
         lookup i vm ∎)
  where open ≡-Reasoning
lookup-++-raise {suc m} {0} _ _ ()
lookup-++-raise {suc m} {suc n} (x ∷ vn) vm i = lookup-++-raise vn vm i

-- concat (map (map f) xs) = map f (concat xs)

concat-map : ∀ {a b m n} {A : Set a} {B : Set b} →
  (xs : Vec (Vec A n) m) → (f : A → B) →
  concatV (mapV (mapV f) xs) ≡ mapV f (concatV xs)
concat-map [] f = refl
concat-map (xs ∷ xss) f =
  begin (concatV (mapV (mapV f) (xs ∷ xss))
           ≡⟨ refl ⟩
         concatV (mapV f xs ∷ mapV (mapV f) xss)
           ≡⟨  refl ⟩
         mapV f xs ++V concatV (mapV (mapV f) xss)
           ≡⟨ cong (_++V_ (mapV f xs)) (concat-map xss f) ⟩
         mapV f xs ++V mapV f (concatV xss)
           ≡⟨ sym (map-++-commute f xs) ⟩
         mapV f (xs ++V concatV xss)
           ≡⟨ refl ⟩
         mapV f (concatV (xs ∷ xss)) ∎)
  where open ≡-Reasoning

map-map-map : ∀ {a b c m n} {A : Set a} {B : Set b} {C : Set c} →
  (f  : B → C) → (g : A → Vec B n) → (xs : Vec A m) →
  mapV (mapV f) (mapV g xs) ≡ mapV (mapV f ∘ g) xs
map-map-map f g xss = sym (map-∘ (mapV f) g xss)

splitV+ : ∀ {m n} {a : Level} {A : Set a} {f : Fin (m + n) → A} →
          Vec A (m + n)
splitV+ {m} {n} {f = f} =
  tabulate {m} (f ∘ inject+ n) ++V tabulate {n} (f ∘ raise m)

splitVOp+ : ∀ {m} {n} {a : Level} {A : Set a} {f : Fin (n + m) → A} →
            Vec A (m + n)
splitVOp+ {m} {n} {f = f} =
  tabulate {m} (f ∘ raise n) ++V tabulate {n} (f ∘ inject+ m)

-- f can be implicit since this is mostly used in equational
-- reasoning, where it can be inferred!

tabulate-split : ∀ {m n} {a : Level} {A : Set a} → {f : Fin (m + n) → A} →
  tabulate {m + n} f ≡ splitV+ {m} {n} {f = f}
tabulate-split {0} = refl
tabulate-split {suc m} {f = f} =
  cong (_∷_ (f zero)) (tabulate-split {m} {f = f ∘ suc})

lookup-subst : ∀ {m m' n}
  (i : Fin n) (xs : Vec (Fin m) n) (eq : m ≡ m') →
  lookup i (subst (λ s → Vec (Fin s) n) eq xs) ≡
  subst Fin eq (lookup i xs)
lookup-subst i xs refl = refl

-- lookup is associative on Fin vectors

lookupassoc : ∀ {m₁ m₂ m₃ m₄} → (π₁ : Vec (Fin m₂) m₁)
  (π₂ : Vec (Fin m₃) m₂) (π₃ : Vec (Fin m₄) m₃) → (i : Fin m₁) →
  lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)) ≡
  lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃
lookupassoc π₁ π₂ π₃ i =
  begin (lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃))
           ≡⟨ lookup∘tabulate (λ j → lookup (lookup j π₂) π₃) (lookup i π₁) ⟩
         lookup (lookup (lookup i π₁) π₂) π₃
           ≡⟨ cong
                (λ x → lookup x π₃)
                (sym (lookup∘tabulate (λ j → lookup (lookup j π₁) π₂) i)) ⟩
         lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃ ∎)
  where open ≡-Reasoning

-- This should generalize a lot, but that can be done later

subst-lookup-tabulate-raise : ∀ {m n : ℕ} → (z : Fin n) →
  subst Fin
    (+-comm n m)
    (lookup z (tabulate (λ i → subst Fin (+-comm m n) (raise m i)))) ≡
  raise m z
subst-lookup-tabulate-raise {m} {n} z =
 begin (subst Fin
          (+-comm n m)
          (lookup z (tabulate (λ i → subst Fin (+-comm m n) (raise m i))))
      ≡⟨ cong (subst Fin (+-comm n m))
             (lookup∘tabulate (λ i → subst Fin (+-comm m n) (raise m i)) z) ⟩
    subst Fin (+-comm n m) (subst Fin (+-comm m n) (raise m z))
      ≡⟨ subst-subst (+-comm n m) (+-comm m n)
           (proof-irrelevance (sym (+-comm n m)) (+-comm m n)) (raise m z) ⟩
    raise m z
     ∎)
  where open ≡-Reasoning

subst-lookup-tabulate-inject+ : ∀ {m n : ℕ} → (z : Fin m) →
  subst Fin
    (+-comm n m)
    (lookup z (tabulate (λ i → subst Fin (+-comm m n) (inject+ n i)))) ≡
  inject+ n z
subst-lookup-tabulate-inject+ {m} {n} z =
 begin (subst Fin
          (+-comm n m)
          (lookup z (tabulate (λ i → subst Fin (+-comm m n) (inject+ n i))))
      ≡⟨ cong (subst Fin (+-comm n m))
             (lookup∘tabulate (λ i → subst Fin (+-comm m n) (inject+ n i)) z) ⟩
    subst Fin (+-comm n m) (subst Fin (+-comm m n) (inject+ n z))
      ≡⟨ subst-subst (+-comm n m) (+-comm m n)
           (proof-irrelevance (sym (+-comm n m)) (+-comm m n)) (inject+ n z) ⟩
    inject+ n z
     ∎)
  where open ≡-Reasoning

-- a kind of inverse for splitAt

unSplit : {m n : ℕ} {A : Set} → (f : Fin (m + n) → A) →
  tabulate {m} (f ∘ (inject+ n)) ++V tabulate {n} (f ∘ (raise m)) ≡ tabulate f
unSplit {0} {n} f = refl
unSplit {suc m} f = cong (λ x → (f zero) ∷ x) (unSplit {m} (f ∘ suc))

-- nested tabulate-lookup
denest-tab-!! : {A B C : Set} {k : ℕ} → (f : B → C) → (g : A → B) →
    (v : Vec A k) →
    tabulate (λ i → f (tabulate (λ j → g (v !! j)) !! i)) ≡ mapV (f ∘ g) v
denest-tab-!! f g v =
  begin (
    tabulate (λ i → f (tabulate (λ j → g (v !! j)) !! i))
        ≡⟨ tabulate-∘ f (λ i → tabulate (λ j → g (v !! j)) !! i) ⟩
    mapV f (tabulate  (λ i → tabulate (λ j → g (v !! j)) !! i) )
        ≡⟨ cong (mapV f) (tabulate∘lookup (tabulate (λ j → g (v !! j)))) ⟩
    mapV f (tabulate (λ j → g (v !! j)))
        ≡⟨ cong (mapV f) (tabulate-∘ g (flip lookup v)) ⟩
    mapV f (mapV g (tabulate (flip lookup v)))
        ≡⟨ sym (map-∘ f g _) ⟩
    mapV (f ∘ g) (tabulate (flip lookup v))
        ≡⟨ cong (mapV (f ∘ g)) (tabulate∘lookup v) ⟩
    mapV (f ∘ g) v ∎)
  where open ≡-Reasoning

tab++[]≡tab∘̂unite+ : ∀ {m} {A : Set} (f : Fin m → A) (eq : m + 0 ≡ m) →
  tabulate f ++V [] ≡ tabulate (λ j → f (subst Fin eq j))
tab++[]≡tab∘̂unite+ {zero} f eq = refl
tab++[]≡tab∘̂unite+ {suc m} f eq = cong₂ _∷_ (cong f pf₁) pf₂
  where
    pf₁ : zero ≡ subst Fin eq zero
    pf₁ = toℕ-injective (sym (toℕ-invariance zero eq))
    pf₃ : ∀ j → suc (subst Fin (+-right-identity m) j) ≡ subst Fin eq (suc j)
    pf₃ j = toℕ-injective
              (trans (cong suc (toℕ-invariance j (+-right-identity m)))
                     (sym (toℕ-invariance (suc j) eq)))
    pf₂ : tabulate (f ∘ suc) ++V [] ≡
          tabulate (λ j → f (subst Fin eq (suc j)))
    pf₂ = trans (tab++[]≡tab∘̂unite+ (f ∘ suc) (+-right-identity m))
                (finext (λ j → cong f (pf₃ j)))

------------------------------------------------------------------------------
