%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open import Function2         using (_$ᵢ)
open import Function          using () renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)

open import Forget
open import EqualityCombinators
open import DataProperties
open import SetoidEquiv

open import TypeEquiv using (swap₊)

import Relation.Binary.PropositionalEquality as P
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\begin{code}
record CommMonoid {ℓ} {o} : Set (lsuc ℓ ⊍ lsuc o) where
  constructor MkCommMon
  field setoid : Setoid ℓ o
  open Setoid setoid public

  field
    e          : Carrier
    _*_        : Carrier → Carrier → Carrier
    left-unit  : {x : Carrier} → e * x ≈ x
    right-unit : {x : Carrier} → x * e ≈ x
    assoc      : {x y z : Carrier} → (x * y) * z ≈ x * (y * z)
    comm       : {x y : Carrier} → x * y ≈ y * x
    _⟨*⟩_       : {x y z w : Carrier} → x ≈ y → z ≈ w → x * z ≈ y * w
  module ≈ = Setoid setoid
  _⟨≈⟩_ = trans

infix -666 eq-in
eq-in = CommMonoid._≈_
syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

record Hom {ℓ} {o} (A B : CommMonoid {ℓ} {o}) : Set (ℓ ⊍ o) where
  constructor MkHom
  open CommMonoid using (setoid; Carrier)
  open CommMonoid A using () renaming (e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B using () renaming (e to e₂; _*_ to _*₂_; _≈_ to _≈₂_)

  field mor    : setoid A ⟶ setoid B
  private mor₀ = Π._⟨$⟩_ mor
  field
    pres-e : mor₀ e₁ ≈₂ e₂
    pres-* : {x y : Carrier A} → mor₀ (x *₁ y)  ≈₂  mor₀ x *₂ mor₀ y

  open Π mor public
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.

%}}}

%{{{ MonoidCat ; Forget
\begin{code}
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (ℓ ⊍ o)
MonoidCat ℓ o = record
  { Obj = CommMonoid {ℓ} {o}
  ; _⇒_ = Hom
  ; _≡_ = λ {A} {B} F G → ∀ {x} → F ⟨$⟩ x ≈ G ⟨$⟩ x ∶ B
  ; id  = λ {A} → let open CommMonoid A in MkHom id refl refl
  ; _∘_ = λ { {C = C} F G → let open CommMonoid C in record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  (cong F (pres-e G)) ⟨≈⟩ (pres-e F)
    ; pres-*   =  (cong F (pres-* G)) ⟨≈⟩ (pres-* F)
    } }
  ; assoc     = λ { {D = D} → CommMonoid.refl D}
  ; identityˡ = λ {_} {B} → CommMonoid.refl B
  ; identityʳ = λ {_} {B} → CommMonoid.refl B
  ; equiv     = λ {_} {B} → record
    { refl  = CommMonoid.refl B
    ; sym   = λ F≈G → CommMonoid.sym B F≈G
    ; trans = λ F≈G G≈H → CommMonoid.trans B F≈G G≈H
    }
  ; ∘-resp-≡ = λ { {C = C} {f = F} F≈F' G≈G' → CommMonoid.trans C (cong F G≈G') F≈F' }
  }
  where open Hom
\end{code}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ (o ⊍ ℓ)) (Setoids ℓ (o ⊍ ℓ))
Forget ℓ o = record
  { F₀             =   λ C → record { CommMonoid C }
  ; F₁             =   λ F → record { Hom F }
  ; identity       =   λ {A} → ≈.refl A
  ; homomorphism   =   λ {A} {B} {C} → ≈.refl C
  ; F-resp-≡      =   λ F≈G {x} → F≈G {x}
  }
  where open CommMonoid using (module ≈)
\end{code}
%}}}

%{{{ Multiset

A “multiset on type X” is a commutative monoid with a to it from |X|.
For now, we make no constraints on the map, however it may be that
future proof obligations will require it to be an injection ---which is reasonable.

\begin{code}
record Multiset {ℓ o : Level} (X : Setoid ℓ o) : Set (lsuc ℓ ⊍ lsuc o) where
  field
    commMonoid : CommMonoid {ℓ} {ℓ ⊍ o}
    singleton : Setoid.Carrier X → CommMonoid.Carrier commMonoid
  open CommMonoid commMonoid public

open Multiset
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure.

\begin{code}
record MultisetHom {ℓ} {o} {X Y : Setoid ℓ o} (A : Multiset X) (B : Multiset Y) : Set (ℓ ⊍ o) where
  constructor MKMSHom
  field
    lift : (X ⟶ Y) → Hom (commMonoid A) (commMonoid B)

open MultisetHom
\end{code}

%}}}

%{{{ Some₀
Setoid based variant of Any.  The definition is 'wrong' in the sense the target of P
really should be a 'Setoid of types', and not one necessarily with ≡ as its equivalence.
We really need an 'interpretable setoid', i.e. one which has ⟦_⟧ : Carrier → Set p,
as I don't know how to otherwise say that the target Setoid must have a type as a Carrier.

\begin{code}
open import SetoidSetoid

module _ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid {ℓa} {ℓa}) where
   open Setoid A renaming (Carrier to A₀ ; _≈_ to _≈ₐ_)
   P₀ = λ e → Setoid.Carrier (Π._⟨$⟩_ P e)

   data Some₀  : List A₀ → Set (a ⊍ ℓa) where
     here  : ∀ {x xs} (px  : P₀ x) → Some₀ (x ∷ xs)
     there : ∀ {x xs} (pxs : Some₀ xs) → Some₀ (x ∷ xs)

   _≈E_ : (x y : A₀) → Setoid ℓa ℓa
   _≈E_ x y =
     record { Carrier = x ≈ₐ y ; _≈_ = λ _ _ → ⊤
         ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }
\end{code}
%}}}

%{{{ Membership module : setoid≈ ; _∈ₛ_
\begin{code}
module Membership {a ℓ} (S : Setoid a ℓ) where
  private
    open module  S = Setoid S renaming
      (Carrier to A; _≈_ to _≈ₛ_; trans to _⟨≈ₛ⟩_ ; reflexive to ≡→≈)

  infix 4 _∈ₛ_

  setoid≈ : A → S ⟶ SSetoid {ℓ} {ℓ}
  setoid≈ x = record
    { _⟨$⟩_ = λ y → _≈S_ {A = S} x y   -- This is an ``evil'' which will be amended in time.
    ; cong = λ i≈j → record
      { to   = record { _⟨$⟩_ = λ x≈i → x≈i ⟨≈ₛ⟩ i≈j         ; cong = λ _ → tt }
      ; from = record { _⟨$⟩_ = λ x≈j → x≈j ⟨≈ₛ⟩ (S.sym i≈j) ; cong = λ _ → tt }
      ; inverse-of = record
        { left-inverse-of = λ _ → tt
        ; right-inverse-of = λ _ → tt } } }

  _∈ₛ_ : A → List A → Set (ℓ ⊍ a)
  x ∈ₛ xs = Some₀ (setoid≈ x) xs
\end{code}
%}}}

\begin{code}
Some : {a ℓa : Level} {A : Setoid a ℓa} (P : A ⟶ SSetoid) → List (Setoid.Carrier A) → Setoid (a ⊍ ℓa) (a ⊍ ℓa)
Some {a} {ℓa} {A} P xs = record
  { Carrier = Some₀ P xs
  ; _≈_ = _≡_ -- TODO, this is what needs changed next to fill
  ; isEquivalence = ≡.isEquivalence
  }

≡→Some : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid} {xs ys : List (Setoid.Carrier A)} →
  xs ≡ ys → Some P xs ≅ Some P ys
≡→Some {A = A} ≡.refl =
  let open Setoid A renaming (refl to refl≈) in
  record { to = id ; from = id ; inverse-of = record { left-inverse-of = λ _ → ≡.refl ; right-inverse-of = λ _ → ≡.refl } }
\end{code}

Some useful stuff about union of setoids commuting
\begin{code}
open import Relation.Binary.Sum -- using (_⊎-setoid_)
infix 1 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊍ i₂) (i₁ ⊍ i₂ ⊍ k₁ ⊍ k₂)
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

-- Same names as in Data.List.Any.Properties
-- (this file sorely needs to be split into pieces!)
++≅ : ∀ {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid} {xs ys : List (Setoid.Carrier A) } →
      (Some P xs ⊎⊎ Some P ys) ≅ Some P (xs ++ ys)
++≅ {P = P} {xs} {ys} = record
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
      -- induction hypothesis probably needs generalized
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
\end{code}

%{{{ ListMS
\begin{code}
abstract
  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { commMonoid = record
        { setoid     =  LM
        ; e          =  []
        ; _*_        =  _++_
        ; left-unit  =  Setoid.refl LM
        ; right-unit = λ {xs} → ≡→≈ₘ (proj₂ ++.identity xs)
        ; assoc      =  λ {xs} {ys} {zs} → ≡→≈ₘ (++.assoc xs ys zs)
        ; comm       =  λ {xs} {ys} {z} →
          z ∈ xs ++ ys        ≅⟨ ≅-sym ++≅ ⟩
          (z ∈ xs ⊎⊎ z ∈ ys)  ≅⟨ ⊎-comm ⟩
          (z ∈ ys ⊎⊎ z ∈ xs)  ≅⟨ ++≅ ⟩
          z ∈ ys ++ xs  ∎
        ; _⟨*⟩_ = λ {x} {y} {z} {w} x≈y z≈w {t} →
           t ∈ x ++ z        ≅⟨ ≅-sym ++≅ ⟩
          (t ∈ x ⊎⊎ t ∈ z)   ≅⟨ x≈y ⊎-inverse z≈w ⟩
          (t ∈ y ⊎⊎ t ∈ w)   ≅⟨ ++≅ ⟩
           t ∈ y ++ w ∎
        }
    ; singleton = λ x → x ∷ []
    }
    where
      open import Algebra using (Monoid)
      open import Data.List using (monoid)
      module ++ = Monoid (monoid (Setoid.Carrier X))
      open Membership X

      X₀ = Setoid.Carrier X

      infix 4 _∈_

      _∈_ : X₀ → List X₀ → Setoid (o ⊍ ℓ) (o ⊍ ℓ)
      x ∈ xs = Some (setoid≈ x) xs

      _≈ₘ_ : (xs ys : List X₀) → Set (o ⊍ ℓ)
      xs ≈ₘ ys = {e : X₀} → (e ∈ xs) ≅ (e ∈ ys)

      ≡→≈ₘ : {a b : List X₀} → a ≡ b → a ≈ₘ b
      ≡→≈ₘ ≡.refl = record
        { to = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; from = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; inverse-of = record { left-inverse-of = λ _ → ≡.refl ; right-inverse-of = λ _ → ≡.refl } }

      LM : Setoid ℓ (ℓ ⊍ o)
      LM = record
        { Carrier = List (Setoid.Carrier X)
        ; _≈_ = _≈ₘ_
        ; isEquivalence = record { refl = ≅-refl ; sym = λ x → ≅-sym x ; trans = λ x y → ≅-trans x y }
        }

  -- |open import Data.Product using (∃₂)|

  ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
  ListCMHom X Y = MKMSHom (λ F → let g = Π._⟨$⟩_ F in record
    { mor = record
      { _⟨$⟩_ = mapL g
      ; cong = λ {xs} {ys} xs≈ys {y} → {!!}
      }
    ; pres-e = λ {z} → {!!}

    ; pres-* = λ {x} {y} {e} → let g = Π._⟨$⟩_ F in {!!}
     {-
           |Any-map (Setoid._≈_ Y e) g (x ++ y) ⟨≃≃⟩|
           |Any-++ (λ z → (Setoid._≈_ Y e (g z))) x y ⟨≃≃⟩|
           |(sym≃ (Any-map (Setoid._≈_ Y e) g x)) ⊎≃|
           |(sym≃ (Any-map (Setoid._≈_ Y e) g y)) ⟨≃≃⟩|
           |sym≃ (Any-++ (Setoid._≈_ Y e) (mapL g x) (mapL g y))|
     -}
    })
    where
      open Multiset (ListMS Y)
      open CommMonoid (Multiset.commMonoid (ListMS X))
      -- |open Membership X renaming (_∈_ to _∈₁_ ; map-with-∈ to map-with-∈₁)|
      -- |open Membership Y renaming (_∈_ to _∈₂_ ; map-with-∈ to map-with-∈₂)|
\end{code}

    fold : {X : Setoid ℓ o} {B : Set ℓ} →
      let A = Carrier X in
      (A → B → B) → B → Carrier (Multiset X) → B
    fold = foldr

    singleton-map : {A B : Setoid ℓ o} (f : A ⟶ B) {a : Setoid.Carrier A} →
      _≈_ (Multiset B) (singleton {B} (f ⟨$⟩ a)) (map (_⟨$⟩_ f) (singleton {A} a))
    singleton-map {_} {B} f = Setoid.refl (Multiset B)

MultisetF : (ℓ o : Level) → Functor (Setoids ℓ o) (MonoidCat ℓ (ℓ ⊔ o))
MultisetF ℓ o = record
  { F₀ = λ S → commMonoid (ListMS S)
  ; F₁ = λ {X} {Y} f → let F = lift (ListCMHom X Y) f in record { Hom F }
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≈G → {!!}
  }
  where
    open Multiset; open MultisetHom

MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊔ ℓ)) (Forget ℓ (o ⊔ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = singleton (ListMS X)
                                     ; cong = {!!} }
                  ; commute = {!!} }
  ; counit = record
    { η = λ { (MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = {! fold _+_ z !} ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
  where
    open Multiset
    open CommMonoid

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
