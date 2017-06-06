%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; IsEquivalence;
  Reflexive; Symmetric; Transitive)

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

\begin{code}

open import Function using (flip)
open import Function.Inverse using () renaming
  (Inverse to _≅_
  ; id to ≅-refl
  ; sym to ≅-sym
  )

≅-trans : {a b c ℓa ℓb ℓc : Level} {A : Setoid a ℓa} {B : Setoid b ℓb} {C : Setoid c ℓc}
        → A ≅ B → B ≅ C → A ≅ C  
≅-trans = flip Function.Inverse._∘_

infix  3 _∎
infixr 2 _≅⟨_⟩_

_≅⟨_⟩_ : {x y z ℓx ℓy ℓz : Level} (X : Setoid x ℓx) {Y : Setoid y ℓy} {Z : Setoid z ℓz} 
      →  X ≅ Y → Y ≅ Z → X ≅ Z
X ≅⟨ X≅Y ⟩ Y≅Z = ≅-trans X≅Y Y≅Z

_∎ : {x ℓx : Level} (X : Setoid x ℓx) → X ≅ X
X ∎ = ≅-refl

record _≋_ {a b ℓa ℓb} {A : Setoid a ℓa} {B : Setoid b ℓb} (eq₁ eq₂ : A ≅ B) : Set (a ⊍ b ⊍ ℓa ⊍ ℓb) where
  constructor eq
  open _≅_
  open Setoid A using () renaming (_≈_ to _≈₁_)
  open Setoid B using () renaming (_≈_ to _≈₂_)
  open Π
  field
    to≈ :   ∀ x → to eq₁   ⟨$⟩ x ≈₂ to eq₂   ⟨$⟩ x
    from≈ : ∀ x → from eq₁ ⟨$⟩ x ≈₁ from eq₂ ⟨$⟩ x

module _ {a b ℓa ℓb} {A : Setoid a ℓa} {B : Setoid b ℓb} where
  id≋ : {x : A ≅ B} → x ≋ x
  id≋ = eq (λ _ → Setoid.refl B) (λ _ → Setoid.refl A)

  sym≋ : {i j : A ≅ B} → i ≋ j → j ≋ i
  sym≋ (eq to≈ from≈) = eq (λ x → Setoid.sym B (to≈ x)) (λ x → Setoid.sym A (from≈ x))

  trans≋ : {i j k : A ≅ B} → i ≋ j → j ≋ k → i ≋ k
  trans≋ (eq to≈₀ from≈₀) (eq to≈₁ from≈₁) = eq (λ x → Setoid.trans B (to≈₀ x) (to≈₁ x)) (λ x → Setoid.trans A (from≈₀ x) (from≈₁ x))
  
_≅S_ : ∀ {a b ℓa ℓb} (A : Setoid a ℓa) (B : Setoid b ℓb) → Setoid (ℓb ⊍ (ℓa ⊍ (b ⊍ a))) (ℓb ⊍ (ℓa ⊍ (b ⊍ a)))
_≅S_ A B = record
  { Carrier = A ≅ B
  ; _≈_ = _≋_
  ; isEquivalence = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ } }

_≈S_ : ∀ {a ℓa} {A : Setoid a ℓa} → (e₁ e₂ : Setoid.Carrier A) → Setoid ℓa {!!}
_≈S_ {A = A} e₁ e₂ = let open Setoid A renaming (_≈_ to _≈ₛ_) in
  record { Carrier = e₁ ≈ₛ e₂ ; _≈_ = λ eq₁ eq₂ → {!eq₁ ≅ eq₂!} ; isEquivalence = {!!} }

SSetoid : ∀ {ℓ o} → Setoid (lsuc o ⊍ lsuc ℓ) (o ⊍ ℓ)
SSetoid {ℓ} {o} = record
  { Carrier = Setoid ℓ o
  ; _≈_ = _≅_
  ; isEquivalence = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans } }
  
-- Setoid based variant of Any.  The definition is 'wrong' in the sense the target of P
-- really should be a 'Setoid of types', and not one necessarily with ≡ as its equivalence.
-- We really need an 'interpretable setoid', i.e. one which has ⟦_⟧ : Carrier → Set p,
-- as I don't know how to otherwise say that the target Setoid must have a type as a Carrier.
data Some₀ {a ℓa} {A : Setoid a ℓa} (P : A ⟶ SSetoid {a} {ℓa}) : List (Setoid.Carrier A) → Set (a ⊍ ℓa) where
  here  : ∀ {x xs} (px  : Setoid.Carrier (P Π.⟨$⟩ x)) → Some₀ P (x ∷ xs)
  there : ∀ {x xs} (pxs : Some₀ P xs) → Some₀ P (x ∷ xs)

module Membership {a ℓ} (S : Setoid a ℓ) where
  private
    open module  S = Setoid S renaming (Carrier to A; _≈_ to _≈ₛ_)

  -- List membership.

  infix 4 _∈_

  setoid≈ : A → S ⟶ SSetoid {{!!}} {{!!}}
  setoid≈ a = record { _⟨$⟩_ = λ b → {!a ≈ₛ b!} ; cong = {!!} }
  
  _∈_ : A → List A → Set _
  x ∈ xs = Some₀ {! setoid≈ x !} xs

Some : {a ℓa : Level} {A : Setoid a ℓa} (P : A ⟶ SSetoid) → List (Setoid.Carrier A) → Setoid (a ⊍ ℓa) ℓa
Some {a} {ℓa} {A} P xs = record
  { Carrier = Some₀ P xs
  ; _≈_ = {!!}
  ; isEquivalence = {!!}
  }

≡→≅ : {a ℓa : Level} {A : Setoid a ℓa} {P : A ⟶ SSetoid} {xs ys : List (Setoid.Carrier A)} →
  xs ≡ ys → Some P xs ≅ Some P ys 
≡→≅ {A = A} ≡.refl =
  let open Setoid A renaming (refl to refl≈) in
  record { to = id ; from = id ; inverse-of = record { left-inverse-of = λ _ → refl≈ ; right-inverse-of = λ _ → refl≈ } }

open import RATH using (_⊎⊎_) -- setoid sum

{-
abstract
  -- RATH-Agda library import
  -- open import Relation.Binary.Setoid.Sum -- previously lived in RATH's Data.Sum.Setoid

  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { commMonoid = record
        { setoid     =  LM
        ; e          =  []
        ; _*_        =  _++_
        ; left-unit  =  Setoid.refl LM
        ; right-unit = λ {xs} → {!!} -- ≡→≅ (proj₂ ++.identity xs)
        ; assoc      =  λ {xs} {ys} {zs} → {!!} -- ≡→≅ (++.assoc xs ys zs)
        ; comm       =  λ {xs} {ys} {z} →
          z ∈ xs ++ ys       ≃⟨ sym≃ {!!} ⟩ -- ≅-sym Any-additive ⟩
          (z ∈ xs ⊎ z ∈ ys)  ≃⟨ {!⊎.comm _ _!} ⟩ -- ⊎.comm _ _                       ⟩
          (z ∈ ys ⊎ z ∈ xs)  ≃⟨ {!!} ⟩ -- Any-additive                     ⟩
          z ∈ ys ++ xs  ◻
        ; _⟨*⟩_ = λ x≈y z≈w → {!!} 
        }
    ; singleton = λ x → x ∷ []
    }
    where
      open import Algebra using (Monoid)
      open import Data.List using (monoid)
      module ++ = Monoid (monoid (Setoid.Carrier X))      

      X₀ = Setoid.Carrier X

      _≈ₘ_ : (xs ys : List (Setoid.Carrier X)) → Set (o ⊍ ℓ)
      xs ≈ₘ ys = {e : Setoid.Carrier X} → (e ∈ xs) ≃ (e ∈ ys)

      LM : Setoid ℓ (ℓ ⊍ o)
      LM = record
        { Carrier = List (Setoid.Carrier X)
        ; _≈_ = _≈ₘ_
        ; isEquivalence = record
          { refl  =  id≃
          ; sym   =  λ x≃y → sym≃ x≃y
          ; trans =  λ xs≃ys ys≃zs → trans≃ xs≃ys ys≃zs
          }
        }

  -- open import Data.Product using (∃₂)

  ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
  ListCMHom X Y = MKMSHom (λ F → record
    { mor = record
      { _⟨$⟩_ = λ xs → {!!} -- map-with-∈₁ xs (λ {x} _ → Π._⟨$⟩_ F x) -- map-with-∈₁ {!map-with-∈₁ ?!} -- mapL (Π._⟨$⟩_ F)
      ; cong = λ {xs} {ys} xs≈ys {e} →
        let 𝔣 : {x : Setoid.Carrier X} → {!!} -- x ∈₁ xs → Setoid.Carrier Y
            𝔣 = λ {x} _ → Π._⟨$⟩_ F x

            𝔣′ : {x : Setoid.Carrier X} → {!!} -- x ∈₁ ys → Setoid.Carrier Y
            𝔣′ = λ {x} _ → Π._⟨$⟩_ F x

            f = Π._⟨$⟩_ F
        in {!!}
      {-
      e ∈₂ (map-with-∈₁ xs 𝔣) ≅⟨ ≅-sym {!map-with-∈-≅!} ⟩
      ∃₂ {A = Setoid.Carrier X} {B = λ x → x ∈₁ xs} (λ x x∈xs → Setoid._≈_ Y e (f x))   ≅⟨ {! crux !} ⟩
      ∃₂ {A = Setoid.Carrier X} {B = λ x → x ∈₁ ys} (λ x x∈ys → Setoid._≈_ Y e (f x))   ≅⟨ {!!} ⟩      
      e ∈₂ (map-with-∈₁ ys 𝔣′) ∎
      -}
      }
    ; pres-e = ≅-refl
    ; pres-* = λ {x} {y} {e} → let g = Π._⟨$⟩_ F in {!!}
     {-
           Any-map (Setoid._≈_ Y e) g (x ++ y) ⟨≃≃⟩
           Any-++ (λ z → (Setoid._≈_ Y e (g z))) x y ⟨≃≃⟩ 
           (sym≃ (Any-map (Setoid._≈_ Y e) g x)) ⊎≃
           (sym≃ (Any-map (Setoid._≈_ Y e) g y)) ⟨≃≃⟩
           sym≃ (Any-++ (Setoid._≈_ Y e) (mapL g x) (mapL g y))
     -}
    })
    where
      open Multiset (ListMS Y)
      open CommMonoid (Multiset.commMonoid (ListMS X))
      -- open Membership X renaming (_∈_ to _∈₁_ ; map-with-∈ to map-with-∈₁)
      -- open Membership Y renaming (_∈_ to _∈₂_ ; map-with-∈ to map-with-∈₂)
-}
\end{code}

{-
    fold : {X : Setoid ℓ o} {B : Set ℓ} →
      let A = Carrier X in
      (A → B → B) → B → Carrier (Multiset X) → B
    fold = foldr
    
    singleton-map : {A B : Setoid ℓ o} (f : A ⟶ B) {a : Setoid.Carrier A} →
      _≈_ (Multiset B) (singleton {B} (f ⟨$⟩ a)) (map (_⟨$⟩_ f) (singleton {A} a))
    singleton-map {_} {B} f = Setoid.refl (Multiset B)
-}

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
    { η = λ { X@(MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = {! fold _+_ z !} ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
  where
    open Multiset
    open CommMonoid
    


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
