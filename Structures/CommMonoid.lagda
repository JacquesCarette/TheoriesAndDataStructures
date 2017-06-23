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
open import Relation.Binary.Sum -- using (_⊎-setoid_)

open import Forget
open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp
open import Some

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
          z ∈ xs ++ ys        ≅⟨ ≅-sym (++≅ {P = setoid≈ z}) ⟩
          (z ∈ xs ⊎⊎ z ∈ ys)  ≅⟨ ⊎⊎-comm ⟩
          (z ∈ ys ⊎⊎ z ∈ xs)  ≅⟨ ++≅ {P = setoid≈ z}⟩
          z ∈ ys ++ xs  ∎
        ; _⟨*⟩_ = λ {x} {y} {z} {w} x≈y z≈w {t} →
           t ∈ x ++ z        ≅⟨ ≅-sym (++≅ {P = setoid≈ t}) ⟩
          (t ∈ x ⊎⊎ t ∈ z)   ≅⟨ x≈y ⊎⊎₁ z≈w ⟩
          (t ∈ y ⊎⊎ t ∈ w)   ≅⟨ ++≅ {P = setoid≈ t}⟩
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

      _≈ₘ_ : (xs ys : List X₀) → Set (o ⊍ ℓ)
      xs ≈ₘ ys = {e : X₀} → (e ∈ xs) ≅ (e ∈ ys)

      ≡→≈ₘ : {a b : List X₀} → a ≡ b → a ≈ₘ b
      ≡→≈ₘ ≡.refl = record
        { to = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; from = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; inverse-of = record { left-inverse-of = λ _ → ≋-refl ; right-inverse-of = λ _ → ≋-refl } }

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
      ; cong = λ {xs} {ys} xs≈ys {y} →
      y ∈ mapL g xs           ≅⟨ ≅-sym (map≅ {P = setoid≈ y} {F}) ⟩
      Some (setoid≈ y ∘ F) xs ≅⟨ Some-cong {P = setoid≈ y ∘ F} xs≈ys ⟩
      Some (setoid≈ y ∘ F) ys ≅⟨ map≅ {P = setoid≈ y} {F} ⟩
      y ∈ mapL g ys ∎
      }
    ; pres-e = λ {z} →
      z ∈ []     ≅⟨ ≅-sym (⊥≅Some[] {P = setoid≈ z}) ⟩
      ⊥⊥         ≅⟨ ⊥≅Some[] {P = setoid≈ z} ⟩
      (z ∈ zero) ∎

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
      -- open Multiset (ListMS Y)
      open CommMonoid (Multiset.commMonoid (ListMS Y)) renaming (e to zero)
      open Membership Y
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
