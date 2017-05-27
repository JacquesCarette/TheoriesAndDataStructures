%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; IsEquivalence;
  Reflexive; Symmetric; Transitive)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open import Function2         using (_$ᵢ)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)
open import Data.List.Any using (Any; module Membership)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Equiv using (_≃_; id≃; sym≃; trans≃)

\end{code}
%}}}

%{{{ CommMonoid ; Hom
\begin{code}
record CommMonoid {ℓ} {o} : Set (lsuc ℓ ⊔ lsuc o) where  
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

  module ≈ = Setoid setoid

open CommMonoid hiding (_≈_)
infix -666 eq-in
eq-in = CommMonoid._≈_
syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

record Hom {ℓ} {o} (A B : CommMonoid {ℓ} {o}) : Set (ℓ ⊔ o) where
  constructor MkHom
  open CommMonoid A using () renaming (e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B using () renaming (e to e₂; _*_ to _*₂_; _≈_ to _≈₂_)

  field mor    : setoid A ⟶ setoid B
  private mor₀ = Π._⟨$⟩_ mor
  field
    pres-e : mor₀ e₁ ≈₂ e₂
    pres-* : {x y : Carrier A} → mor₀ (x *₁ y)  ≈₂  mor₀ x *₂ mor₀ y

  open Π mor public

open Hom
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.

%}}}

%{{{ MonoidCat ; Forget
\begin{code}
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊔ lsuc o) (o ⊔ ℓ) (ℓ ⊔ o)
MonoidCat ℓ o = record
  { Obj = CommMonoid {ℓ} {o}
  ; _⇒_ = Hom
  ; _≡_ = λ {A} {B} F G → {x : Carrier A} → F ⟨$⟩ x ≈ G ⟨$⟩ x ∶ B
  ; id  = λ {A} → MkHom id (≈.refl A) (≈.refl A)
  ; _∘_ = λ {A} {B} {C} F G → record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  ≈.trans C (cong F (pres-e G)) (pres-e F)
    ; pres-*   =  ≈.trans C (cong F (pres-* G)) (pres-* F)
    }
  ; assoc     = λ {A} {B} {C} {D} {F} {G} {H} {x} → ≈.refl D
  ; identityˡ = λ {A} {B} {F} {x} → ≈.refl B
  ; identityʳ = λ {A} {B} {F} {x} → ≈.refl B
  ; equiv     = λ {A} {B} → record
    { refl  = λ{F} {x} → ≈.refl B 
    ; sym   = λ {F} {G} F≈G {x} → ≈.sym B F≈G
    ; trans = λ {F} {G} {H} F≈G G≈H {x} → ≈.trans B F≈G G≈H
    }
  ; ∘-resp-≡ = λ {A} {B} {C} {F} {F'} {G} {G'} F≈F' G≈G' {x} → ≈.trans C (cong F G≈G') F≈F'
  }
\end{code}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ (o ⊔ ℓ)) (Setoids ℓ (o ⊔ ℓ))
Forget ℓ o = record
  { F₀             =   λ C → record { CommMonoid C }
  ; F₁             =   λ F → record { Hom F }
  ; identity       =   λ {A} → ≈.refl A
  ; homomorphism   =   λ {A} {B} {C} → ≈.refl C
  ; F-resp-≡      =   λ F≈G {x} → F≈G {x}
  }
\end{code}
%}}}

%{{{ Multiset

A “multiset on type X” is a commutative monoid with a to it from |X|.
For now, we make no constraints on the map, however it may be that
future proof obligations will require it to be an injection ---which is reasonable.

\begin{code}
record Multiset {ℓ o : Level} (X : Setoid ℓ o) : Set (lsuc ℓ ⊔ lsuc o) where
  field
    commMonoid : CommMonoid {ℓ} {ℓ ⊔ o}
    singleton : Setoid.Carrier X → CommMonoid.Carrier commMonoid
  open CommMonoid commMonoid public

record MultisetHom {ℓ} {o} {X Y : Setoid ℓ o} (A : Multiset X) (B : Multiset Y) : Set (ℓ ⊔ o) where
  constructor MsHom
  open Multiset A using () renaming (commMonoid to cm₁)
  open Multiset B using () renaming (commMonoid to cm₂)

  field
    cmor : Hom cm₁ cm₂
    map : (X ⟶ Y) → (CommMonoid.setoid cm₁ ⟶ CommMonoid.setoid cm₂)
\end{code}

%}}}

\begin{code}
abstract
  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { commMonoid =
    record
    { setoid     =  LM
    ; e          =  []
    ; _*_        =  _++_
    ; left-unit  =  Setoid.refl LM
    ; right-unit = rightId
    ; assoc      =  {!!}
    ; comm       =  {!!}

    }
    ; singleton = λ x → x ∷ []
    }
    where
      open Membership X

      LM : Setoid ℓ (ℓ ⊔ o)
      LM = record
        { Carrier = List (Setoid.Carrier X)
        ; _≈_ = λ xs ys → {e : Setoid.Carrier X} → e ∈ xs  ≃  e ∈ ys
        ; isEquivalence = record
          { refl  =  id≃
          ; sym   =  λ xs≃ys → sym≃ xs≃ys
          ; trans =  λ xs≈ys ys≈zs → trans≃ xs≈ys ys≈zs
          }
        }

      F : ∀ {xs e} → Any (X Setoid.≈ e) (xs ++ []) → Any (X Setoid.≈ e) xs
      F {[]} ()
      F {x ∷ xs} (Any.here px) = Any.here px
      F {x ∷ xs} (Any.there ar) = Any.there (F ar)

      F˘ : ∀ {xs e} → Any (X Setoid.≈ e) xs → Any (X Setoid.≈ e) (xs ++ [])
      F˘ {[]} ()
      F˘ {x ∷ xs} (Any.here px) = Any.here px
      F˘ {x ∷ xs} (Any.there eq) = Any.there (F˘ eq)

      FF˘≈Id : ∀ {xs e} (pf : Any (X Setoid.≈ e) xs) → F (F˘ pf) ≡ pf
      FF˘≈Id {[]} ()
      FF˘≈Id {x ∷ xs} (Any.here px) = ≡.refl
      FF˘≈Id {x ∷ xs} (Any.there pf) = ≡.cong Any.there (FF˘≈Id pf)

      F˘F≈Id : ∀ {xs e} (pf : Any (X Setoid.≈ e) (xs ++ [])) → F˘ {xs} {e} (F pf) ≡ pf
      F˘F≈Id {[]} ()
      F˘F≈Id {x ∷ xs} (Any.here px) = ≡.refl
      F˘F≈Id {x ∷ xs} (Any.there pf) = ≡.cong Any.there (F˘F≈Id {xs} pf)

      rightId : ∀ {xs x} → Any (Setoid._≈_ X x) (xs ++ []) ≃ Any (Setoid._≈_ X x) xs
      rightId {xs} {x} = F , Equiv.qinv F˘ FF˘≈Id F˘F≈Id

  ListCMHom : ∀ {ℓ} {o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
  ListCMHom X Y = MsHom {!!}
         (λ f → record { _⟨$⟩_ = mapL (Π._⟨$⟩_ f)
                       ; cong = λ i≈j → {!!} })
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
  ; F₁ = λ {X} {Y} f → MkHom (MultisetHom.map (ListCMHom X Y) f)
               {!!} {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≈G → {!!}
  }
  where open Multiset

MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊔ ℓ)) (Forget ℓ (o ⊔ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = {!!} -- singleton (ListMS X)
                                     ; cong = {!!} }
                  ; commute = {!!} } -- singleton-map }
  ; counit = record
    { η = λ { X@(MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = {! fold _+_ z !} ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = {!!}
  ; zag = {!!}
  }
  where open Multiset

\end{code}

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
