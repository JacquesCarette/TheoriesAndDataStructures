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
    pres-* : {x y : Carrier A} → mor₀ (x *₁ y) ≈₂ mor₀ x  *₂  mor₀ y

  open Π mor public

open Hom
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.

%}}}

%{{{ MonoidCat
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
%}}}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ (o ⊔ ℓ)) (Setoids ℓ (o ⊔ ℓ))
Forget ℓ o = record
  { F₀ = λ C → record { CommMonoid C }
  ; F₁ = λ F → record { Hom F }
  ; identity = λ {A} → Setoid.refl (setoid A)
  ; homomorphism = λ {_} {_} {C} → Setoid.refl (setoid C)
  ; F-resp-≡ = λ F≈G {x} → F≈G {x}
  }
  -- equivalent functions aren't necessarily extensionally-identical functions

record Multiset {ℓ o : Level} (X : Setoid ℓ o) : Set (lsuc ℓ ⊔ lsuc o) where
  field
    cm : CommMonoid {ℓ} {ℓ ⊔ o}
  open CommMonoid cm public
  field
    singleton : Setoid.Carrier X → CommMonoid.Carrier cm

abstract
  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { cm = MkCommMon LM [] _++_ (Setoid.refl LM) {!!} {!!} {!!}
    ; singleton = λ x → x ∷ [] }
    where
      private
        Z = List (Setoid.Carrier X)
        open Membership X

      LM : Setoid ℓ (ℓ ⊔ o)
      LM = record
        { Carrier = Z
        ; _≈_ = λ m₁ m₂ → ∀ x → (x ∈ m₁) ≃ (x ∈ m₂)
        ; isEquivalence = record
          { refl = λ _ → id≃
          ; sym = λ s x → sym≃ (s x)
          ; trans = λ s t x → trans≃ (s x) (t x) } }
{-
module _ {ℓ o : Level} where
  infixl 8 _+ₘ_
  infix  4 _≈ₘ_

  open Setoid
  
  abstract
    map : {A B : Setoid ℓ o} → (Carrier A → Carrier B) → Carrier (Multiset A) → Carrier (Multiset B)
    map = mapL

    singleton : {X : Setoid ℓ o} → Carrier X → Carrier (Multiset X)
    singleton x = x ∷ []

    fold : {X : Setoid ℓ o} {B : Set ℓ} →
      let A = Carrier X in
      (A → B → B) → B → Carrier (Multiset X) → B
    fold = foldr
    
    singleton-map : {A B : Setoid ℓ o} (f : A ⟶ B) {a : Setoid.Carrier A} →
      _≈_ (Multiset B) (singleton {B} (f ⟨$⟩ a)) (map (_⟨$⟩_ f) (singleton {A} a))
    singleton-map {_} {B} f = Setoid.refl (Multiset B)

    _+ₘ_ : {X : Setoid ℓ o} → Carrier (Multiset X) → Carrier (Multiset X) → Carrier (Multiset X)
    m₁ +ₘ m₂ = m₁ ++ m₂

    left0 : {X : Setoid ℓ o} {m : Carrier (Multiset X)} → _≈_ (Multiset X) (0ₘ +ₘ m) m
    left0 {X} = Setoid.refl (Multiset X)

    right0 : {X : Setoid ℓ o} {m : Carrier (Multiset X)} → _≈_ (Multiset X) (m +ₘ 0ₘ) m
    right0 {X} = {!!}
      where open Membership (Multiset X)

MSMonoid : {ℓ o : Level} → Setoid ℓ o → CommMonoid {ℓ} {o ⊔ ℓ}
MSMonoid X = MkCommMon (Multiset X) 0ₘ _+ₘ_ left0 right0 {!!} {!!}
-}

MultisetF : (ℓ o : Level) → Functor (Setoids ℓ o) (MonoidCat ℓ (ℓ ⊔ o))
MultisetF ℓ o = record
  { F₀ = λ S → cm (ListMS S)
  ; F₁ = λ f → MkHom (record { _⟨$⟩_ = {!!} -- map (_⟨$⟩_ f)
                             ; cong = λ i≈j → {!!} })
               {!!} {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≈G → {!!}
  }
  where open Multiset

MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊔ ℓ)) (Forget ℓ (o ⊔ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = singleton (ListMS X)
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
