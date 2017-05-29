%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
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
open import Data.List.Any using (Any; module Membership)

open import Forget
open import EqualityCombinators
open import DataProperties

open import Equiv using (_≃_; id≃; sym≃; trans≃; _⊎≃_ ; _⟨≃≃⟩_ ; ≅-setoid)
open import TypeEquiv

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
  ; _∘_ = λ {_} {_} {C} F G → record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  ≈.trans C (cong F (pres-e G)) (pres-e F)
    ; pres-*   =  ≈.trans C (cong F (pres-* G)) (pres-* F)
    }
  ; assoc     = λ { {D = D} → ≈.refl D}
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

open Multiset
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure.

\begin{code}
record MultisetHom {ℓ} {o} {X Y : Setoid ℓ o} (A : Multiset X) (B : Multiset Y) : Set (ℓ ⊔ o) where
  constructor MKMSHom
  field
    lift : (X ⟶ Y) → Hom (commMonoid A) (commMonoid B)

open MultisetHom
\end{code}

%}}}

%{{{ ≡→≃-Any ; Any-∷ ; Any-⊥ ; Any-++ ; Any-map

Lots of lemmas about |Any|
\begin{code}
≡→≃-Any : {a p : Level} {A : Set a} {P : A → Set p} {xs ys : List A} → xs ≡ ys → Any P xs ≃ Any P ys 
≡→≃-Any ≡.refl = id₀ , Equiv.qinv id₀ ≐-refl ≐-refl

-- this means reasoning with Any simpler
Any-∷ : {a p : Level} {A : Set a} {P : A → Set p} {x : A} {xs : List A} →
  Any P (x ∷ xs) ≃ (P x ⊎ Any P xs)
Any-∷ {a} {p} {A} {P} {x} {xs} = fwd , Equiv.qinv bwd f∘b b∘f
  where
    fwd : Any P (x ∷ xs) → P x ⊎ Any P xs
    fwd (Any.here px) = inj₁ px
    fwd (Any.there z) = inj₂ z

    bwd : P x ⊎ Any P xs → Any P (x ∷ xs)
    bwd (inj₁ x₁) = Any.here x₁
    bwd (inj₂ y) = Any.there y

    f∘b : fwd ⊚ bwd ≐ id₀
    f∘b (inj₁ x₁) = ≡.refl
    f∘b (inj₂ y) = ≡.refl

    b∘f : bwd ⊚ fwd ≐ id₀
    b∘f (Any.here px) = ≡.refl
    b∘f (Any.there x₁) = ≡.refl

Any-⊥ : {a p : Level} {A : Set a} {P : A → Set p} → _≃_ {a ⊔ p} {p} (Any P []) ⊥
Any-⊥ = (λ {()}) , Equiv.qinv (λ {()}) (λ {()}) (λ {()})

Any-++ : {a p : Level} {A : Set a} (P : A → Set p) (xs ys : List A) →
  Any P (xs ++ ys) ≃ (Any P xs ⊎ Any P ys)
Any-++ P [] ys = (uniti₊equiv {A = Any P ys}) ⟨≃≃⟩ (sym≃ Any-⊥ ⊎≃ id≃)
Any-++ P (x ∷ xs) ys = Any-∷ ⟨≃≃⟩ (id≃ ⊎≃ Any-++ P xs ys) ⟨≃≃⟩
  assocl₊equiv ⟨≃≃⟩ (sym≃ Any-∷ ⊎≃ id≃)

Any-map : {a b p : Level} {A : Set a} {B : Set b} (P : B → Set p)
  (f : A → B) (xs : List A) → Any P (mapL f xs) ≃ Any (P ⊚ f) xs
Any-map P f [] = Any-⊥ ⟨≃≃⟩ (sym≃ Any-⊥)
Any-map P f (x ∷ xs) = Any-∷ ⟨≃≃⟩ id≃ ⊎≃ Any-map P f xs ⟨≃≃⟩ sym≃ Any-∷
\end{code}

%}}}

\begin{code}
abstract

  open import Relation.Binary.SetoidReasoning

  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { commMonoid = record
        { setoid     =  LM
        ; e          =  []
        ; _*_        =  _++_
        ; left-unit  =  Setoid.refl LM
        ; right-unit = λ {x} → ≡→≃-Any (proj₂ ++.identity x)
        ; assoc      =  λ {xs} {ys} {zs} → ≡→≃-Any (++.assoc xs ys zs)
        ; comm       =  λ {xs} {ys} {z} → begin⟨ ≅-setoid ⟩
          z ∈ xs ++ ys     ≈⟨ Any-++ _ _ _ ⟩
          z ∈ xs ⊎ z ∈ ys ≈⟨ swap₊equiv ⟩
          z ∈ ys ⊎ z ∈ xs ≈⟨ sym≃ (Any-++ _ _ _) ⟩
          z ∈ ys ++ xs     ∎
        }
    ; singleton = λ x → x ∷ []
    }
    where
      open Membership X

      open import Algebra using (Monoid)
      open import Data.List using (monoid)
      module ++ = Monoid (monoid (Setoid.Carrier X))

      _≈ₘ_ : (xs ys : List (Setoid.Carrier X)) → Set (ℓ ⊔ o)
      xs ≈ₘ ys = {e : Setoid.Carrier X} → e ∈ xs  ≃  e ∈ ys
      
      LM : Setoid ℓ (ℓ ⊔ o)
      LM = record
        { Carrier = List (Setoid.Carrier X)
        ; _≈_ = _≈ₘ_
        ; isEquivalence = record
          { refl  =  id≃
          ; sym   =  λ xs≃ys → sym≃ xs≃ys
          ; trans =  λ xs≈ys ys≈zs → xs≈ys ⟨≃≃⟩ ys≈zs
          }
        }

  ListCMHom : ∀ {ℓ} {o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
  ListCMHom X Y = MKMSHom (λ F → record
    { mor = record
      { _⟨$⟩_ = mapL (Π._⟨$⟩_ F)
      ; cong = λ {xs} {ys} xs≈ys {e} → {!!}
      }
    ; pres-e = id≃
    ; pres-* = λ {x} {y} {e} → let g = Π._⟨$⟩_ F in 
           Any-map (Setoid._≈_ Y e) g (x ++ y) ⟨≃≃⟩
           Any-++ (λ z → (Setoid._≈_ Y e (g z))) x y ⟨≃≃⟩ 
           (sym≃ (Any-map (Setoid._≈_ Y e) g x)) ⊎≃
           (sym≃ (Any-map (Setoid._≈_ Y e) g y)) ⟨≃≃⟩
           sym≃ (Any-++ (Setoid._≈_ Y e) (mapL g x) (mapL g y))
    })
    where
      open Multiset (ListMS Y)
      open CommMonoid (Multiset.commMonoid (ListMS X))
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
