%{{{ Imports
\begin{code}
module Structures.CommMonoidTerm where

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

open import Equiv using (_≃_; id≃ ; sym≃ ; trans≃ ; _⊎≃_ ; _⟨≃≃⟩_ ; ≃-setoid ; ≃IsEquiv)
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

  module ≈ = Setoid setoid

open CommMonoid hiding (_≈_)
infix -666 eq-in
eq-in = CommMonoid._≈_
syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

record Hom {ℓ} {o} (A B : CommMonoid {ℓ} {o}) : Set (ℓ ⊍ o) where
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
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (ℓ ⊍ o)
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
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ (o ⊍ ℓ)) (Setoids ℓ (o ⊍ ℓ))
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

module _ {ℓ o : Level} (X : Setoid ℓ o) where

  X₀ = Setoid.Carrier X

  infix 5 _∙_
  infix 3 _≈ₜ_

  -- syntax of monoids over X
  data Term : Set ℓ where
    inj : X₀ → Term
    ε   : Term
    _∙_ : Term → Term → Term

  open Setoid X using () renaming (_≈_ to _≈ₓ_)

  data _≈ₜ_ : Term → Term → Set (ℓ ⊍ o) where
    -- This is an equivalence relation
    ≈ₜ-refl : {t : Term} → t ≈ₜ t
    ≈ₜ-sym  : {s t : Term} → s ≈ₜ t → t ≈ₜ s
    ≈ₜ-trans : {s t u : Term} → s ≈ₜ t → t ≈ₜ u → s ≈ₜ u
    -- where the commutative monoid laws hold
    ∙-cong : {s t u v : Term} → s ≈ₜ t → u ≈ₜ v → s ∙ u ≈ₜ t ∙ v
    ∙-assoc : {s t u : Term} → (s ∙ t) ∙ u ≈ₜ s ∙ (t ∙ u)
    ∙-comm  : {s t : Term} → s ∙ t ≈ₜ t ∙ s
    ∙-leftId : {s : Term} → ε ∙ s ≈ₜ s
    ∙-rightId : {s : Term} → s ∙ ε ≈ₜ s
    -- and it contains all equailities of the underlying setoid
    embed : {x y : X₀} → x ≈ₓ y → inj x ≈ₜ inj y
      --
      -- This means that we do NOT have unique proofs.
      -- For example, |inj x ≈ₜ inj x| can be proven in two ways: |≈ₜ-refl| or |embed ≈ₓ-refl|.
      --
      -- This may bite us in the butt; not necessarily though...

  LM : Setoid _ _
  LM = record
          { Carrier = Term
          ; _≈_ = _≈ₜ_
          ; isEquivalence = record
            { refl  =  ≈ₜ-refl
            ; sym   =  ≈ₜ-sym
            ; trans =  ≈ₜ-trans
            }
          }

  ListMS : Multiset X
  ListMS  = record
      { commMonoid = record
          { setoid     =  LM
          ; e          =  ε
          ; _*_        =  _∙_
          ; left-unit  =  ∙-leftId
          ; right-unit = ∙-rightId
          ; assoc      =  ∙-assoc
          ; comm       =  ∙-comm
          }
      ; singleton = inj
      }
      where

-- Term is functorial
module _ {ℓ o : Level} {X Y : Setoid ℓ o} where
  term-lift : (X ⟶ Y) → Term X → Term Y
  term-lift F (inj x) = inj (Π._⟨$⟩_ F x)
  term-lift F ε = ε
  term-lift F (s ∙ t) = term-lift F s ∙ term-lift F t

  term-cong : (F : X ⟶ Y) → {s t : Term X} → _≈ₜ_ X s t → _≈ₜ_ Y (term-lift F s) (term-lift F t)
  term-cong F ≈ₜ-refl = ≈ₜ-refl
  term-cong F (≈ₜ-sym eq) = ≈ₜ-sym (term-cong F eq)
  term-cong F (≈ₜ-trans eq eq₁) = ≈ₜ-trans (term-cong F eq) (term-cong F eq₁)
  term-cong F (∙-cong eq eq₁) = ∙-cong (term-cong F eq) (term-cong F eq₁)
  term-cong F ∙-assoc = ∙-assoc
  term-cong F ∙-comm = ∙-comm
  term-cong F ∙-leftId = ∙-leftId
  term-cong F ∙-rightId = ∙-rightId
  term-cong F (embed x≈y) = embed (Π.cong F x≈y)

  -- Setoid morphism
  term : (F : X ⟶ Y) → (LM X) ⟶ (LM Y)
  term F = record { _⟨$⟩_ = term-lift F ; cong = term-cong F }

-- proofs that it is functorial; must pattern-match and expand.  This is the 'cost' of
-- going with a term language. Can't put them in the above module either, because
-- the implicit premises are different.
term-id : ∀ {ℓ o} {X : Setoid ℓ o} {x : Term X} → term-lift id x ≈ x ∶ commMonoid (ListMS X)
term-id {x = inj x} = ≈ₜ-refl
term-id {x = ε} = ≈ₜ-refl
term-id {x = x ∙ x₁} = ∙-cong (term-id {x = x}) (term-id {x = x₁})

term-Hom : ∀ {ℓ o} {X Y Z : Setoid ℓ o} {f : X ⟶ Y} {g : Y ⟶ Z} {x : Term X} →
  (term-lift (g ∘ f) x) ≈ (term-lift g (term-lift f x)) ∶ commMonoid (ListMS Z)
term-Hom {x = inj x} = ≈ₜ-refl
term-Hom {x = ε} = ≈ₜ-refl
term-Hom {x = x ∙ x₁} = ∙-cong term-Hom term-Hom

term-resp-F : ∀ {ℓ o} {X Y : Setoid ℓ o} {f g : X ⟶ Y} {x : Term X} →
  ({z : Setoid.Carrier X} → Setoid._≈_ Y (f Π.⟨$⟩ z) (g Π.⟨$⟩ z)) → term-lift f x ≈ term-lift g x ∶ commMonoid (ListMS Y)
term-resp-F {x = inj x} F = embed F
term-resp-F {x = ε} F = ≈ₜ-refl
term-resp-F {x = x ∙ x₁} F = ∙-cong (term-resp-F F) (term-resp-F F)

ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
ListCMHom X Y = MKMSHom (λ F → record
      { mor      =   term F
      ; pres-e   =   ≈ₜ-refl
      ; pres-*   =   ≈ₜ-refl
      })

-- We have a fold over the syntax
fold : ∀ {ℓ o} {X : Setoid ℓ o} {B : Set ℓ} →
  let A = Setoid.Carrier X in
  (A → B) → B → (B → B → B) → Term X → B
fold f b g (inj x) = f x
fold f b g ε = b
fold f b g (m ∙ m₁) = g (fold f b g m) (fold f b g m₁)

-- and an induction principle
ind : ∀ {ℓ o p} → {X : Setoid ℓ o} (P : Term X → Set p) →
  ((x : Setoid.Carrier X) → P (inj x)) → P ε →
  ({t₁ t₂ : Term X} → P t₁ → P t₂ → P (t₁ ∙ t₂)) →
  (t : Term X) → P t
ind P base e₁ bin (inj x) = base x
ind P base e₁ bin ε = e₁
ind P base e₁ bin (t ∙ t₁) = bin (ind P base e₁ bin t) (ind P base e₁ bin t₁)

-- but the above can be really hard to use in some cases, such as:

fold-resp-≈ : ∀ {ℓ o}
  (CM : CommMonoid {ℓ} {o}) → let X = CommMonoid.setoid CM in {i j : Term X} →
  (i ≈ j ∶ commMonoid (ListMS X)) → (fold id₀ (e CM) (_*_ CM) i) ≈ (fold id₀ (e CM) (_*_ CM) j) ∶ CM
fold-resp-≈ cm ≈ₜ-refl = CommMonoid.refl cm
fold-resp-≈ cm (≈ₜ-sym pf) = CommMonoid.sym cm (fold-resp-≈ cm pf) 
fold-resp-≈ cm (≈ₜ-trans pf pf₁) = CommMonoid.trans cm (fold-resp-≈ cm pf) (fold-resp-≈ cm pf₁)
fold-resp-≈ cm (∙-cong pf pf₁) = {!!} -- and this is where it all falls apart!!
fold-resp-≈ cm ∙-assoc = CommMonoid.assoc cm
fold-resp-≈ cm ∙-comm = CommMonoid.comm cm
fold-resp-≈ cm ∙-leftId = CommMonoid.left-unit cm
fold-resp-≈ cm ∙-rightId = CommMonoid.right-unit cm
fold-resp-≈ cm (embed x₁) = x₁
\end{code}

\begin{code}
MultisetF : (ℓ o : Level) → Functor (Setoids ℓ o) (MonoidCat ℓ (ℓ ⊍ o))
MultisetF ℓ o = record
  { F₀ = λ S → commMonoid (ListMS S)
  ; F₁ = λ {X} {Y} f → let F = lift (ListCMHom X Y) f in record { Hom F }
  ; identity = term-id
  ; homomorphism = term-Hom
  ; F-resp-≡ = λ F≈G → term-resp-F F≈G
  }

MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊍ ℓ)) (Forget ℓ (o ⊍ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = singleton (ListMS X)
                                     ; cong = embed }
                  ; commute = λ f → ≈ₜ-refl }
  ; counit = record
    { η = λ { X@(MkCommMon A z _+_ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = fold id₀ z _+_
                        ; cong = fold-resp-≈ X })
                (Setoid.refl A)
                ( λ {a} {b} → {!!} ) }
    ; commute = λ f → {!!}
    }
  ; zig = {!!}
  ; zag = λ {CM} → CommMonoid.refl CM
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
