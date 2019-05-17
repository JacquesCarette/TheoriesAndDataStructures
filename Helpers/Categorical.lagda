\section{Categorical -- material taken from copumkin's library to make our development self-contained}

\begin{code}
{-# OPTIONS --irrelevant-projections #-}

module Helpers.Categorical where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)
open import Relation.Binary using (Setoid ; Rel ; IsEquivalence)
open import Data.List using ()

open import Helpers.Function2
import Relation.Binary.PropositionalEquality as ≡ ; open ≡ using () renaming (_≡_ to _≣_)
open import Helpers.DataProperties using (_⊎_)

-- open import Categories.Category using (Category; module Category)
record Category (o ℓ e : Level) : Set (lsuc (o ⊍ ℓ ⊍ e)) where

  infix  4 _≡_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    {_≡_} : ∀ {A B} → Rel (A ⇒ B) e

    {id}  : ∀ {A} → (A ⇒ A)
    {_∘_} : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    .{assoc}     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    .{identityˡ} : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    .{identityʳ} : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    .{equiv}     : ∀ {A B} → IsEquivalence (_≡_ {A} {B})
    .{∘-resp-≡}  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

  .hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier = A ⇒ B
    ; _≈_ = _≡_
    ; isEquivalence = equiv
    }


  infixr 4 _⟨≈≈⟩_ _⟨≈≈˘⟩_

  ._⟨≈≈⟩_ : ∀ {A B} → ∀ {f g h : A ⇒ B} → f ≡ g → g ≡ h → f ≡ h
  _⟨≈≈⟩_ {A} {B} = IsEquivalence.trans (equiv {A} {B})

  ._⟨≈≈˘⟩_ : ∀ {A B} → ∀ {f g h : A ⇒ B} → f ≡ g → h ≡ g → f ≡ h
  _⟨≈≈˘⟩_ f≈g h≈g = f≈g ⟨≈≈⟩ IsEquivalence.sym equiv h≈g

infix 10  _[_,_] _[_≡_] _[_∘_]

_[_,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_≡_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≡_] = Category._≡_

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

-- open import Categories.Agda using (Sets)
Sets : ∀ o → Category _ _ _
Sets o = record
  { Obj = Set o
  ; _⇒_ = λ d c → d → c
  ; _≡_ = λ f g → ∀ {x} → f x ≣ g x

  ; _∘_ = λ f g x → f (g x)
  ; id = λ x → x

  ; assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; equiv = record { refl = ≡.refl; sym = s; trans = t }
  ; ∘-resp-≡ = ∘-resp-≡′
  }
  where
  s : {A B : Set o} → {i j : A → B} → ({x : A} → i x ≣ j x) → {x : A} → j x ≣ i x
  s f {x} rewrite f {x} = ≡.refl

  t : {A B : Set o} {i j k : A → B} → ({x : A} → i x ≣ j x) → ({x : A} → j x ≣ k x) → {x : A} → i x ≣ k x
  t f g {x} rewrite f {x} | g {x} = ≡.refl

  ∘-resp-≡′ : {A B C : Set o} {f h : B → C} {g i : A → B} →
             (∀ {x} → f x ≣ h x) →
             (∀ {x} → g x ≣ i x) →
             (∀ {x} → f (g x) ≣ h (i x))
  ∘-resp-≡′ {g = g} f≡h g≡i {x} rewrite f≡h {g x} | g≡i {x} = ≡.refl


-- open import Categories.Functor using (Functor; Contravariant)
record Functor {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊍ ℓ ⊍ e ⊍ o′ ⊍ ℓ′ ⊍ e′) where
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    {F₁} : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    .{identity} : ∀ {A} → D [ F₁ (C.id {A}) ≡ D.id ]
    .{homomorphism} : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → D [ F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ] ]
    .{F-resp-≡} : ∀ {A B} {F G : C [ A , B ]} → C [ F ≡ G ] → D [ F₁ F ≡ F₁ G ]

idF : ∀ {o ℓ e} {C : Category o ℓ e} → Functor C C
idF {C = C} = record
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = IsEquivalence.refl equiv
  ; homomorphism = IsEquivalence.refl equiv
  ; F-resp-≡ = λ x → x
  }
  where open Category C

infixr 9 _∘F_

_∘F_ : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≡ = ∘-resp-≡′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)

  open import Relation.Binary.SetoidReasoning

  open E using (_⟨≈≈⟩_)

  .identity′ : ∀ {A} → E [ F₁ (G₁ (C.id {A})) ≡ E.id ]
  identity′ {A} =  F-resp-≡ G.identity ⟨≈≈⟩ F.identity

  .homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F₁ (G₁ (C [ g ∘ f ])) ≡ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ]
  homomorphism′ {f = f} {g = g} = F-resp-≡ G.homomorphism ⟨≈≈⟩ F.homomorphism

  .∘-resp-≡′ : ∀ {A B} {F G : C [ A , B ]}
            → C [ F ≡ G ] → E [ F₁ (G₁ F) ≡ F₁ (G₁ G) ]
  ∘-resp-≡′ = λ x → F-resp-≡ (G-resp-≡ x)

Faithful : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Set (o ⊍ ℓ ⊍ e ⊍ e′)
Faithful {C = C} {D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≡ F₁ g ] → C [ f ≡ g ]
  where
  module C = Category C
  module D = Category D
  open Functor F

-- module Categories.NaturalTransformation.Core
record NaturalTransformation {o ℓ e o′ ℓ′ e′}
                             {C : Category o ℓ e}
                             {D : Category o′ ℓ′ e′}
                             (F G : Functor C D) : Set (o ⊍ ℓ ⊍ e ⊍ o′ ⊍ ℓ′ ⊍ e′) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)

  -- CommutativeSquare = λ f g h i → D [ h ∘ f ≡ i ∘ g ]

  field
    η : ∀ X → D [ F₀ X , G₀ X ]
    .commute : ∀ {X Y} (f : C [ X , Y ]) → let open Category D in η Y ∘ F₁ f ≡ G₁ f ∘ η X

idT : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} → NaturalTransformation F F
idT {C = C} {D} {F} = record
  { η = λ _ → D.id
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  open F

  open D using (_⟨≈≈˘⟩_)

  .commute′ : ∀ {X Y} (f : C [ X , Y ]) → D [ D [ D.id ∘ F₁ f ] ≡ D [ F₁ f ∘ D.id ] ]
  commute′ f =  D.identityˡ ⟨≈≈˘⟩ D.identityʳ

infix 4 _≡T_
_≡T_ : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} → Rel (NaturalTransformation F G) (o ⊍ e′)
_≡T_ {D = D} X Y = ∀ {x} → D [ NaturalTransformation.η X x ≡ NaturalTransformation.η Y x ]

infixr 9 _∘ˡ_ _∘ʳ_

_∘ˡ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (H : Functor D E) → (η : NaturalTransformation F G) → NaturalTransformation (H ∘F F) (H ∘F G)
_∘ˡ_ {C = C} {D} {E} {F} {G} H η′ = record
  { η       = λ X → Functor.F₁ H (NaturalTransformation.η η′ X)
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
  module E = Category E renaming (_∘_ to _∘E_; _≡_ to _≡E_)
  module H = Functor H
  -- open D
  open E using (_∘E_ ; _≡E_)

  .commute′ : ∀ {X Y} (f : C [ X , Y ]) →
      Functor.F₁ H (NaturalTransformation.η η′ Y) ∘E Functor.F₁ H (Functor.F₁ F f) ≡E
      Functor.F₁ H (Functor.F₁ G f) ∘E Functor.F₁ H (NaturalTransformation.η η′ X)
  commute′ {X} {Y} f =  let open E in
        IsEquivalence.sym equiv H.homomorphism
    ⟨≈≈⟩ H.F-resp-≡ (NaturalTransformation.commute η′ f)
    ⟨≈≈⟩ H.homomorphism

_∘ʳ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (η : NaturalTransformation F G) → (K : Functor E C) → NaturalTransformation (F ∘F K) (G ∘F K)
_∘ʳ_ η K = record
  { η       = λ X → NaturalTransformation.η η (Functor.F₀ K X)
  ; commute = λ f → NaturalTransformation.commute η (Functor.F₁ K f)
  }

{- causes internal error

-- "Vertical composition"
_∘₁_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁}
        {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁}
        {F G H : Functor C D}
    → NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘₁_ {C = C} {D} {F} {G} {H} X Y = record
  { η = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  module H = Functor H
  module X = NaturalTransformation X
  module Y = NaturalTransformation Y
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)
  open H renaming (F₀ to H₀; F₁ to H₁)

  .commute′ : ∀ {A B} (f : C [ A , B ]) → D [ D [ D [ X.η B ∘ Y.η B ] ∘ F₁ f ] ≡ D [ H₁ f ∘ D [ X.η A ∘  Y.η A ] ] ]
  commute′ {A} {B} f =  let open D in
         assoc
    ⟨≈≈⟩ (( ∘-resp-≡ (IsEquivalence.refl equiv) (Y.commute f)
    ⟨≈≈˘⟩ assoc)
    ⟨≈≈⟩  ∘-resp-≡ (X.commute f) (IsEquivalence.refl equiv) )
    ⟨≈≈⟩ assoc


-- open import Categories.Adjunction using (Adjunction)
record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} (F : Functor D C) (G : Functor C D) : Set (o ⊍ ℓ ⊍ e ⊍ o₁ ⊍ ℓ₁ ⊍ e₁) where
  field
    unit   : NaturalTransformation idF (G ∘F F)
    counit : NaturalTransformation (F ∘F G) idF

    .zig : idT ≡T (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
    .zag : idT ≡T (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

-}

-- Categories.Object.Initial {o ℓ e} (C : Category o ℓ e) where
module _ {o ℓ e} (C : Category o ℓ e) where
   open Category C
   record Initial : Set (o ⊍ ℓ ⊍ e) where
     field
       ⊥ : Obj
       ! : ∀ {A} → (⊥ ⇒ A)
       .!-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! ≡ f

     .!-unique₂ : ∀ {A} → (f g : ⊥ ⇒ A) → f ≡ g
     !-unique₂ f g = IsEquivalence.sym equiv (!-unique f) ⟨≈≈⟩ !-unique g
     .⊥-id : (f : ⊥ ⇒ ⊥) → f ≡ id
     ⊥-id f = !-unique₂ f id

  -- open import Categories.Object.Terminal
   record Terminal : Set (o ⊍ ℓ ⊍ e) where
     field
       ⊤ : Obj
       ! : ∀ {A} → (A ⇒ ⊤)
       .!-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≡ f

     .!-unique₂ : ∀ {A} → (f g : A ⇒ ⊤) → f ≡ g
     !-unique₂ f g = IsEquivalence.sym equiv (!-unique f) ⟨≈≈⟩ !-unique g

     .⊤-id : (f : ⊤ ⇒ ⊤) → f ≡ id
     ⊤-id f = !-unique₂ f id

   -- module Categories.Morphisms {o ℓ e} (C : Category o ℓ e) where
   record Iso {A B} (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊍ ℓ ⊍ e) where
     field
       .isoˡ : g ∘ f ≡ id
       .isoʳ : f ∘ g ≡ id

   infix 4 _≅_
   record _≅_ (A B : Obj) : Set (o ⊍ ℓ ⊍ e) where
     field
       f : A ⇒ B
       g : B ⇒ A
       .iso : Iso f g
     .isoˡ : _
     isoˡ = Iso.isoˡ iso
     .isoʳ : _
     isoʳ = Iso.isoʳ iso
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
