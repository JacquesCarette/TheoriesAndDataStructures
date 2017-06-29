\section{Structures.CommMonoid}

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
open import Relation.Binary.Sum

open import Forget
open import EqualityCombinators
open import DataProperties
open import SetoidEquiv
open import ParComp
open import Some
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\subsection{Definitions}
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
\subsection{Category and Forgetful Functor}
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
\subsection{Multiset}
A “multiset on type X” is a commutative monoid with a map to it from |X|.
\edcomm{WK}{Misnomer!}
For now, we make no constraints on the map, however it may be that
future proof obligations will require it to be an injection --- which is reasonable.

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
\subsection{ListMS}
\begin{code}
abstract
  ListMS : {ℓ o : Level} (X : Setoid ℓ o) → Multiset X
  ListMS {ℓ} {o} X = record
    { commMonoid = record
        { setoid     =  LM
        ; e          =  []
        ; _*_        =  _++_
        ; left-unit  =  Setoid.refl LM
        ; right-unit = λ {xs} → ≡→BE (proj₂ ++.identity xs)
        ; assoc      =  λ {xs} {ys} {zs} → ≡→BE (++.assoc xs ys zs)
        ; comm       =  λ {xs} {ys} → BE (λ {z} →
          z ∈ xs ++ ys         ≅⟨ {!!} ⟩ -- |≅⟨ ≅-sym (++≅ {P = setoid≈ z}) ⟩|
          (z ∈ xs ⊎⊎ z ∈ ys)  ≅⟨ ⊎⊎-comm ⟩
          (z ∈ ys ⊎⊎ z ∈ xs)  ≅⟨ {!!} ⟩ -- |≅⟨ ++≅ {P = setoid≈ z}⟩|
          z ∈ ys ++ xs  ∎) {!!} {!!}
        ; _⟨*⟩_ = λ {x} {y} {z} {w} x≈y z≈w → BE (λ {t} →
           t ∈ x ++ z        ≅⟨ {!!} ⟩ -- |≅-sym (++≅ {P = setoid≈ t}) |
          (t ∈ x ⊎⊎ t ∈ z)   ≅⟨ (permut x≈y) ⊎⊎₁ (permut z≈w) ⟩
          (t ∈ y ⊎⊎ t ∈ w)   ≅⟨ {!!} ⟩ -- |++≅ {P = setoid≈ t} |
           t ∈ y ++ w ∎) {!!} {!!}
        }
    ; singleton = λ x → x ∷ []
    }
    where
      open import Algebra using (Monoid)
      open import Data.List using (monoid)
      module ++ = Monoid (monoid (Setoid.Carrier X))
      open Membership X
      open BagEq

      X₀ = Setoid.Carrier X

      ≡→BE : {a b : List X₀} → a ≡ b → BagEq a b
      ≡→BE ≡.refl = BE (record
        { to = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; from = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; inverse-of = record { left-inverse-of = λ _ → ≋-refl ; right-inverse-of = λ _ → ≋-refl } })
        (λ _ pf → pf) (λ _ pf → pf)

      LM : Setoid ℓ (ℓ ⊍ o)
      LM = record
        { Carrier = List (Setoid.Carrier X)
        ; _≈_ = BagEq
        ; isEquivalence = record { refl = BE-refl ; sym = BE-sym ; trans = BE-trans }
        }

  ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ListMS X) (ListMS Y)
  ListCMHom X Y = MKMSHom (λ F → let g = Π._⟨$⟩_ F in record
    { mor = record
      { _⟨$⟩_ = mapL g
      ; cong = λ {xs} {ys} xs≈ys → BE (λ {y} →
      y ∈ mapL g xs           ≅⟨ ≅-sym (map≅ {P = setoid≈ y} {F}) ⟩
      {! Some (setoid≈ y ∘ F) xs !} ≅⟨ {!!} ⟩ -- |Some-cong {P = setoid≈ y ∘ F} xs≈ys |
      {! Some (setoid≈ y ∘ F) ys !} ≅⟨ map≅ {P = setoid≈ y} {F} ⟩
      y ∈ mapL g ys ∎) {!!} {!!}
      }
    ; pres-e = BE (λ {z} →
      z ∈ []     ≅⟨ ≅-sym (⊥≅Some[] {P = setoid≈ z}) ⟩
      ⊥⊥         ≅⟨ ⊥≅Some[] {P = setoid≈ z} ⟩
      (z ∈ e₁) ∎) {!!} {!!}

      -- in the proof below, *₀ and *₁ are both ++
    ; pres-* = λ {x} {y} → BE (λ {z} → let g = Π._⟨$⟩_ F in
      z ∈ mapL g (x *₀ y)                              ≅⟨ ≅-sym (map≅ {P = setoid≈ z} {F}) ⟩
      {! Some (setoid≈ z ∘ F) (x *₀ y) !}                    ≅⟨ {!!} ⟩ -- |≅-sym (++≅ {P = setoid≈ z ∘ F}) |
      {! Some (setoid≈ z ∘ F) x ⊎⊎ Some (setoid≈ z ∘ F) y !} ≅⟨ (map≅ {P = setoid≈ z} {F}) ⊎⊎₁ (map≅ {P = setoid≈ z} {F})⟩
      z ∈ mapL g x ⊎⊎ z ∈ mapL g y                     ≅⟨ {!!} ⟩ -- | ++≅ {P = setoid≈ z} |
      z ∈ mapL g x *₁ mapL g y ∎) {!!} {!!}
    })
    where
      open CommMonoid (Multiset.commMonoid (ListMS X)) renaming (e to e₀  ; _*_ to _*₀_)
      open CommMonoid (Multiset.commMonoid (ListMS Y)) renaming (e to e₁; _*_ to _*₁_)
      open Membership Y

  id-pres : ∀ {ℓ o} {X : Setoid ℓ o} (x : Carrier (ListMS X)) →
    (lift (ListCMHom X X) id) Hom.⟨$⟩ x ≈ x ∶ commMonoid (ListMS X)
  id-pres {X = X} x = BE (λ {z} →
    -- | z ∈ lift (ListCMHom X X) id Hom.⟨$⟩ x ≅⟨ ≅-refl ⟩ |
    z ∈ mapL id₀ x                       ≅⟨ ≅-sym (map≅ {P = setoid≈ z} {f = id}) ⟩
    z ∈ x ∎) {!!} {!!}
    where
      open Membership X
      open Setoid X

  homMS : ∀ {ℓ o} {X Y Z : Setoid ℓ o} {f : X ⟶ Y} {g : Y ⟶ Z} (x : Carrier (ListMS X)) →
    let gg = lift (ListCMHom Y Z) g in
    let ff = lift (ListCMHom X Y) f in
    Hom.mor (lift (ListCMHom X Z) (g ∘ f)) Π.⟨$⟩ x ≈
      gg Hom.⟨$⟩ (ff Hom.⟨$⟩ x) ∶ commMonoid (ListMS Z)
  homMS {Z = Z} {f} {g} xs = BE (λ {x} →
    x ∈ mapL (_⟨$⟩_ (g ∘ f)) xs              ≅⟨ ≅-sym (map≅ {P = setoid≈ x} {g ∘ f}) ⟩
    {! Some (setoid≈ x ∘ (g ∘ f)) xs           !} ≅⟨ ≅-refl ⟩ -- associativity of |∘| is "free"
    {! Some ((setoid≈ x ∘ g) ∘ f) xs           !} ≅⟨ map≅ {P = setoid≈ x ∘ g} {f} ⟩
    {! Some (setoid≈ x ∘ g) (mapL (_⟨$⟩_ f) xs !} ≅⟨ map≅ {P = setoid≈ x} {g} ⟩
    x ∈ mapL (_⟨$⟩_ g) (mapL (_⟨$⟩_ f) xs) ∎) {!!} {!!}
    where open Membership Z; open Π

  cong-singleton : ∀ {ℓ o} {X : Setoid ℓ o} {i j : Setoid.Carrier X} →
    (Setoid._≈_ X i j) → singleton (ListMS X) i ≈ singleton (ListMS X) j ∶ commMonoid (ListMS X)
  cong-singleton {X = X} {i} {j} i≈j = BE (λ {x} →
    x ∈ i ∷ [] ≅⟨ {!!} ⟩
    x ∈ j ∷ [] ∎) {!!} {!!}
    where open Membership X

  fold : ∀ {ℓ o} {X : Setoid ℓ o} {B : Set ℓ} →
    let A = Setoid.Carrier X in
    (A → B → B) → B → Carrier (ListMS X) → B
  fold = foldr
\end{code}

\begin{code}
MultisetF : (ℓ o : Level) → Functor (Setoids ℓ o) (MonoidCat ℓ (ℓ ⊍ o))
MultisetF ℓ o = record
  { F₀ = λ S → commMonoid (ListMS S)
  ; F₁ = λ {X} {Y} f → let F = lift (ListCMHom X Y) f in record { Hom F }
  ; identity = λ {A} {x} → id-pres x
  ; homomorphism = λ { {x = x} → homMS x }
  ; F-resp-≡ = λ F≈G {x} → {!!}
  }
  where
    open Multiset; open MultisetHom

MultisetLeft : (ℓ o : Level) → Adjunction (MultisetF ℓ (o ⊍ ℓ)) (Forget ℓ (o ⊍ ℓ))
MultisetLeft ℓ o = record
  { unit = record { η = λ X → record { _⟨$⟩_ = singleton (ListMS X)
                                     ; cong = cong-singleton }
                  ; commute = λ f → λ {x} → {!!} }
  ; counit = record
    { η = λ { (MkCommMon A z _+_ _ _ _ _ _) →
          MkHom (record { _⟨$⟩_ = fold _+_ z ; cong = {!!} }) {!!} {!!} }
    ; commute = {!!}
    }
  ; zig = λ {X} {l} → {!!}
  ; zag = λ {X} {l} → {!!}
  }
  where
    open Multiset
    open CommMonoid
\end{code}
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
