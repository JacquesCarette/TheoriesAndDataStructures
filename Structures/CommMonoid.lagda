\section{Structures.CommMonoid}

%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; _Preserves₂_⟶_⟶_; IsEquivalence)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open import Function2         using (_$ᵢ)
open import Function          using () renaming (id to id₀; _∘_ to _⊚_)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)
open import Data.List.Properties using (map-++-commute; map-id; map-compose)

open import Relation.Binary.Sum
import Algebra.FunctionProperties as AFP
open AFP using (Op₂)

open import Forget
open import EqualityCombinators
open import DataProperties hiding (_,_; ⟨_,_⟩)
open import SetoidEquiv
open import ParComp
open import Belongs
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\subsection{Definitions}

Some of this is borrowed from the standard library's |Algebra.Structures|
and |Algebra|.  But un-nested and made direct.

\begin{code}
record IsCommutativeMonoid {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
                           (_∙_ : Op₂ A) (ε : A) : Set (a ⊍ ℓ) where
  open AFP _≈_
  field
    left-unit   : LeftIdentity ε _∙_
    right-unit  : RightIdentity ε _∙_
    assoc       : Associative _∙_
    comm        : Commutative _∙_
    _⟨∙⟩_        : Congruent₂ _∙_

record CommMonoid {ℓ} {o} : Set (lsuc ℓ ⊍ lsuc o) where
  constructor MkCommMon
  field setoid : Setoid ℓ o
  open Setoid setoid public

  field
    e            : Carrier
    _*_          : Carrier → Carrier → Carrier
    isCommMonoid : IsCommutativeMonoid _≈_ _*_ e
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
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (o ⊍ ℓ)
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
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ o) (Setoids ℓ o)
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

%{{{ CtrSetoid
\subsection{CtrSetoid}

As will be explained below, the kind of ``container'' used for
building a |Multiset| needs to support a |Setoid|-polymorphic
equivalence relation.
\begin{code}
record IsCtrEquivalence {ℓ : Level} (o : Level) (Ctr : Set ℓ → Set ℓ)
    : Set (lsuc ℓ ⊍ lsuc o) where
  field
    equiv : (X : Setoid ℓ o) → Rel (Ctr (Setoid.Carrier X)) (o ⊍ ℓ)
    equivIsEquiv : (X : Setoid ℓ o) → IsEquivalence (equiv X)
\end{code}
%}}}

%{{{ Multiset
\subsection{Multiset}
A “multiset on type X” is a structure on which one can define
\begin{itemize}
\item a \emph{commutative monoid} structure,
\item implement the concept of \emph{singleton}
\item implement the concept of \emph{fold}; note that the name
is inspired by its implementation in the main model.  Its signature
would have suggested ``extract'', but this would have been
quite misleading.
\end{itemize}

\begin{code}
record Multiset {ℓ o : Level} (X : Setoid ℓ o) : Set (lsuc ℓ ⊍ lsuc o) where
  open Setoid X renaming (Carrier to X₀)
  open IsCtrEquivalence
  open CommMonoid hiding (_≈_)
  field
    Ctr : Set ℓ → Set ℓ
    Ctr-equiv : IsCtrEquivalence o Ctr
    Ctr-empty : (Y : Set ℓ) → Ctr Y
  LIST : Set ℓ
  LIST = Ctr X₀
  _↔_ = equiv Ctr-equiv X
  ↔isEquiv = equivIsEquiv Ctr-equiv X
  empty = Ctr-empty X₀
  field
    _+_ : LIST → LIST → LIST
    MSisCommMonoid : IsCommutativeMonoid _↔_ _+_ empty

  commMonoid : CommMonoid {ℓ} {ℓ ⊍ o}
  commMonoid = record
    { setoid = record { Carrier = LIST ; _≈_ = _↔_ ; isEquivalence = ↔isEquiv }
    ; e = empty
    ; _*_ = _+_
    ; isCommMonoid = MSisCommMonoid
    }
  field
    singleton : X₀ → LIST
    cong-singleton : {i j : X₀} → (i ≈ j) → singleton i ≈ singleton j ∶ commMonoid
    fold : (CM : CommMonoid {ℓ} {o}) → let B = CommMonoid.Carrier CM in Ctr B → B
    fold-cong : {CM : CommMonoid {ℓ} {o}} →
      let Y = CommMonoid.Carrier CM in let YS = CommMonoid.setoid CM in
      {i j : Ctr Y}
      → equiv Ctr-equiv YS i j
      → Setoid._≈_ YS (fold CM i) (fold CM j)
    fold-empty : {CM : CommMonoid {ℓ} {o}} →
      let YS = setoid CM in let Y = Carrier CM in
      Setoid._≈_ YS (fold CM (Ctr-empty Y)) (e CM)
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

\begin{code}
record MultisetHom {ℓ} {o} {X Y : Setoid ℓ o} (A : Multiset X) (B : Multiset Y) : Set (ℓ ⊍ o) where
  open Multiset
  field
    lift : (X ⟶ Y) → Hom (commMonoid A) (commMonoid B)
    singleton-commute : (f : X ⟶ Y) {x : Setoid.Carrier X} → singleton B (f Π.⟨$⟩ x) ≈
      (Hom.mor (lift f) Π.⟨$⟩ singleton A x) ∶ commMonoid B

open MultisetHom

record FunctorialMSH {ℓ} {o} (MS : (X : Setoid ℓ o) → Multiset X)
    (MSH : (X Y : Setoid ℓ o) → MultisetHom (MS X) (MS Y))
    : Set (lsuc ℓ ⊍ lsuc o) where
  open Multiset using (commMonoid; LIST)
  open Hom using (mor; _⟨$⟩_)
  open MultisetHom
  field
    id-pres : {X : Setoid ℓ o}
      {x : LIST (MS X)} → (lift (MSH X X) id) ⟨$⟩ x ≈ x ∶ commMonoid (MS X)

    ∘-pres : {X Y Z : Setoid ℓ o} {f : X ⟶ Y} {g : Y ⟶ Z} {x : LIST (MS X)} →
      let gg = lift (MSH Y Z) g in
      let ff = lift (MSH X Y) f in
      mor (lift (MSH X Z) (g ∘ f)) Π.⟨$⟩ x ≈ gg ⟨$⟩ (ff ⟨$⟩ x) ∶ commMonoid (MS Z)

    resp-≈ : {A B : Setoid ℓ o} {F G : A ⟶ B}
      (F≈G : {x : Setoid.Carrier A} → (Setoid._≈_ B (F Π.⟨$⟩ x) (G Π.⟨$⟩ x))) →
      {x : LIST (MS A)} →
      Hom.mor (lift (MSH A B) F) Π.⟨$⟩ x ≈ Hom.mor (lift (MSH A B) G) Π.⟨$⟩ x ∶ commMonoid (MS B)
\end{code}
%}}}

Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module Build (MS : ∀ {ℓ o} (X : Setoid ℓ o) → Multiset X)
  (MSH : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (MS X) (MS Y))
  (Func : ∀ {ℓ o} → FunctorialMSH {ℓ} {o} MS MSH ) where

  open Multiset
  open MultisetHom
  open FunctorialMSH

  MultisetF : (ℓO ℓ≡ : Level) → Functor (Setoids ℓO (ℓO ⊍ ℓ≡)) (MonoidCat ℓO (ℓO ⊍ ℓ≡))
  MultisetF ℓO ℓ≡ = record
    { F₀ = λ S → commMonoid (MS S)
    ; F₁ = λ {X} {Y} f → record { Hom (lift (MSH X Y) f) }
    ; identity = id-pres Func
    ; homomorphism = ∘-pres Func
    ; F-resp-≡ = resp-≈ Func
    }

  MultisetLeft : {ℓ o : Level} → Adjunction (MultisetF ℓ o) (Forget ℓ (ℓ ⊍ o))
  MultisetLeft = record
    { unit = record { η = λ X → record { _⟨$⟩_ = singleton (MS X)
                                       ; cong = cong-singleton (MS X) }
                    ; commute = λ {X} {Y} → singleton-commute (MSH X Y) }
    ; counit = record
      { η = λ { cm → let M = MS (setoid cm) in
            MkHom (record { _⟨$⟩_ = fold M cm
                          ; cong = fold-cong M })
                  ( fold-empty M {cm}) {!!} }
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

%{{{ An implementation of |Multiset| using lists with Bag equality
\subsection{An implementation of |Multiset| using lists with Bag equality}
\begin{code}
module ImplementationViaList {ℓ o : Level} (X : Setoid ℓ o) where
  open Setoid X hiding (refl) renaming (Carrier to X₀)
  open BagEq X using (≡→⇔)

  open import Algebra using (Monoid)
  open import Data.List using (monoid)
  module ++ = Monoid (monoid (Setoid.Carrier X))
  open Membership X using (elem-of)
  open ConcatTo⊎⊎ X using (⊎S≅++)

  ListMS : Multiset X
  ListMS = record
    { Ctr = List
    ; Ctr-equiv = record
      { equiv = λ Y → let open BagEq Y in _⇔_
      ; equivIsEquiv = λ _ → record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
      }
    ; Ctr-empty  =  λ _ → []
    ; _+_        =  _++_
    ; MSisCommMonoid = record
      { left-unit  =  λ _ → ≅-refl
      ; right-unit = λ xs → ≡→⇔ (proj₂ ++.identity xs)
      ; assoc      =  λ xs ys zs → ≡→⇔ (++.assoc xs ys zs)
      ; comm       =  λ xs ys →
        elem-of (xs ++ ys)         ≅˘⟨ ⊎S≅++ ⟩
        elem-of xs ⊎S elem-of ys   ≅⟨ ⊎S-comm _ _ ⟩
        elem-of ys ⊎S elem-of xs   ≅⟨ ⊎S≅++ ⟩
        elem-of (ys ++ xs) ∎
      ; _⟨∙⟩_ = λ {x} {y} {z} {w} x⇔y z⇔w →
         elem-of (x ++ z)          ≅˘⟨ ⊎S≅++ ⟩
         elem-of x ⊎S elem-of z    ≅⟨ x⇔y ⊎S₁ z⇔w ⟩
         elem-of y ⊎S elem-of w    ≅⟨ ⊎S≅++ ⟩
         elem-of (y ++ w) ∎
      }

    ; singleton = λ x → x ∷ []
    ; cong-singleton = λ {i} {j} i≈j →
        elem-of (i ∷ []) ≅⟨ {!!} ⟩
        elem-of (j ∷ []) ∎
    ; fold = λ { (MkCommMon _ e _+_ _) → foldr _+_ e }
    ; fold-cong = λ { {CM} i⇔j → {!!}}
    ; fold-empty = λ {CM} → Setoid.refl (CommMonoid.setoid CM)
    }

ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ o) → MultisetHom (ImplementationViaList.ListMS X) (ImplementationViaList.ListMS Y)
ListCMHom {ℓ} {o} X Y = record
  { lift = λ F → let g = Π._⟨$⟩_ F in record
    { mor = record
      { _⟨$⟩_ = mapL g
      ; cong = λ {xs} {ys} xs≈ys →
        elem-of (mapL g xs)   ≅⟨ shift-map F xs ⟩
        shifted F xs          ≅⟨ shifted-cong F xs≈ys ⟩
        shifted F ys          ≅˘⟨ shift-map F ys ⟩
        elem-of (mapL g ys) ∎
      }
    ; pres-e =
         elem-of []     ≅˘⟨ ⊥⊥≅elem-of-[] Y ⟩
         ⊥⊥             ≅⟨ ⊥⊥≅elem-of-[] Y ⟩
         (elem-of e₁) ∎

      -- in the proof below, *₀ and *₁ are both ++
    ; pres-* = λ {x} {y} →
      elem-of (mapL g (x *₀ y))           ≅⟨ ≡→⇔ (map-++-commute g x y) ⟩
      elem-of (mapL g x *₁ mapL g y) ∎
    }
  ; singleton-commute = {!!}
  }
    where
      open ImplementationViaList
      open CommMonoid (Multiset.commMonoid (ListMS X)) renaming (e to e₀; _*_ to _*₀_)
      open CommMonoid (Multiset.commMonoid (ListMS Y)) renaming (e to e₁; _*_ to _*₁_)
      open Membership Y using (elem-of)
      open BagEq Y using (≡→⇔)

module _ where
  open ImplementationViaList
{-
  id-pres : ∀ {ℓ o} {X : Setoid ℓ o} (x : List (Setoid.Carrier X)) →
    (lift (ListCMHom X X) id) Hom.⟨$⟩ x ≈ x ∶ Multiset.commMonoid (ListMS X)
  id-pres {X = X} x =
    elem-of (mapL id₀ x)   ≅⟨ ≡→⇔ (map-id x) ⟩
    elem-of x ∎
    where
      open Membership X
      open BagEq X

  homMS : ∀ {ℓ o} {X Y Z : Setoid ℓ o} {f : X ⟶ Y} {g : Y ⟶ Z} (x : List (Setoid.Carrier X)) →
    let gg = lift (ListCMHom Y Z) g in
    let ff = lift (ListCMHom X Y) f in
    Hom.mor (lift (ListCMHom X Z) (g ∘ f)) Π.⟨$⟩ x ≈
      gg Hom.⟨$⟩ (ff Hom.⟨$⟩ x) ∶ Multiset.commMonoid (ListMS Z)
  homMS {Z = Z} {f} {g} xs = ≡→⇔ (map-compose xs)
    where open BagEq Z
-}
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
