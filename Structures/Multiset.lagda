%{{{ Imports
\begin{code}
module Structures.Multiset where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)

open import Data.List     using (List; []; _++_; _∷_; foldr)  renaming (map to mapL)
open import Data.List.Properties using (map-++-commute; map-id; map-compose)

open import DataProperties hiding (⟨_,_⟩)
open import SetoidEquiv
open import ParComp
open import Belongs
open import Structures.CommMonoid
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
  open CommMonoid
  field
    Ctr : Set ℓ → Set ℓ
    Ctr-equiv : IsCtrEquivalence o Ctr
    Ctr-empty : (Y : Set ℓ) → Ctr Y
    Ctr-append : (Y : Set ℓ) → Ctr Y → Ctr Y → Ctr Y

  LIST-Ctr : Setoid ℓ (ℓ ⊍ o)
  LIST-Ctr = record
    { Carrier = Ctr X₀
    ; _≈_ = equiv Ctr-equiv X
    ; isEquivalence = equivIsEquiv Ctr-equiv X
    }

  empty = Ctr-empty X₀
  _+_ = Ctr-append X₀
  field
    MSisCommMonoid : IsCommutativeMonoid (equiv Ctr-equiv X) _+_ empty

  commMonoid : CommMonoid LIST-Ctr
  commMonoid = record
    { e = empty
    ; _*_ = _+_
    ; isCommMonoid = MSisCommMonoid
    }
  field
    singleton : X₀ → Ctr X₀
    cong-singleton : {i j : X₀} → (i ≈ j) → singleton i ≈ singleton j ∶ commMonoid
    fold : {X : Setoid ℓ o} (CM : CommMonoid X) → let B = Setoid.Carrier X in Ctr B → B
    fold-cong : {YS : Setoid ℓ o} {CM : CommMonoid YS} →
      let Y = Setoid.Carrier YS in
      {i j : Ctr Y}
      → equiv Ctr-equiv YS i j
      → Setoid._≈_ YS (fold CM i) (fold CM j)
    fold-empty : {YS : Setoid ℓ o} {CM : CommMonoid YS} →
      let Y = Setoid.Carrier YS in
      Setoid._≈_ YS (fold CM (Ctr-empty Y)) (e CM)
    fold-+ : {YS : Setoid ℓ o} {CM : CommMonoid YS} →
      let Y = Setoid.Carrier YS in
      let _**_ = _*_ CM in
      {lx ly : Ctr Y} →
      Setoid._≈_ YS (fold CM (Ctr-append Y lx ly)) ((fold CM lx) ** (fold CM ly))
    fold-singleton : {CM : CommMonoid X} → (m : X₀) →
      m ≈ fold CM (singleton m)
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

\begin{code}
record MultisetHom {ℓ} {o} {X Y : Setoid ℓ (ℓ ⊍ o)} (A : Multiset X) (B : Multiset Y) : Set (lsuc ℓ ⊍ lsuc o) where
  open Multiset
  X₀ = Setoid.Carrier X
  field
    lift : (X ⟶ Y) → Hom (LIST-Ctr A , commMonoid A) (LIST-Ctr B , commMonoid B)
    singleton-commute : (f : X ⟶ Y) {x : X₀} → singleton B (f Π.⟨$⟩ x) ≈
      (Hom.mor (lift f) Π.⟨$⟩ singleton A x) ∶ commMonoid B
    fold-commute : {W : CommMonoid X} {Z : CommMonoid Y} (f : Hom (X , W) (Y , Z))
      {lx : Ctr A X₀} →
      Setoid._≈_ Y (fold B Z (lift (Hom.mor f) Hom.⟨$⟩ lx))
                   (Hom.mor f Π.⟨$⟩ (fold A W lx))

open MultisetHom
\end{code}

And now something somewhat different: to express that we have the right
functoriality properties (and ``zap''), we need to assume that we have
\emph{constructors} of |Multiset| and |MultisetHom|.  With these in hand,
we can then phrase what extra properties must hold.  Because these properties
hold at ``different types'' than the ones for the underlying ones, these
cannot go into the above.
\begin{code}
record FunctorialMSH {ℓ} {o} (MS : (X : Setoid ℓ (ℓ ⊍ o)) → Multiset X)
    (MSH : (X Y : Setoid ℓ (ℓ ⊍ o)) → MultisetHom {ℓ} {o} {X} {Y} (MS X) (MS Y))
    : Set (lsuc ℓ ⊍ lsuc o) where
  open Multiset using (Ctr; commMonoid; Ctr-equiv; fold; singleton; cong-singleton; LIST-Ctr)
  open Hom using (mor; _⟨$⟩_)
  open MultisetHom
  field
    id-pres : {X : Setoid ℓ (ℓ ⊍ o)} {x : Ctr (MS X) (Setoid.Carrier X)}
      → (lift (MSH X X) id) ⟨$⟩ x ≈ x ∶ commMonoid (MS X)

    ∘-pres : {X Y Z : Setoid ℓ (ℓ ⊍ o)} {f : X ⟶ Y} {g : Y ⟶ Z}
      {x : Ctr (MS X) (Setoid.Carrier X)} →
      let gg = lift (MSH Y Z) g in
      let ff = lift (MSH X Y) f in
      mor (lift (MSH X Z) (g ∘ f)) Π.⟨$⟩ x ≈ gg ⟨$⟩ (ff ⟨$⟩ x) ∶ commMonoid (MS Z)

    resp-≈ : {A B : Setoid ℓ (ℓ ⊍ o)} {F G : A ⟶ B}
      (F≈G : {x : Setoid.Carrier A} → (Setoid._≈_ B (F Π.⟨$⟩ x) (G Π.⟨$⟩ x))) →
      {x : Ctr (MS A) (Setoid.Carrier A)} →
      Hom.mor (lift (MSH A B) F) Π.⟨$⟩ x ≈ Hom.mor (lift (MSH A B) G) Π.⟨$⟩ x ∶ commMonoid (MS B)

    fold-lift-singleton : {X : Setoid ℓ (ℓ ⊍ o)} →
      let ms = MS X in
      let Singleton = record { _⟨$⟩_ = singleton ms ; cong = cong-singleton ms } in
      {l : Ctr ms (Setoid.Carrier X)} →
      IsCtrEquivalence.equiv (Ctr-equiv ms) X l
      (fold (MS (LIST-Ctr ms)) (commMonoid ms)
            (Hom.mor (lift (MSH X (LIST-Ctr ms)) Singleton) Π.⟨$⟩ l))

\end{code}
%}}}

Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module BuildLeftAdjoint (MS : ∀ {ℓ o} (X : Setoid ℓ (ℓ ⊍ o)) → Multiset X)
  (MSH : ∀ {ℓ o} (X Y : Setoid ℓ (ℓ ⊍ o)) → MultisetHom {ℓ} {o} (MS X) (MS {o = o} Y))
  (Func : ∀ {ℓ o} → FunctorialMSH {ℓ} {o} MS MSH ) where

  open Multiset
  open MultisetHom
  open FunctorialMSH

  Free : (ℓO ℓ≡ : Level) → Functor (Setoids ℓO (ℓO ⊍ ℓ≡)) (MonoidCat ℓO (ℓO ⊍ ℓ≡))
  Free ℓO ℓ≡ = record
    { F₀ = λ S → LIST-Ctr (MS S) , commMonoid (MS S)
    ; F₁ = λ {X} {Y} f → record { Hom (lift {o = ℓ≡} (MSH X Y) f) }
    ; identity = id-pres Func
    ; homomorphism = ∘-pres Func
    ; F-resp-≡ = resp-≈ Func
    }

  LeftAdjoint : {ℓ o : Level} → Adjunction (Free ℓ o) (Forget ℓ (ℓ ⊍ o))
  LeftAdjoint = record
    { unit = record { η = λ X → record { _⟨$⟩_ = singleton (MS X)
                                       ; cong = cong-singleton (MS X) }
                    ; commute = λ {X} {Y} → singleton-commute (MSH X Y) }
    ; counit = record
      { η = λ { (X , cm) → let M = MS X in
            MkHom (record { _⟨$⟩_ = fold M cm
                          ; cong = fold-cong M })
                  (fold-empty M {X} {cm}) (fold-+ M {X} {cm}) }
      ; commute = λ { {X , _} {Y , _} f → fold-commute (MSH X Y) f}
      }
    ; zig = fold-lift-singleton Func
    ; zag = λ { {X , CM} {m} → fold-singleton (MS X) m}
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
  open ElemOfSing X

  open import Algebra using (Monoid)
  open import Data.List using (monoid)
  module ++ = Monoid (monoid (Setoid.Carrier X))
  open Membership X using (elem-of)
  open ConcatTo⊎S X using (⊎S≅++)

  ListMS : Multiset X
  ListMS = record
    { Ctr = List
    ; Ctr-equiv = record
      { equiv = λ Y → let open BagEq Y in _⇔_
      ; equivIsEquiv = λ _ → record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
      }
    ; Ctr-empty  =  λ _ → []
    ; Ctr-append = λ _ → _++_
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
    ; cong-singleton = singleton-≈
    ; fold = λ { (MkCommMon e _+_ _) → foldr _+_ e }
    ; fold-cong = λ { {CM} i⇔j → {!!}}
    ; fold-empty = λ { {X} → Setoid.refl X}
    ; fold-+ = λ {X} {CM} {lx} {ly} → {!!}
    ; fold-singleton = λ {CM} m → ≈.sym CM (IsCommutativeMonoid.right-unit (isCommMonoid CM) m)
    }
    where open CommMonoid

ListCMHom : ∀ {ℓ o} (X Y : Setoid ℓ (ℓ ⊍ o))
  → MultisetHom {o = o} (ImplementationViaList.ListMS X) (ImplementationViaList.ListMS Y)
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
  ; singleton-commute = λ f {x} → ≅-refl
  ; fold-commute = λ { {W} {Z} (MkHom f pres-e pres-*) {lx} → {!!} }
  }
    where
      open ImplementationViaList
      open CommMonoid (Multiset.commMonoid (ListMS X)) renaming (e to e₀; _*_ to _*₀_)
      open CommMonoid (Multiset.commMonoid (ListMS Y)) renaming (e to e₁; _*_ to _*₁_)
      open Membership Y using (elem-of)
      open BagEq Y using (≡→⇔)

module BuildProperties where
  open ImplementationViaList
  functoriality : {ℓ o : Level} → FunctorialMSH {ℓ} {o} ListMS ListCMHom
  functoriality = record
    { id-pres = λ {X} {x} → BagEq.≡→⇔ X (map-id x)
    ; ∘-pres = λ {_} {_} {Z} {f} {g} {x} → BagEq.≡→⇔ Z (map-compose x)
    ; resp-≈ = λ {A} {B} {F} {G} F≈G {l} → {!!}
    ; fold-lift-singleton = λ {X} {l} → {!!}
    }
\end{code}

Last but not least, build the left adjoint:

\begin{code}
module FreeCommMonoid = BuildLeftAdjoint ImplementationViaList.ListMS ListCMHom
  BuildProperties.functoriality
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
