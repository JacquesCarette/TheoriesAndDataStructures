\section{Structures.Multiset}

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
open import EqualityCombinators
open import Belongs
open import Structures.CommMonoid renaming (Hom to CMArrow)

open import Algebra   using (Monoid)
open import Data.List using (monoid)
\end{code}
%}}}

%{{{ CtrSetoid
\subsection{CtrSetoid}

As will be explained below, the kind of ``container'' ---|ctr|--- used for
building a |Multiset| needs to support a |Setoid|-polymorphic
equivalence relation.
\begin{code}
record IsCtrEquivalence {ℓ : Level} (o : Level) (Ctr : Set ℓ → Set ℓ)
  : Set (lsuc ℓ ⊍ lsuc o) where
  field
    equiv        : (X : Setoid ℓ (o ⊍ ℓ)) → Rel (Ctr (Setoid.Carrier X)) (o ⊍ ℓ)
    equivIsEquiv : (X : Setoid ℓ (o ⊍ ℓ)) → IsEquivalence (equiv X)
  -- handy dandy syntactic sugar for |k|ontainer equality
  infix -666 equiv
  syntax equiv X s t  =  s ≈ₖ t ∶ X   -- ghost colon
\end{code}

We have a type transformer |ctr| that furnishes setoids with an equivalence relation |equiv|.

\edcomm{MA}{Since there are no `coherencey' constraints, we might as well say that this
|IsCtrEquivalence| is nothing more than a setoid transformer: The object component of an endofunctor
on the category of setoids. Indeed:}

\begin{code}
  ctrSetoid : (X : Setoid ℓ (o ⊍ ℓ)) → Setoid ℓ (ℓ ⊍ o)
  ctrSetoid X = record
    { Carrier        =  Ctr (Setoid.Carrier X)
    ; _≈_            =  equiv X
    ; isEquivalence  =  equivIsEquiv X
    }
\end{code}
%}}}

%{{{ CommutativeContainer

In the same vein as before, we consider a setoid-polymorphic equivalence relation that
also furnishes a raw type with a commutative monoid structure. That is, we know have
a the object-component of a functor from the category of setoids to the category of
commutative monoids.

\begin{code}
record CommutativeContainer (ℓ c : Level) : Set (lsuc ℓ ⊍ lsuc c) where
  open IsCtrEquivalence using (equiv)
  field
    𝒞                    :   Set ℓ → Set ℓ
    isCtrEquivalence     :   IsCtrEquivalence c 𝒞
    ∅                    :  {X : Set ℓ} → 𝒞 X
    _⊕_                  :  {X : Set ℓ} → 𝒞 X → 𝒞 X → 𝒞 X
    isCommutativeMonoid  :  {X : Setoid ℓ (c ⊍ ℓ)} → IsCommutativeMonoid (equiv isCtrEquivalence X) _⊕_ ∅

  open IsCtrEquivalence isCtrEquivalence             public

  commMonoid : (X : Setoid ℓ (c ⊍ ℓ)) → CommMonoid (ctrSetoid X)
  commMonoid X = record
    { e              =   ∅
    ; _*_            =   _⊕_
    ; isCommMonoid   =   isCommutativeMonoid
    }
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
open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
open CommMonoid using (eq-in ; isCommMonoid)

record Multiset {ℓ c : Level} (X : Setoid ℓ (c ⊍ ℓ)) : Set (lsuc ℓ ⊍ lsuc c) where  
  field
    commutativeContainer : CommutativeContainer ℓ c

  open CommutativeContainer commutativeContainer     public
  open Setoid X using (_≈_) renaming (Carrier to X₀)  

  field
    singleton       :  X ⟶ ctrSetoid X
    fold            :  {Y : Setoid ℓ (c ⊍ ℓ)} (CMY : CommMonoid Y) → CMArrow (commMonoid Y) CMY
    fold-singleton  :  {CM : CommMonoid X} (x : X₀) → x ≈ fold CM ⟨$⟩ (singleton ⟨$⟩₀ x)
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

In the classical contexts of sets and set-functions, the constraints take the form:
|{ f x } ≈ lift f { x }| and |fold (lift f s) ≈ f (fold s)|. In particular, the |lift| operation
mimics the behaviour of the morphism, or “map”, portion of a functor.

\begin{code}
record MultisetHom {ℓ c : Level} {X Y : Setoid ℓ (c ⊍ ℓ)} (A : Multiset X) (B : Multiset Y)
  : Set (lsuc ℓ ⊍ lsuc c) where
  open Multiset {ℓ} {c}
  X₀ = Setoid.Carrier X
  open Setoid Y using (_≈_)

  private
    𝓜 = λ {Z : Setoid ℓ (c ⊍ ℓ)} (CMZ : Multiset Z) → commMonoid CMZ Z
    𝒮  = λ {Z : Setoid ℓ (c ⊍ ℓ)} (CMZ : Multiset Z) → singleton CMZ ⟨$⟩₀_

  field
    lift : (X ⟶ Y) → CMArrow (𝓜 A) (𝓜 B)

    -- This ensures that |singleton| is sufficiently polymorphic; i.e., a natural transformation.
    -- See the Adjunction below.
    singleton-commute : (F : X ⟶ Y) {x : X₀} → 𝒮 B (F ⟨$⟩₀ x) ≈ lift F ⟨$⟩ (𝒮 A x)  ∶  𝓜 B

    fold-commute : {CMX : CommMonoid X} {CMY : CommMonoid Y} (F : CMArrow CMX CMY)
                 → {s : 𝒞 A X₀}
                 → fold B CMY ⟨$⟩ (lift (mor F) ⟨$⟩ s)  ≈  F ⟨$⟩ (fold A CMX ⟨$⟩ s)
                 
open MultisetHom
\end{code}

And now something somewhat different: to express that we have the right
functoriality properties (and ``zap''), we need to assume that we have
\emph{constructors} of |Multiset| and |MultisetHom|.  With these in hand,
we can then phrase what extra properties must hold.  Because these properties
hold at ``different types'' than the ones for the underlying ones, these
cannot go into the above.
\begin{code}
record FunctorialMSH {ℓ c : Level} (MS : (X : Setoid ℓ (c ⊍ ℓ)) → Multiset X)
    (MSH : {X Y : Setoid ℓ (c ⊍ ℓ)} → MultisetHom {ℓ} {c} {X} {Y} (MS X) (MS Y))
    : Set (lsuc ℓ ⊍ lsuc c) where
  open Multiset
  open MultisetHom
  open Setoid   using (Carrier)
  open IsCtrEquivalence hiding (ctrSetoid)
  private
    Obj = Setoid ℓ (c ⊍ ℓ)
    𝒞ₘ = λ X → 𝒞 (MS X) (Carrier X)
    𝓜 = λ X → commMonoid (MS X) X
    𝑳  = λ {X Y : Obj}  (F   : X ⟶ Y) → lift MSH F
    _≋_ = λ {X : Obj} (l r : 𝒞ₘ X) → l ≈ r ∶ 𝓜 X
  
  field
    -- Lifting the identity yields an identity morphism.
    id-pres : {X : Obj} {x : 𝒞ₘ X} → 𝑳 id ⟨$⟩ x  ≈  x  ∶  𝓜 X

    -- Lifting preserves composition.
    ∘-pres : {X Y Z : Obj} {F : X ⟶ Y} {G : Y ⟶ Z}
           → {x : 𝒞ₘ X} → (𝑳 (G ∘ F)) ⟨$⟩ x ≈ 𝑳 G ⟨$⟩ (𝑳 F ⟨$⟩ x)  ∶  𝓜 Z

    -- Lifting preserves extensional equality.
    resp-≈ : {X Y : Obj} {F G : X ⟶ Y} (let open Setoid Y renaming (_≈_ to _≈₀_))
          → (F≈G : {x : Carrier X} → F ⟨$⟩₀ x ≈₀ G ⟨$⟩₀ x)
          → {x : 𝒞ₘ X} → 𝑳 F ⟨$⟩ x ≈ 𝑳 G ⟨$⟩ x  ∶  𝓜 Y

    -- Lifting the singleton mapping then folding yields the orginal result.
    -- In particular, the singleton construction is injective --as we'd like.
    fold-lift-singleton : {X : Obj} (let ms = MS X ; _≈_ = equiv (isCtrEquivalence ms) X)
      → {s : 𝒞ₘ X} → s ≈ (fold (MS (ctrSetoid ms X)) (𝓜 X) ⟨$⟩ (𝑳 (singleton ms) ⟨$⟩ s))
\end{code}
%}}}

%{{{ BuildLeftAdjoint
Given an implementation of a |Multiset| as well as of |MultisetHom| over that,
build a Free Functor which is left adjoint to the forgetful functor.

\begin{code}
module BuildLeftAdjoint
  (MS   : {ℓ c : Level} (X : Setoid ℓ (ℓ ⊍ c)) → Multiset X)
  (MSH  : {ℓ c : Level} {X Y : Setoid ℓ (ℓ ⊍ c)} → MultisetHom {ℓ} {c} (MS X) (MS {c = c} Y))
  (Func : {ℓ c : Level} → FunctorialMSH {ℓ} {c} MS MSH )
  where

  open Multiset
  open MultisetHom
  open FunctorialMSH

  Free : (ℓ c : Level) → Functor (Setoids ℓ (ℓ ⊍ c)) (MonoidCat ℓ (ℓ ⊍ c))
  Free _ _ = record
    { F₀             =   λ S → ctrSetoid (MS S) S , commMonoid (MS S) S
    ; F₁             =   λ F → record { CMArrow (lift MSH F) }
    ; identity       =   id-pres Func
    ; homomorphism   =   ∘-pres Func
    ; F-resp-≡       =   resp-≈ Func
    }

  LeftAdjoint : {ℓ o : Level} → Adjunction (Free ℓ o) (Forget ℓ (ℓ ⊍ o))
  LeftAdjoint = record
    { unit = record
      { η = λ X → singleton (MS X)
      ; commute = singleton-commute MSH
      }
    ; counit = record
      { η        =  λ { (X , cm) → record { CMArrow (fold (MS X) cm) } }
      ; commute  =  fold-commute MSH
      }
    ; zig = fold-lift-singleton Func
    ; zag = λ { {X , CM} {m} → fold-singleton (MS X) m }
    }
\end{code}
%}}}

%{{{ An implementation of |Multiset| using lists with Bag equality
\subsection{An implementation of |Multiset| using lists with Bag equality}
\begin{code}
module ImplementationViaList {ℓ o : Level} (X : Setoid ℓ (ℓ ⊍ o)) where
  open Setoid  
  open ElemOfSing X
\end{code}

\begin{code}
  ListMS : Multiset {ℓ} {o} X
  ListMS = record
    { commutativeContainer = record
         { 𝒞                   = List
         ; isCtrEquivalence    = record
            { equiv        = λ Y → let open BagEq Y in _⇔_
            ; equivIsEquiv = λ _ → record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
            }
         ; ∅                   = []
         ; _⊕_                 = _++_
         ; isCommutativeMonoid = λ {Y} →
           let
             open BagEq       Y   using   (≡→⇔)
             open Membership  Y   using   (elem-of)
             open ConcatTo⊎S  Y   using   (⊎S≅++)
             module ++ = Monoid (monoid (Carrier Y))
           in record
            { left-unit  = λ y → ≅-refl
            ; right-unit = λ ys → ≡→⇔ (proj₂ ++.identity ys)
            ; assoc      = λ xs ys zs → ≡→⇔ (++.assoc xs ys zs)
            ; comm       = λ xs ys → 
               elem-of (xs ++ ys)         ≅˘⟨ ⊎S≅++ ⟩
               elem-of xs ⊎S elem-of ys   ≅⟨ ⊎S-comm _ _ ⟩
               elem-of ys ⊎S elem-of xs   ≅⟨ ⊎S≅++ ⟩
               elem-of (ys ++ xs)         ∎
            ; _⟨∙⟩_      = λ {x} {y} {z} {w} x⇔y z⇔w →
               elem-of (x ++ z)          ≅˘⟨ ⊎S≅++ ⟩
               elem-of x ⊎S elem-of z    ≅⟨ x⇔y ⊎S₁ z⇔w ⟩
               elem-of y ⊎S elem-of w    ≅⟨ ⊎S≅++ ⟩
               elem-of (y ++ w)          ∎
            }
         }
    ; singleton = record { _⟨$⟩_ = λ x → x ∷ [] ; cong = singleton-≈ }
    ; fold = λ {Y} CMX → let open CommMonoid CMX in record
         { mor      =   record { _⟨$⟩_ = foldr _*_ e ; cong = fold-permute {CM = CMX} }
         ; pres-e   =   refl Y
         ; pres-*   =   fold-CM-over-++ CMX
         }
    ; fold-singleton = λ {CM} x → sym X (right-unit (isCommMonoid CM) x)
    }
    where
       open IsCommutativeMonoid using (left-unit ; right-unit ; assoc) renaming (_⟨∙⟩_ to cong)
       open import Relation.Binary.SetoidReasoning renaming (_∎ to _■)
        
       fold-CM-over-++ : {Z : Setoid ℓ (o ⊍ ℓ)} (cm : CommMonoid Z) {s t : List (Carrier Z)}
                       →  let open CommMonoid cm ; F = foldr _*_ e in
                           F (s ++ t) ≈⌊ Z ⌋ (F s * F t)
       fold-CM-over-++ {Z} (MkCommMon e _*_ isCommMon) {[]} {t} = sym Z (left-unit isCommMon _)
       fold-CM-over-++ {Z} CMZ@(MkCommMon e _*_ isCommMon) {x ∷ s} {t} = begin⟨ Z ⟩
         let F = foldr _*_ e in
         x * F (s ++ t)  ≈⟨ cong isCommMon (refl Z) (fold-CM-over-++ CMZ ) ⟩
         x * (F s * F t) ≈⟨ sym Z (assoc isCommMon _ _ _)                  ⟩
         (x * F s) * F t ■
       
       fold-permute : {Z : Setoid ℓ (o ⊍ ℓ)} {CM : CommMonoid Z} {s t : List (Carrier Z)}
                      (let open BagEq Z ; open CommMonoid CM)
                    → s ⇔ t
                    → foldr _*_ e s ≈⌊ Z ⌋ foldr _*_ e t
       fold-permute {Z} {MkCommMon e _*_ isCommMon} {s} {t} pf = {!!}
\end{code}

\begin{spec}
      open Locations
      open Membership using (El)
      open ElemOf[]
      fold-permute : {Z : Setoid ℓ o} {CM : CommMonoid Z} {i j : List (Setoid.Carrier Z)} →
        let open BagEq Z in let open CommMonoid CM renaming (_*_ to _+_; e to e₁) in
        i ⇔ j → foldr _+_ e₁ i ≈⌊ Z ⌋ foldr _+_ e₁ j
      fold-permute {Z} {CM} {[]} {[]} i⇔j = Setoid.refl Z
      fold-permute {Z} {CM} {[]} {x ∷ j} i⇔j =
        ⊥-elim (elem-of-[] Z (_≅_.from i⇔j Π.⟨$⟩ El (here (Setoid.refl Z))))
      fold-permute {Z} {CM} {x ∷ i} {[]} i⇔j =
        ⊥-elim (elem-of-[] Z (_≅_.to i⇔j Π.⟨$⟩ El (here (Setoid.refl Z))))
      fold-permute {Z} {CM} {x ∷ i} {x₁ ∷ j} i⇔j = {!!}

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
         elem-of []     ≅˘⟨ ⊥⊥≅elem-of-[] ⟩
         ⊥⊥             ≅⟨ ⊥⊥≅elem-of-[] ⟩
         (elem-of e₁) ∎

      -- in the proof below, *₀ and *₁ are both ++
    ; pres-* = λ {x} {y} →
      elem-of (mapL g (x *₀ y))           ≅⟨ ≡→⇔ (map-++-commute g x y) ⟩
      elem-of (mapL g x *₁ mapL g y) ∎
    }
  ; singleton-commute = λ f {x} → ≅-refl
  ; fold-commute = f-comm
  }
    where
      open ImplementationViaList
      open CommMonoid (Multiset.commMonoid (ListMS X)) renaming (e to e₀; _*_ to _*₀_)
      open CommMonoid (Multiset.commMonoid (ListMS Y)) renaming (e to e₁; _*_ to _*₁_)
      open Membership Y using (elem-of)
      open BagEq Y using (≡→⇔)
      open ElemOfMap
      open ElemOf[] Y
      f-comm : {W : CommMonoid X} {Z : CommMonoid Y} (f : Hom (X , W) (Y , Z))
        {lx : List (Setoid.Carrier X)} →
        Setoid._≈_ Y (foldr (CommMonoid._*_ Z) (CommMonoid.e Z) (mapL (Π._⟨$⟩_ (Hom.mor f)) lx))
                     (Hom.mor f Π.⟨$⟩ foldr (CommMonoid._*_ W) (CommMonoid.e W) lx)
      f-comm {MkCommMon e _*_ isCommMonoid₁} {MkCommMon e₂ _*₂_ isCM₂} f {[]} =
        Setoid.sym Y (Hom.pres-e f)
      f-comm {MkCommMon e _*_ isCommMonoid₁} {MkCommMon e₂ _*₂_ isCM₂} f {x ∷ lx} =
        let g = Π._⟨$⟩_ (Hom.mor f) in  begin⟨ Y ⟩
         ((g x) *₂ (foldr _*₂_ e₂ (mapL g lx)))  ≈⟨ refl ⟨∙⟩ f-comm f {lx} ⟩
         ((g x) *₂ (g (foldr _*_ e lx)))         ≈⟨ sym (Hom.pres-* f) ⟩
         (g (x * foldr _*_ e lx)) ■
        where
          open Setoid Y
          open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_; begin⟨_⟩_) renaming (_∎ to _■)
          open IsCommutativeMonoid isCM₂ using (_⟨∙⟩_)

module BuildProperties where
  open ImplementationViaList
  functoriality : {ℓ o : Level} → FunctorialMSH {ℓ} {o} ListMS ListCMHom
  functoriality {ℓ} {o} = record
    { id-pres = λ {X} {x} → BagEq.≡→⇔ X (map-id x)
    ; ∘-pres = λ {_} {_} {Z} {f} {g} {x} → BagEq.≡→⇔ Z (map-compose x)
    ; resp-≈ = λ {A} {B} {F} {G} F≈G {l} → respect-≈ {F = F} {G} F≈G l
    ; fold-lift-singleton = λ {X} {l} → BagEq.≡→⇔ X (concat-singleton l)
    }
    where
    open Membership
    open Locations using (here; there)
    open Setoid using (Carrier; trans; sym)
    open Multiset using (Ctr; commMonoid)
    respect-≈ : {A B : Setoid ℓ (o ⊍ ℓ)} {F G : A ⟶ B}
      (F≈G : {x : Carrier A} → F Π.⟨$⟩ x ≈⌊ B ⌋ G Π.⟨$⟩ x)
      (lst : Ctr (ListMS A) (Carrier A))
      → mapL (Π._⟨$⟩_ F) lst ≈ mapL (Π._⟨$⟩_ G) lst ∶ commMonoid (ListMS B)
    respect-≈                 F≈G [] = ≅-refl
    respect-≈ {A} {B} {F} {G} F≈G (x ∷ lst) = record
      { to = record { _⟨$⟩_ = to-G ; cong = cong-to-G }
      ; from = record { _⟨$⟩_ = from-G ; cong = cong-from-G }
      ; inverse-of = record { left-inverse-of = left-inv ; right-inverse-of = right-inv } }
        where
          open LocEquiv B
          f = mapL (Π._⟨$⟩_ F)
          g = mapL (Π._⟨$⟩_ G)

          to-G : {l : List (Carrier A)} → elements B (f l) → elements B (g l)
          to-G {[]} (El ())
          to-G {_ ∷ _} (El (here sm)) = El (here (trans B sm F≈G))
          to-G {_ ∷ _} (El (there belongs)) = lift-el B there (to-G (El belongs))

          cong-to-G : {l : List (Carrier A)} {i j : elements B (f l)} → belongs i ≋ belongs j
            → belongs (to-G i) ≋ belongs (to-G j)
          cong-to-G {[]} ()
          cong-to-G {_ ∷ _} (hereEq x≈z y≈z) = LocEquiv.hereEq (trans B x≈z F≈G) (trans B y≈z F≈G)
          cong-to-G {_ ∷ _} (thereEq i≋j) = LocEquiv.thereEq (cong-to-G i≋j)

          from-G : {l : List (Carrier A)} → elements B (g l) → elements B (f l)
          from-G {[]} (El ())
          from-G {_ ∷ _} (El (here sm)) = El (here (trans B sm (sym B F≈G)))
          from-G {_ ∷ xs} (El (there x₁)) = lift-el B there (from-G (El x₁))

          cong-from-G : {l : List (Carrier A)} {i j : elements B (g l)} → belongs i ≋ belongs j
            → belongs (from-G i) ≋ belongs (from-G j)
          cong-from-G {[]} ()
          cong-from-G {_ ∷ _} (hereEq x≈z y≈z) = hereEq (trans B x≈z (sym B F≈G)) (trans B y≈z (sym B F≈G))
          cong-from-G {_ ∷ _} (thereEq loc₁) = thereEq (cong-from-G loc₁)

          left-inv : {l : List (Carrier A)} (y : elements B (mapL (Π._⟨$⟩_ F) l))
            → belongs (from-G (to-G y)) ≋ belongs y
          left-inv {[]} (El ())
          left-inv {_ ∷ _} (El (here sm)) = hereEq (trans B (trans B sm F≈G) (sym B F≈G)) sm
          left-inv {_ ∷ _} (El (there belongs₁)) = thereEq (left-inv (El belongs₁))

          right-inv : {l : List (Carrier A)} (y : elements B (mapL (Π._⟨$⟩_ G) l))
            → belongs (to-G (from-G y)) ≋ belongs y
          right-inv {[]} (El ())
          right-inv {_ ∷ _} (El (here sm)) = hereEq (trans B (trans B sm (sym B F≈G)) F≈G) sm
          right-inv {_ ∷ _} (El (there belongs₁)) = thereEq (right-inv (El belongs₁))
    concat-singleton : {X : Set ℓ} (lst : List X)
      → lst ≡ foldr _++_ [] (mapL (λ x → x ∷ []) lst)
    concat-singleton [] = ≡.refl
    concat-singleton (x ∷ lst) = ≡.cong (λ z → x ∷ z) (concat-singleton lst)
\end{spec}

Last but not least, build the left adjoint:

\begin{spec}
module FreeCommMonoid = BuildLeftAdjoint ImplementationViaList.ListMS ListCMHom
  BuildProperties.functoriality
\end{spec}
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
