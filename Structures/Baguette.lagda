\section{Structures.Baguette}

New experimental variation on |Structures.Multiset| using Brad Hardy's work.


A “baguette” is a long and narrow loaf of French bread.
The same modifiers are used to describe the final piece of this project.

Alternatively, a “baguette” is a form of gem, as is this the project's remaining hole.

On a completely unrelated matter, we're running out of names since
we already have files named “multiset” and “bag” in the experimental directory.

%{{{ Precisé

\begin{enumerate}

\item |IsCtrEquivalence 𝒞| is a proof that data-type constructor |𝒞| endows types with equivalence relations. We show how lists with bag equality are such an instance: |Bag-isCtrEquivalence|.

\item |CommutativeContainer| is a essentially a tuple |(𝒞, ø, _⊕_)| consisting of a container equivalence |𝒞|
      along with an “empty container” |ø| and a “container union” |_⊕_| operation such that the type
      transformer |𝒞| endows types with a commutative monoid structure.

      We relise that bags, implemented as lists with usual catenation, are such an instance:
      |Bag-CommutativeContainer|.

\item |Multiset| is a type transformer furnishing a (setoid) carrier type with a commutative container
      transformer |𝒞|, a way to embed the carrier into into its associated container (|singleton|),
      a polymoprhic operation, “fold”, that reifies commutative container values (terms)
      as values in any given commutative monoid such that the “one point rule” holds:
      The |fold| of a |singleton| is just the carrier element being injected into the carrier.

      That the one point rule holds ensures that the |singleton| embedding is in-fact injective
      ---provided our carrier type admits a commutative monoid structure at all; this is also
      a technical proviso for the one point rule.

\item |MultisetHom| consist of a method of |lift|ing functions between types to be between multisets
      which are compatible with the |singleton| and |fold| operations.

      ( Later we show, in |ListCMHom|, that lists with their usual
        map operation result in such a structure --with bag equality. )

      The expected Functorialty conditions are, for now, in their own record: |FunctorialMSH|.

\item |BuildLeftAdjoint|: Provided we have implementations of the multiset transformers we can
      produce a |Free| functor from category of setoids to the category of commutative monoids.

\item |ImplementationViaList|: An implementation of |Multiset| using lists with Bag equality
\end{enumerate}

%}}}

%{{{ Imports
\begin{code}
module Structures.Baguette where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)

open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)
open Π                        using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open import Algebra           using (Monoid ; CommutativeMonoid ; CommutativeSemiring)
open import Relation.Binary   using (Setoid; Rel; IsEquivalence)
open Setoid                   using (Carrier)

open import Data.List  using ([]; [_]; _++_; _∷_)  renaming (map to mapL)
open import Data.List.Properties using (map-++-commute; map-id; map-compose)
import Data.List as List

open import Data.Sum using ([_,_]′)

open import DataProperties hiding (⟨_,_⟩ ; ⊎-cong)
open import SetoidEquiv
open import ParComp
open import EqualityCombinators
open import Structures.CommMonoid renaming (Hom to CMArrow)

open import FinEquivPlusTimes using (module Plus)
open Plus using (+≃⊎)

open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
open CommMonoid using (eq-in ; isCommMonoid)

-- open import Data.List.Any
-- open import Function.Related hiding (_∼[_]_)
-- open import Function.Related.TypeIsomorphisms
-- module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
open import Relation.Binary.SetoidReasoning renaming (_∎ to _■₀)

open import Function.Inverse using (_↔_)
open import Data.List.Any.Properties hiding (map-id)
open import Function using (_$_)
-- open import Function.Related hiding (_∼[_]_) ; open EquationalReasoning renaming (_∎ to _■) hiding (sym)
-- module ↔ = EquationalReasoning
-- open import Function.Inverse public using () renaming  (id to  ↔-refl)

-- multiset type
open import Structures.SequencesAsBags as Seq using (table ; table˘ ; BagSetoid) renaming (Seq to Bag)

bag-eq : {ℓ c : Level} (X : Setoid ℓ c) (f g : Bag (Setoid.Carrier X)) → Set (c ⊍ ℓ)
bag-eq X = Setoid._≈_ (BagSetoid X)

infix -666 bag-eq
syntax bag-eq X s t  =  s ≈ₘ t ∶ X   -- ghost colon
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

  -- handy dandy syntactic sugar for |k|ontainer equality.
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

Bag-isCtrEquivalence : (ℓ c : Level) → IsCtrEquivalence {ℓ} c Bag
Bag-isCtrEquivalence ℓ c = record
  { equiv        = λ X → Setoid._≈_ (BagSetoid X)
  ; equivIsEquiv = λ X → Setoid.isEquivalence (BagSetoid X)
  }
\end{code}
%}}}

%{{{ CommutativeContainer

In the same vein as before, we consider a setoid-polymorphic equivalence relation that
also furnishes a raw type with a commutative monoid structure. That is, we now have
the object-component of a functor from the category of setoids to the category of
commutative monoids.

\begin{code}
record CommutativeContainer (ℓ c : Level) : Set (lsuc ℓ ⊍ lsuc c) where
  open IsCtrEquivalence using (equiv)
  field
    𝒞                    : Set ℓ → Set ℓ
    isCtrEquivalence     :  IsCtrEquivalence c 𝒞
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

Bag-CommutativeContainer : (ℓ c : Level) → CommutativeContainer ℓ c
Bag-CommutativeContainer ℓ c = record
  { 𝒞 = Bag
  ; isCtrEquivalence = Bag-isCtrEquivalence ℓ c
  ; ∅   = λ {X} → Seq.∅
  ; _⊕_ = λ {X} → Seq._⊕_
  ; isCommutativeMonoid = λ {X} →
      let open CommutativeMonoid (Seq.commutativeMonoid X) in record
      { left-unit   =  identityˡ
      ; right-unit  =  proj₂ identity
      ; assoc       =  assoc
      ; comm        =  comm
      ; _⟨∙⟩_       =  ∙-cong
      }
  }
\end{code}
%}}}

%{{{ Multiset
\subsection{Multiset}
A “multiset on type X” is a structure on which one can define
\begin{itemize}
\item a \emph{commutative monoid} structure,
\item implement the concept of ``wrapping an element up as a \emph{singleton} container''
\item implement the concept of \emph{fold}; note that the name
is inspired by its implementation in the main model.  Its signature
would have suggested ``extract'', but this would have been
quite misleading.

  That is to say, we wish to have an operation |fold : ⦃x₁, …, xₙ⦄ ↦ x₁ ⊕ ⋯ ⊕ xₙ|
  where |⦃⋯⦄| are multi-set brackets and so order is irrelevant, but multiplicity matters.

  Really, we are asking for a way to ``form finite sums'' on the multiset.
\end{itemize}

\begin{code}
record Multiset {ℓ c : Level} (X : Setoid ℓ (c ⊍ ℓ)) : Set (lsuc ℓ ⊍ lsuc c) where
  field
    commutativeContainer : CommutativeContainer ℓ c

  open CommutativeContainer commutativeContainer     public
  open Setoid X using (_≈_) renaming (Carrier to X₀)

  field
    singleton       :  X ⟶ ctrSetoid X             -- A setoid map
    fold            :  {Y : Setoid ℓ (c ⊍ ℓ)} (CMY : CommMonoid Y) → CMArrow (commMonoid Y) CMY
    fold-singleton  :  {CM : CommMonoid X} {x : X₀} → x ≈ fold CM ⟨$⟩ (singleton ⟨$⟩₀ x)

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|, and |𝒮| for referring to a multiset's singleton embedding operation.

  -- |𝓜 : CommMonoid (ctrSetoid X)|
  -- |𝓜 = commMonoid X|

  𝒮 : X₀ → 𝒞 X₀
  𝒮 x = singleton ⟨$⟩₀ x

  singleton-injective : (CM : CommMonoid X) {x y : X₀}
                      → 𝒮 x ≈ 𝒮 y ∶ commMonoid X  →  x ≈ y
  singleton-injective CM {x} {y} 𝒮x≈𝒮y = begin⟨ X ⟩
      x
    ≈⟨ fold-singleton ⟩
      fold CM  ⟨$⟩  𝒮 x
    ≈⟨ CMArrow.cong (fold CM) 𝒮x≈𝒮y ⟩
      fold CM  ⟨$⟩  𝒮 y
    ≈˘⟨ fold-singleton ⟩
      y
    ■
    where open import Relation.Binary.SetoidReasoning using (_≈⟨_⟩_; begin⟨_⟩_) renaming (_∎ to _■)

-- MA: Define and discuss,
  -- |_⊕₀_ : X₀ → X₀ → 𝒞 X₀|
  -- |x ⊕₀ y = fold {!commMonoid ?!} ⟨$⟩ ( (singleton ⟨$⟩₀ x) ⊕ (singleton ⟨$⟩₀ y) )|
\end{code}

A “multiset homomorphism” is a way to lift arbitrary (setoid) functions on the carriers
to be homomorphisms on the underlying commutative monoid structure, as well as a few
compatibility laws.

In the classical contexts of sets and set-functions, the constraints take the form:
|{ f x } ≈ lift f { x }| and |fold (lift f s) ≈ f (fold s)|. In particular, the |lift| operation
mimics the behaviour of the morphism, or “map”, portion of a functor.

\begin{code}
record MultisetHom {ℓ c : Level} {X Y : Setoid ℓ (c ⊍ ℓ)} (X* : Multiset X) (Y* : Multiset Y)
  : Set (lsuc ℓ ⊍ lsuc c) where
  open Multiset {ℓ} {c}
  X₀ = Setoid.Carrier X
  open Setoid Y using (_≈_)

  -- Let's introduce two handy combinators: |𝓜| for referring to the underlying commutative monoid
  -- structure of a |Multiset|.
  private
    𝓜 = λ {Z : Setoid ℓ (c ⊍ ℓ)} (CMZ : Multiset Z) → commMonoid CMZ Z

  field
    lift : (X ⟶ Y) → CMArrow (𝓜 X*) (𝓜 Y*)

    -- This ensures that |singleton| is sufficiently polymorphic; i.e., a natural transformation.
    -- See the Adjunction below.
    singleton-commute : (F : X ⟶ Y) {x : X₀} → 𝒮 Y* (F ⟨$⟩₀ x) ≈ lift F ⟨$⟩ (𝒮 X* x)  ∶  𝓜 Y*

    fold-commute : {CMX : CommMonoid X} {CMY : CommMonoid Y} (F : CMArrow CMX CMY)
                 → {s : 𝒞 X* X₀}
                 → fold Y* CMY ⟨$⟩ (lift (mor F) ⟨$⟩ s)  ≈  F ⟨$⟩ (fold X* CMX ⟨$⟩ s)
                 -- MA: This is ``precisely'' the condition that |F| is a homomorphism!
                 -- Instead of requesting `F (x ⊕ y) ≈ F x ⊕ F y ∧ F ε ≈ ε`, we ask for
                 -- `F (x₁ ⊕ ⋯ ⊕ xₙ) ≈ F x₁ ⊕ ⋯ ⊕ F xₙ` for any `n : ℕ`.
\end{code}

\edcomm{MA}{

From Bird's theory of lists we know that every list homomorphism is the composition of a fold
after a map. Now a fold usually serves to realise an algebra as being initial and so ``least'' in some
sense. As such, perhaps it'd be beneficial to request every |CMArrow (commMonoid Y) CMY|
be expressible as a |fold|?

}%edcomm

And now something somewhat different: To express that we have the right
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

    -- 𝑳ift and apply onto the ₘultiset.
    𝑳ₘ  = λ {X Y : Obj}  (F   : X ⟶ Y) (x : 𝒞ₘ X) → lift MSH F ⟨$⟩ x

    infix 0 _≋_
    _≋_ = λ {X : Obj} (l r : 𝒞ₘ X) → l ≈ r ∶ 𝓜 X

  field
    -- Lifting the identity yields an identity morphism.
    id-pres : {X : Obj} → {x : 𝒞ₘ X} → 𝑳ₘ id x  ≋  x

    -- Lifting preserves composition.
    ∘-pres : {X Y Z : Obj} {F : X ⟶ Y} {G : Y ⟶ Z}
           → {x : 𝒞ₘ X} → 𝑳ₘ (G ∘ F) x  ≋  𝑳ₘ G (𝑳ₘ F x)

    -- Lifting preserves extensional equality.
    resp-≈ : {X Y : Obj} {F G : X ⟶ Y} (let open Setoid Y renaming (_≈_ to _≈₀_))
          → (F≈G : {x : Carrier X} → F ⟨$⟩₀ x ≈₀ G ⟨$⟩₀ x)
          → {x : 𝒞ₘ X} → 𝑳ₘ F x  ≋  𝑳ₘ G x

    -- Lifting the singleton mapping then folding yields the orginal result.
    -- In particular, the singleton construction is injective --as we'd like.
    fold-lift-singleton : {X : Obj} (let ms = MS X ; _≈_ = equiv (isCtrEquivalence ms) X)
      → {s : 𝒞ₘ X} → s ≈ (fold (MS (ctrSetoid ms X)) (𝓜 X) ⟨$⟩ (𝑳ₘ (singleton ms) s))
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

  module _ {ℓ c} {X : Setoid ℓ (ℓ ⊍ c)} where open Multiset {ℓ} {c} (MS X) public
  module _ {ℓ c} {X Y : Setoid ℓ (ℓ ⊍ c)} where open MultisetHom (MSH {ℓ} {c} {X} {Y}) public
  module _ {ℓ c} where open FunctorialMSH {ℓ} {c} Func public

  Free : (ℓ c : Level) → Functor (Setoids ℓ (ℓ ⊍ c)) (CommMonoidCat ℓ (ℓ ⊍ c))
  Free ℓ c = record
    { F₀             =   λ S → ctrSetoid {ℓ} {c} S , commMonoid S
    ; F₁             =   λ F → record { CMArrow (lift F) }
    ; identity       =   id-pres
    ; homomorphism   =   ∘-pres
    ; F-resp-≡      =   resp-≈
    }

  LeftAdjoint : {ℓ c : Level} → Adjunction (Free ℓ c) (Forget ℓ (ℓ ⊍ c))
  LeftAdjoint = record
    { unit = record
      { η = λ _ → singleton
      ; commute = singleton-commute
      }
    ; counit = record
      { η        =  λ { (_ , cm) → record { CMArrow (fold cm) } }
      ; commute  =  fold-commute
      }
    ; zig = fold-lift-singleton
    ; zag = λ { {X , _} → fold-singleton {X = X} }
    }
\end{code}
%}}}

%{{{ An implementation of |Multiset| using lists with Bag equality
\subsection{An implementation of |Multiset| using lists with Bag equality}
\begin{code}
module CMUtils {ℓ c : Level} {S : Setoid ℓ c} (CMS : CommMonoid S) where
  open Setoid S using (_≈_) renaming (Carrier to S₀)
  open CommMonoid CMS renaming (_*_ to _+_)
  open import Data.Table.Base
  open import Algebra.Operations.CommutativeMonoid (asCommutativeMonoid CMS)
  open import Algebra.Properties.CommutativeMonoid (asCommutativeMonoid CMS)

  sumₛ : Bag S₀ → S₀
  sumₛ = λ f → sumₜ (table f)

  -- In a commutative monoid, if you add up everything in two sequences that contain
  -- the same elements, you get the same result.
  sumₛ-cong : {f g : Bag S₀} → f ≈ₘ g ∶ S → sumₛ f ≈ sumₛ g
  sumₛ-cong {f} {g} (s Seq.⟨π⟩ f≈sg) = let open Setoid S in begin⟨ S ⟩
      sumₛ f
    ≈⟨ refl ⟩
      sumₜ (table f)
    ≈⟨ sumₜ-cong {Seq.len f} {table f} {table (s Seq.◈ g)} f≈sg ⟩
      sumₜ (table (s Seq.◈ g))
    ≈⟨ sym (sumₜ-permute′ {Seq.len f} {Seq.len g} (table g) s)   ⟩
      sumₜ (table g)
    ≈⟨ refl ⟩
      sumₛ g
    ■₀

  -- Since JC provided the definition of _⊕_, he may be able to make this postulate go through?
  --
  --
  -- The |sumₛ| operator distributes over addition.
  postulate sumₛ-homo : {f g : Bag S₀} → sumₛ (f Seq.⊕ g) ≈ sumₛ f + sumₛ g -- c.f., fold-CM-over-++ below.
{-
  sumₛ-homo {f} {g} = let open Setoid S in begin⟨ S ⟩
      sumₛ (f Seq.⊕ g)
    ≈⟨ {!!} ⟩
      sumₛ (sequence (Seq.len f + Seq.len g) λ i → [ f ‼_ , g ‼_ ]′ (proj₁ +≃⊎ i))
    ≈⟨ {!!} ⟩
      sumₛ f + sumₛ g
    ■₀
-}

{- older attempt:
  sumₛ-homo {f} {g} = let open Setoid S in begin⟨ S ⟩
      sumₛ (f Seq.⊕ g)
    ≈⟨ {!_‼_!} ⟩
      sumₜ {!!}
    ≈⟨ sym {!∑-+-hom (Seq.len (f Seq.⊕ g)) !} ⟩
      sumₜ (table f) + sumₜ (table g)
    ≈⟨ refl ⟩
      sumₛ f + sumₛ g
    ■₀
-}

module ImplementationViaList {ℓ c : Level} (X : Setoid ℓ (c ⊍ ℓ)) where
  open Setoid

  ListMS : Multiset {ℓ} {c ⊍ ℓ} X
  ListMS = record
    { commutativeContainer   =   Bag-CommutativeContainer ℓ (c ⊍ ℓ)
    ; singleton              =   record { _⟨$⟩_ = Seq.singleton X ; cong = Seq.singleton-cong X }
    ; fold  =   λ {Y} CMY → let open CMUtils CMY in record
      { mor      =   record { _⟨$⟩_ = sumₛ ; cong = sumₛ-cong }
      ; pres-e   =   Setoid.refl Y
      ; pres-*   =   λ {f} {g} → sumₛ-homo {f} {g} -- fold-CM-over-++ CMY
      }
    ; fold-singleton         =   λ {CMX} {x} → Setoid.sym X (CommMonoid.right-unit CMX x)
    }
\end{code}
\begin{spec}
    where

      open import Data.Table.Base

      open IsCommutativeMonoid using (left-unit ; right-unit ; assoc) renaming (_⟨∙⟩_ to cong)

      fold-CM-over-++ : {Z : Setoid ℓ (ℓ ⊍ c)} (cm : CommMonoid Z) {s t : Bag (Carrier Z)}
                      →  let open CommMonoid cm ; F = λ f → foldr _*_ e (table f) in
                          F (s Seq.⊕ t) ≈⌊ Z ⌋ (F s * F t)
      fold-CM-over-++ {Z} cm {s} {t} = {!!}
{-
      fold-CM-over-++ {Z} (MkCommMon e _*_ isCommMon) {[]} {t} = sym Z (left-unit isCommMon _)
      fold-CM-over-++ {Z} CMZ@(MkCommMon e _*_ isCommMon) {x ∷ s} {t} = begin⟨ Z ⟩
        let F = List.foldr _*_ e in
        x * F (s ++ t)   ≈⟨ cong isCommMon (refl Z) (fold-CM-over-++ CMZ ) ⟩
        x * (F s * F t)  ≈⟨ sym Z (assoc isCommMon _ _ _)                  ⟩
        (x * F s) * F t  ■₀
-}
\end{spec}

\begin{code}
open ImplementationViaList

open import Data.Table.Base

apply-map : {ℓ ℓ′ : Level} {X Y : Setoid ℓ ℓ} {Z W : Set ℓ′} {g : Z → Carrier X} {h : W → Carrier X} →
  (f : X ⟶ Y) → (c : Z ⊎ W) → Setoid._≈_ Y (f ⟨$⟩₀ ([ g , h ]′ c)) ([ (λ x → f ⟨$⟩₀ (g x)), (λ x → f ⟨$⟩₀ (h x)) ]′ c)
apply-map {Y = Y} f (inj₁ x) = Setoid.refl Y
apply-map {Y = Y} f (inj₂ y) = Setoid.refl Y

ListCMHom : {ℓ : Level} {X Y : Setoid ℓ ℓ} → MultisetHom (ListMS {ℓ} {ℓ} X) (ListMS {ℓ} {ℓ} Y)
ListCMHom {ℓ} {X} {Y} = record
  { lift =   λ f → let mapf = λ x → table˘ (map (f ⟨$⟩₀_) (table x)) in record
    { mor      =   record
      { _⟨$⟩_ = mapf
      ; cong  = λ i≈ₛj → Seq._≈ₛ_.shuffle i≈ₛj Seq.⟨π⟩ (λ a → Π.cong f (Seq._≈ₛ_.eq i≈ₛj a))
      }
    ; pres-e   =   Function.Inverse.id Seq.⟨π⟩ λ ()
    ; pres-*   =   λ {xs ys} → Function.Inverse.id Seq.⟨π⟩ λ i → apply-map f (proj₁ +≃⊎ i)
    }
  ; singleton-commute   =   λ F → Seq.≈ₛ-refl Y
  ; fold-commute        =   λ {CMX} {CMY} F {s} → it {CMX = CMX} {CMY} F s
  }
  where
    open Setoid Y
    open import Data.Nat using (zero; suc)
    import Data.Fin as Fin
    -- Proving |foldr _*₂_ e₂ (mapL (F ⟨$⟩_) xs)  ≈ F ⟨$⟩ foldr _*₁_ e₁ xs|.
    it : {ℓ : Level} {X Y : Setoid ℓ ℓ} {CMX : CommMonoid X} {CMY : CommMonoid Y}
         (F : CMArrow CMX CMY) (s : Bag (Carrier X))
         → foldr (CommMonoid._*_ CMY) (CommMonoid.e CMY) (tabulate (λ x → mor F ⟨$⟩₀ (s Bag.‼ x)))  ≈⌊ Y ⌋
           mor F ⟨$⟩₀ foldr (CommMonoid._*_ CMX) (CommMonoid.e CMX) (tabulate (Bag._‼_ s))
    it {ℓ} {X} {Y} {MkCommMon e₁ _*₁_ _} {MkCommMon e₂ _*₂_ isCM₂} F (Bag.sequence zero fun) = Setoid.sym Y (pres-e F)
    it {ℓ} {X} {Y} {MkCommMon e₁ _*₁_ _} {MkCommMon e₂ _*₂_ isCM₂} F (Bag.sequence (suc len) fun) = {!!} {-
        begin⟨ Y ⟩
           (F ⟨$⟩ x)  *₂  foldr CMY (mapL (F ⟨$⟩_) xs)
        ≈⟨ refl ⟨∙⟩ it F ⟩
           (F ⟨$⟩ x)  *₂  (F ⟨$⟩ foldr CMX xs)
        ≈˘⟨ pres-* F ⟩
           F ⟨$⟩ (x *₁ foldr CMX xs)
        ■₀ -}
        where open IsCommutativeMonoid isCM₂ using (_⟨∙⟩_)
              open CMUtils
\end{code}

\begin{spec}
-- \edcomm{MA}{Should be moved into a List-like library. Maybe moved to the standard library.}
--
-- Transforming a list into singletons then catenating is the same as “doing nothing.”
concat-singleton : {ℓ : Level} {X : Set ℓ} (xs : List.List X)
                 → xs ≡ List.foldr _++_ [] (mapL [_] xs)
concat-singleton []         =   ≡.refl
concat-singleton (x ∷ xs)   =   ≡.cong (x ∷_) (concat-singleton xs)

module BuildProperties where
  open ImplementationViaList
  functoriality : {ℓ : Level} → FunctorialMSH {ℓ} (ListMS {ℓ} {ℓ}) ListCMHom
  functoriality {ℓ} = record
    { id-pres               =   λ {X} {xs} → {!!} -- ∈-↔-reflexive X (map-id xs)
    ; ∘-pres                =   λ {_} {_} {Z} {F} {G} {xs} → {!!}
    ; resp-≈                =   λ {X} {Y} {f} {g} F≈G {xs} → {!!}
    ; fold-lift-singleton   =   λ {X} {xs} → {!!}
    }
    where
    open Multiset using (𝒞; commMonoid)
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
