\section{Indexed Setoid Equivalence}

%{{{ Imports
\begin{code}
module ISEquiv where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Setoid)

open import Function.Inverse using (_InverseOf_) renaming (Inverse to _≅_; id to ≅-refl)
open import Function.Equality using (_⟨$⟩_; _⟶_; Π; id; _∘_)
\end{code}
%}}}

A |SetoidFamily| (over a |Setoid| S), is a family of |Setoid|s indexed by the carrier of S,
along with a way to ``reindex'' between equivalent members of S.  |reindex| works as expected
with respect to the the equivalences of S.
\begin{code}
record SetoidFamily {ℓS ℓs : Level} (S : Setoid ℓS ℓs) (ℓA ℓa : Level) : Set (ℓS ⊔ ℓs ⊔ suc (ℓA ⊔ ℓa)) where
  open Setoid using () renaming (Carrier to ∣_∣ )
  open Setoid S using (_≈_; refl; sym; trans)
  field
    index : ∣ S ∣ → Setoid ℓA ℓa
    reindex : {x y : ∣ S ∣ } → x ≈ y → index x ⟶ index y
    id-coh : {a : ∣ S ∣ } {b : ∣ index a ∣ } → Setoid._≈_ (index a) (reindex refl ⟨$⟩ b) b
    sym-iso : {x y : ∣ S ∣} → (p : x ≈ y) → reindex (sym p) InverseOf reindex p
    trans-coh : {x y z : ∣ S ∣} {b : ∣ index x ∣} → (p : x ≈ y) → (q : y ≈ z) →
      Setoid._≈_ (index z) (reindex (trans p q) ⟨$⟩ b)
                           (reindex q ∘ reindex p ⟨$⟩ b)
\end{code}

A map |_⇛_| of |SetoidFamily| is a map (aka |_⟶_|) of the underlying setoids,
and |transport|, a method of mapping from |index B x| to the setoid obtained
by shifting from one |Setoid| to another, i.e. |index B' (map ⟨$⟩ x)|.  Lastly,
|transport| and |reindex| obey a commuting law.

\begin{code}
record _⇛_ {ℓS ℓs ℓA ℓa ℓS' ℓs' ℓA' ℓa' : Level} {S : Setoid ℓS ℓs} {S' : Setoid ℓS' ℓs'}
 (B : SetoidFamily S ℓA ℓa ) (B' : SetoidFamily S' ℓA' ℓa') :
   Set (ℓS ⊔ ℓA ⊔ ℓS' ⊔ ℓA' ⊔ ℓa' ⊔ ℓs ⊔ ℓs' ⊔ ℓa) where
 constructor FArr
 open SetoidFamily
 open Setoid using () renaming (Carrier to ∣_∣ )
 open Setoid S using (_≈_)
 field
   map : S ⟶ S'
   transport : (x : ∣ S ∣ ) → index B x ⟶ index B' (map ⟨$⟩ x)
   transport-coh : {y x : ∣ S ∣ } {By : ∣ index B y ∣ } → (p : y ≈ x) →
        Setoid._≈_ (index B' (map ⟨$⟩ x))
          (transport x ⟨$⟩ (reindex B p ⟨$⟩ By))
          (reindex B' (Π.cong map p) ⟨$⟩ (transport y ⟨$⟩ By))
\end{code}

We say that two maps F and G are equivalent (written |F ≈≈ G|) if
there is an (extensional) equivalence between the underlying |Setoid| maps,
and a certain coherence law.

\begin{code}
infix 3 _≈≈_

record _≈≈_ {ℓS ℓs ℓA ℓa ℓS' ℓs' ℓA' ℓa' : Level} {S : Setoid ℓS ℓs} {S' : Setoid ℓS' ℓs'}
  {B : SetoidFamily S ℓA ℓa} {B' : SetoidFamily S' ℓA' ℓa'}
  (F : B ⇛ B') (G : B ⇛ B') : Set (ℓA ⊔ ℓS ⊔ ℓs' ⊔ ℓa') where
   open Setoid using () renaming (Carrier to ∣_∣ )
   open Setoid S using () renaming (_≈_ to _≈₁_)
   open Setoid S' using () renaming (_≈_ to _≈₂_)
   open SetoidFamily
   open _⇛_
   field
     ext : (x : ∣ S ∣ ) → map G ⟨$⟩ x ≈₂ map F ⟨$⟩ x
     transport-ext-coh : (x : ∣ S ∣ ) (Bx : ∣ index B x ∣ ) →
       Setoid._≈_ (index B' (map F ⟨$⟩ x))
         (reindex B' (ext x) ⟨$⟩ (transport G x ⟨$⟩ Bx))
         (transport F x ⟨$⟩ Bx)
\end{code}

|_≈≈_| is an equivalence relation.

\begin{code}
≈≈-refl : {ℓS ℓs ℓA ℓa : Level} {S : Setoid ℓS ℓs} {B : SetoidFamily S ℓA ℓa}
  (F : B ⇛ B) → F ≈≈ F
≈≈-refl {S = S} {B} F = record
  { ext = λ _ → refl ; transport-ext-coh = λ x Bx → id-coh {map F ⟨$⟩ x} {transport F x ⟨$⟩ Bx} }
  where open Setoid S; open SetoidFamily B; open _⇛_

≈≈-sym : {ℓS ℓs ℓA ℓa ℓS' ℓs' ℓA' ℓa' : Level} {S : Setoid ℓS ℓs} {S' : Setoid ℓS' ℓs'}
  {B : SetoidFamily S ℓA ℓa} {B' : SetoidFamily S' ℓA' ℓa'}
  {F : B ⇛ B'} {G : B ⇛ B'} → F ≈≈ G → G ≈≈ F
≈≈-sym {S = S} {S'} {B} {B'} {F} {G} record { ext = ext ; transport-ext-coh = tec } = record
  { ext = λ x → sym (ext x)
  ; transport-ext-coh = λ x Bx → Setoid.trans (index (map G ⟨$⟩ x))
     (Setoid.sym (index (map G ⟨$⟩ x)) (Π.cong (reindex (sym (ext x))) (tec x Bx)))
    ((left-inverse-of (sym-iso (ext x)) (transport G x ⟨$⟩ Bx))) }
  where
   open SetoidFamily B'
   open _InverseOf_
   open Setoid S'
   open _⇛_

≈≈-trans : {ℓS ℓs ℓA ℓa ℓS' ℓs' ℓA' ℓa' ℓS'' ℓs'' ℓA'' ℓa'' : Level}
  {S : Setoid ℓS ℓs} {S' : Setoid ℓS' ℓs'}
  {B : SetoidFamily S ℓA ℓa} {B' : SetoidFamily S' ℓA' ℓa'}
  {F : B ⇛ B'} {G : B ⇛ B'} {H : B ⇛ B'} → F ≈≈ G → G ≈≈ H → F ≈≈ H
≈≈-trans {S' = S'} {B} {B'} {F} {G} {H} F≈G G≈H = record
  { ext = λ x → trans (G=H.ext x) (F=G.ext x)
  ; transport-ext-coh = λ x Bx →
    let open Setoid (index B' (_⇛_.map F ⟨$⟩ x)) renaming (trans to _⟨≈≈⟩_) in
    (SetoidFamily.trans-coh B' (G=H.ext x) (F=G.ext x) ⟨≈≈⟩
    (Π.cong (reindex B' (F=G.ext x)) (G=H.transport-ext-coh x Bx))) ⟨≈≈⟩
    (F=G.transport-ext-coh x Bx)
  }
  where
    open Setoid S'
    open SetoidFamily
    module F=G = _≈≈_ F≈G
    module G=H = _≈≈_ G≈H
\end{code}

If |⇛| is going to be a proper notion of mapping, it should at least have an
identity map as well as composition.  [We might expect more, that it can all be
packaged as a |Category|.  It can, but we don't need it, so we do just the parts
that are needed.

\begin{code}
id⇛ : {ℓS ℓs ℓA ℓa : Level} {S : Setoid ℓS ℓs}
 {B : SetoidFamily S ℓA ℓa} → B ⇛ B
id⇛ {S = S} {B} =
  FArr id (λ _ → reindex refl)
      (λ {y} {x} {By} y≈x → Setoid.trans (index x)
        id-coh
        (Π.cong (reindex y≈x) (Setoid.sym (index y) (id-coh {y} {By}))))
    where
      open SetoidFamily B
      open Setoid S

infixr 9 _∘⇛_

_∘⇛_ : {ℓS ℓs ℓT ℓt ℓU ℓu ℓA ℓa ℓB ℓb ℓC ℓc : Level}
 {S : Setoid ℓS ℓs} {T : Setoid ℓT ℓt} {U : Setoid ℓU ℓu}
 {A : SetoidFamily S ℓA ℓa} {B : SetoidFamily T ℓB ℓb} {C : SetoidFamily U ℓC ℓc} →
 (A ⇛ B) → (B ⇛ C) → (A ⇛ C)
_∘⇛_ {A = A} {B} {C} A⇛B B⇛C = FArr (G.map ∘ F.map) (λ x → G.transport (F.map ⟨$⟩ x) ∘ F.transport x)
  (λ {y} {x} {By} y≈x →
  let open Setoid (index C (G.map ∘ F.map ⟨$⟩ x)) renaming (trans to _⟨≈≈⟩_) in
  Π.cong (G.transport (F.map ⟨$⟩ x)) (F.transport-coh {By = By} y≈x) ⟨≈≈⟩
  G.transport-coh (Π.cong F.map y≈x))
  where
    module F = _⇛_ A⇛B
    module G = _⇛_ B⇛C
    open SetoidFamily
\end{code}

Lastly, we need to know when two |SetoidFamily| are equivalent.  In fact, we'll use
a quasi-equivalence (we have no need for it to be a proposition).  So we'll
need two maps back and forth, and show that they compose to the identity, up to
equivalence of maps.

\begin{code}
infix 3 _♯_

record _♯_ {ℓS ℓs ℓA ℓa ℓS' ℓs' ℓA' ℓa' : Level} {S : Setoid ℓS ℓs} {S' : Setoid ℓS' ℓs'}
 (From : SetoidFamily S ℓA ℓa ) (To : SetoidFamily S' ℓA' ℓa')
 : Set (ℓS ⊔ ℓA ⊔ ℓS' ⊔ ℓs ⊔ ℓa ⊔ ℓA' ⊔ ℓs' ⊔ ℓa') where
 field
    to         : From ⇛ To
    from       : To ⇛ From
    left-inv   : from ∘⇛ to ≈≈ id⇛ {B = To}
    right-inv  : to ∘⇛ from ≈≈ id⇛ {B = From}
\end{code}

We need to show that |_♯_| is also an equivalence relation too.
Luckily, all the hard work has been done already.

{-
infixr 2 _♯⟨_⟩_ _♯˘⟨_⟩_

infix  4 _Is♯To_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _Is♯To_ {f₁ f₂ t₁ t₂ : Level}
       (From : I.Setoid (Setoid.Carrier S) f₁ f₂)
       (To : I.Setoid (Setoid.Carrier S) t₁ t₂) : Set (ℓS ⊔ ℓs ⊔ f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  relTo : (x♯y : From ♯ To) → From Is♯To To

begin_ : {f₁ f₂ t₁ t₂ : Level}
       {From : I.Setoid (Setoid.Carrier S) f₁ f₂}
       {To : I.Setoid (Setoid.Carrier S) t₁ t₂}
       → From Is♯To To → From ♯ To
begin relTo x♯y = x♯y

_♯⟨_⟩_ : {a₁ a₂ b₁ b₂ c₁ c₂ : Level}
  (A : I.Setoid (Setoid.Carrier S) a₁ a₂)
  {B : I.Setoid (Setoid.Carrier S) b₁ b₂}
  {C : I.Setoid (Setoid.Carrier S) c₁ c₂}
      →  A ♯ B → B Is♯To C → A Is♯To C
_♯⟨_⟩_ A {B} {C} A♯B (relTo B♯C) = relTo (ISE-trans A♯B B♯C)
  where open ISE-Trans S A B C

_♯˘⟨_⟩_ : {a₁ a₂ b₁ b₂ c₁ c₂ : Level}
  (A : I.Setoid (Setoid.Carrier S) a₁ a₂)
  {B : I.Setoid (Setoid.Carrier S) b₁ b₂}
  {C : I.Setoid (Setoid.Carrier S) c₁ c₂}
      →  B ♯ A → B Is♯To C → A Is♯To C
_♯˘⟨_⟩_ A {B} {C} B♯A (relTo B♯C) = relTo (ISE-trans (ISE-sym B♯A) B♯C)
  where open ISE-Trans S A B C; open ISE-Combinators S B A
-}

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
