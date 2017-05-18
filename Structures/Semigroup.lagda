
%{{{ Imports
\begin{code}
module Structures.Semigroup where

open import Level renaming (suc to lsuc; zero to lzero)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (const ; id ; _∘_)
open import Data.Product          using (_×_; _,_)

open import Function2 using (_$ᵢ)
open import EqualityCombinators
open import Forget
\end{code}
%}}}

%{{{ Semigroup ; _⟨_⟩_ ; Hom

A Free Semigroup is a Non-empty list
\begin{code}
record Semigroup {a} : Set (lsuc a) where
  constructor MkSG
  infixr 5 _*_
  field
    Carrier : Set a
    _*_     : Carrier → Carrier → Carrier
    assoc   : {x y z : Carrier} → x * (y * z) ≡ (x * y) * z

open Semigroup renaming (_*_ to Op)
bop = Semigroup._*_
syntax bop A x y = x ⟨ A ⟩ y

record Hom {ℓ} (Src Tgt : Semigroup {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor   :  Carrier Src → Carrier Tgt
    pres  :  {x y : Carrier Src} → mor (x ⟨ Src ⟩ y)   ≡  (mor x) ⟨ Tgt ⟩ (mor y)

open Hom
\end{code}

%}}}

%{{{ SGAlg ; SemigroupCat ; Forget
\begin{code}
SGAlg : {ℓ : Level} → OneSortedAlg ℓ
SGAlg = record
   { Alg         =   Semigroup
   ; Carrier     =   Semigroup.Carrier
   ; Hom         =   Hom
   ; mor         =   Hom.mor
   ; comp        =   λ F G → MkHom (mor F ∘ mor G) (≡.cong (mor F) (pres G) ⟨≡≡⟩ pres F)
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl
   ; Id-is-id    =   ≐-refl
   }

SemigroupCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
SemigroupCat ℓ = oneSortedCategory ℓ SGAlg

Forget : (ℓ : Level) → Functor (SemigroupCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ SGAlg
\end{code}
%}}}

%{{{ List₁ ; _++_ ; ⟦_,_⟧ ; mapNE ; list₁ ; indNE

The non-empty lists constitute a free semigroup algebra.

They can be presented as |X × List X| or via
|Σ n ∶ ℕ • Σ xs : Vec n X • n ≢ 0|. A more direct presentation would be:

\begin{code}
data List₁ {ℓ : Level} (X : Set ℓ) : Set ℓ where
  [_]  : X → List₁ X
  _∷_  : X → List₁ X → List₁ X
\end{code}

One would expect the second constructor to be an binary operator
that we would somehow (setoids!) cox into being associative. However, were
we to use an operator, then we would lose canonocity. ( Why is it important? )

In some sense, by choosing this particular typing, we are insisting that
the operation is right associative.

This is indeed a semigroup,
\begin{code}
_++_ : {ℓ : Level} {X : Set ℓ} → List₁ X → List₁ X → List₁ X
[ x ] ++ ys    = x ∷ ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : {ℓ : Level} {X : Set ℓ} {xs ys zs : List₁ X}
         → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc {xs = [ x ]}   =  ≡.refl
++-assoc {xs = x ∷ xs}  =  ≡.cong (x ∷_) ++-assoc         

List₁SG : {ℓ : Level} (X : Set ℓ) → Semigroup {ℓ}
List₁SG X = MkSG (List₁ X) _++_ ++-assoc
\end{code}

We can interpret the syntax of a |List₁| in any semigroup provided we have
a function between the carriers. That is to say, a function of sets is freely
lifted to a homomorphism of semigroups.

\begin{code}
⟦_,_⟧ : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′}
    → (wrap : X → Y)
    → (op   : Y → Y → Y)
    → (List₁ X → Y)
⟦ 𝔀 , _𝓸_ ⟧ [ x ]     =  𝔀 x
⟦ 𝔀 , _𝓸_ ⟧ (x ∷ xs)  =  (𝔀 x)  𝓸  (⟦ 𝔀 , _𝓸_ ⟧ xs)

list₁ : {ℓ : Level} {X : Set ℓ} {S : Semigroup {ℓ} }
     →  (X → Carrier S)  →  Hom (List₁SG X) S
list₁ {X = X} {S = S} f = MkHom ⟦ f , Op S ⟧  ⟦⟧-over-++
  where 𝒽  = ⟦ f , Op S ⟧
        ⟦⟧-over-++ : {xs ys : List₁ X} → 𝒽 (xs ++ ys) ≡ (𝒽 xs) ⟨ S ⟩ (𝒽 ys)
        ⟦⟧-over-++ {[ x ]}  = ≡.refl
        ⟦⟧-over-++ {x ∷ xs} = ≡.cong (Op S (f x)) ⟦⟧-over-++ ⟨≡≡⟩ assoc S
\end{code}

In particular, the map operation over lists is:

\begin{code}
mapNE : {a b : Level} {A : Set a} {B : Set b} → (A → B) → List₁ A → List₁ B
mapNE f = ⟦ [_] ∘ f , _++_ ⟧
\end{code}

At the dependent level, we have the induction principle,

\begin{code}
indNE : {a b : Level} {A : Set a} {P : List₁ A → Set b}
      → (base : {x : A} → P [ x ])
      → (ind  : {x : A} {xs : List₁ A} → P [ x ] → P xs → P (x ∷ xs))
      → (xs : List₁ A) → P xs
indNE {P = P} base ind [ x ] = base
indNE {P = P} base ind (x ∷ xs) = ind {x} {xs} (base {x}) (indNE {P = P} base ind xs)
\end{code}

For example, map preserves identity:

\begin{code}
map-id : {a : Level} {A : Set a} → mapNE id ≐ id {A = List₁ A}
map-id = indNE {P = λ xs → mapNE id xs ≡ xs} ≡.refl (λ {x} {xs} refl ind → ≡.cong (x ∷_) ind)

map-∘ : {ℓ : Level} {A B C : Set ℓ} {f : A → B} {g : B → C}
        → mapNE (g ∘ f) ≐ mapNE g ∘ mapNE f
map-∘ {f = f} {g} = indNE {P = λ xs → mapNE (g ∘ f) xs ≡ mapNE g (mapNE f xs)}
                               ≡.refl (λ {x} {xs} refl ind → ≡.cong ((g (f x)) ∷_) ind)

map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
  → f ≐ g → mapNE f ≐ mapNE g
map-cong {f = f} {g} f≐g = indNE {P = λ xs → mapNE f xs ≡ mapNE g xs}
                                 (≡.cong [_] (f≐g _))
                                 (λ {x} {xs} refl ind → ≡.cong₂ _∷_ (f≐g x) ind)
\end{code}

%}}}

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (SemigroupCat ℓ)
Free ℓ = record
  { F₀             =   List₁SG
  ; F₁             =   λ f → list₁ ([_] ∘ f)
  ; identity       =   map-id
  ; homomorphism   =   map-∘
  ; F-resp-≡      =   λ F≈G → map-cong (λ x → F≈G {x})
  }

TreeLeft : ∀ o → Adjunction (Free o) (Forget o)
TreeLeft o = record
  { unit   = record { η = {!!} ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ {(MkSG Carrier _*_ _) → MkHom {!!} {!!}} ; commute = {!!} }
  ; zig = {!!}
  ; zag = {!!} }

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
