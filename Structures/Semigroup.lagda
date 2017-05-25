
%{{{ Imports
\begin{code}
module Structures.Semigroup where

open import Level renaming (suc to lsuc; zero to lzero)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor ; Faithful)
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

Forget-isFaithful : {ℓ : Level} → Faithful (Forget ℓ)
Forget-isFaithful F G F≈G = λ x → F≈G {x}
\end{code}
%}}}

%{{{ List₁ ; _++_ ; ⟦_,_⟧ ; mapNE ; list₁ ; indNE

The non-empty lists constitute a free semigroup algebra.

They can be presented as |X × List X| or via
|Σ n ∶ ℕ • Σ xs : Vec n X • n ≢ 0|. A more direct presentation would be:

\begin{code}
data List₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
  [_]  : A → List₁ A
  _∷_  : A → List₁ A → List₁ A

rec : {ℓ ℓ′ : Level} {Y : Set ℓ} {X : List₁ Y → Set ℓ′}
    → (wrap : (y : Y) → X [ y ])
    → (cons : (y : Y) (ys : List₁ Y) → X ys → X (y ∷ ys))
    → (ys : List₁ Y) → X ys
rec w c [ x ]      =   w x
rec w c (x ∷ xs)   =   c x xs (rec w c xs)

[]-injective : {ℓ : Level} {A : Set ℓ} {x y : A} → [ x ] ≡ [ y ] → x ≡ y
[]-injective ≡.refl = ≡.refl
\end{code}

One would expect the second constructor to be an binary operator
that we would somehow (setoids!) cox into being associative. However, were
we to use an operator, then we would lose canonocity. ( Why is it important? )

In some sense, by choosing this particular typing, we are insisting that
the operation is right associative.

This is indeed a semigroup,
\begin{code}
_++_ : {ℓ : Level} {X : Set ℓ} → List₁ X → List₁ X → List₁ X
xs ++ ys = rec (_∷ ys) (λ x xs' res → x ∷ res) xs
-- [ x ] ++ ys    = x ∷ ys
-- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : {ℓ : Level} {X : Set ℓ} {xs ys zs : List₁ X}
         → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc {xs = xs} {ys} {zs} = rec {X = λ xs → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs} ≐-refl (λ x xs' ind → ≡.cong (x ∷_) ind) xs         
-- ++-assoc {xs = [ x ]}   =  ≡.refl
-- ++-assoc {xs = x ∷ xs}  =  ≡.cong (x ∷_) ++-assoc         

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
⟦ w , o ⟧ = rec w (λ x xs res → o (w x) res)
-- ⟦ 𝔀 , _𝓸_ ⟧ [ x ]     =  𝔀 x
-- ⟦ 𝔀 , _𝓸_ ⟧ (x ∷ xs)  =  (𝔀 x)  𝓸  (⟦ 𝔀 , _𝓸_ ⟧ xs)

list₁ : {ℓ : Level} {X : Set ℓ} {S : Semigroup {ℓ} }
     →  (X → Carrier S)  →  Hom (List₁SG X) S
list₁ {X = X} {S = S} f = MkHom ⟦ f , Op S ⟧  ⟦⟧-over-++
  where 𝒽  = ⟦ f , Op S ⟧
        ⟦⟧-over-++ : {xs ys : List₁ X} → 𝒽 (xs ++ ys) ≡ (𝒽 xs) ⟨ S ⟩ (𝒽 ys)
        ⟦⟧-over-++ {xs} {ys} = rec {X = λ xs → 𝒽 (xs ++ ys) ≡ (𝒽 xs) ⟨ S ⟩ (𝒽 ys)}
                                   ≐-refl (λ x xs' ind → ≡.cong (Op S (f x)) ind ⟨≡≡⟩ assoc S) xs
--        ⟦⟧-over-++ {[ x ]}  = ≡.refl
--        ⟦⟧-over-++ {x ∷ xs} = ≡.cong (Op S (f x)) ⟦⟧-over-++ ⟨≡≡⟩ assoc S
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
indNE base ind = rec (λ y → base) (λ y ys → ind base)
-- indNE {P = P} base ind [ x ] = base
-- indNE {P = P} base ind (x ∷ xs) = ind {x} {xs} (base {x}) (indNE {P = P} base ind xs)
\end{code}

For example, map preserves identity:

\begin{code}
map-id : {a : Level} {A : Set a} → mapNE id ≐ id {A = List₁ A}
map-id = indNE ≡.refl (λ {x} {xs} refl ind → ≡.cong (x ∷_) ind)

map-∘ : {ℓ : Level} {A B C : Set ℓ} {f : A → B} {g : B → C}
        → mapNE (g ∘ f) ≐ mapNE g ∘ mapNE f
map-∘ {f = f} {g} = indNE ≡.refl (λ {x} {xs} refl ind → ≡.cong ((g (f x)) ∷_) ind)

map-cong : {ℓ : Level} {A B : Set ℓ} {f g : A → B}
  → f ≐ g → mapNE f ≐ mapNE g
map-cong {f = f} {g} f≐g = indNE (≡.cong [_] (f≐g _))
                                 (λ {x} {xs} refl ind → ≡.cong₂ _∷_ (f≐g x) ind)
\end{code}

%}}}

%{{{ Free ; TreeLeft   wrt  SETS
\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (SemigroupCat ℓ)
Free ℓ = record
  { F₀             =   List₁SG
  ; F₁             =   λ f → list₁ ([_] ∘ f)
  ; identity       =   map-id
  ; homomorphism   =   map-∘
  ; F-resp-≡      =   λ F≈G → map-cong (λ x → F≈G {x})
  }

Free-isFaithful : {ℓ : Level} → Faithful (Free ℓ)
Free-isFaithful F G F≈G {x} = []-injective (F≈G [ x ])

TreeLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
TreeLeft ℓ = record
  { unit   = record { η = λ _ → [_] ; commute = λ _ → ≡.refl }
  ; counit = record
    { η       = λ S → list₁ id
    ; commute = λ {X} {Y} F  → rec ≐-refl (λ x xs ind → ≡.cong (Op Y (mor F x)) ind ⟨≡≡˘⟩ pres F)
    }
  ; zig = rec ≐-refl (λ x xs ind → ≡.cong (x ∷_) ind)
  ; zag = ≡.refl
  }
\end{code}

ToDo ∷ Discuss streams and their realisation in Agda.

%}}}

%{{{ Free ; TreeLeft   wrt  MAGMA
\begin{code}
open import Structures.Magma renaming (Hom to MagmaHom)
open MagmaHom using () renaming (mor to morₘ)

ForgetM : (ℓ : Level) → Functor (SemigroupCat ℓ) (MagmaCat ℓ)
ForgetM ℓ = record
  { F₀             =   λ S → MkMagma (Carrier S) (Op S)
  ; F₁             =   λ F → MkHom (mor F) (pres F)
  ; identity       =   ≐-refl
  ; homomorphism   =   ≐-refl
  ; F-resp-≡      =   id
  }

ForgetM-isFaithful : {ℓ : Level} → Faithful (ForgetM ℓ)
ForgetM-isFaithful F G F≈G = λ x → F≈G x
\end{code}

Even though there's essentially no difference between the homsets of MagmaCat and SemigroupCat,
I ``feel'' that there ought to be no free functor from the former to the latter.
More precisely, I feel that there cannot be an associative “extension” of an arbitrary binary operator;
see _⟪_ below.

\begin{code}
open import Relation.Nullary
open import Categories.NaturalTransformation hiding (id ; _≡_)
NoLeft : {ℓ : Level} (FreeM : Functor (MagmaCat lzero) (SemigroupCat lzero)) → Faithful FreeM → ¬ (Adjunction FreeM (ForgetM lzero))
NoLeft FreeM faithfull Adjunct = ohno (inj-is-injective crash)
  where open Adjunction Adjunct
        open NaturalTransformation
        open import Data.Nat

        open Functor

        {- 
        We expect a free functor to be injective on morphisms, otherwise if
        it collides functions then it is enforcing equations and that's not
        what is expected of a “free construction”. That is, we want the 
        unit of the adjunction to be monic, at least. 
        Which is rather reasonable: We want the injection of our basis into
        a a free construction to not collide things, else we obtain new unfree
        equations.
        -}
        
        _⟪_ : ℕ → ℕ → ℕ
        x ⟪ y = x * y + 1
        -- (x ⟪ y) ⟪ z   ≡  x * y * z + z + 1
        -- x ⟪ (y  ⟪ z)  ≡  x * y * z + x + 1
        --
        -- Taking z , x ≔ 1 , 0 yields 2 ≡ 1
        --
        -- The following code realises this pseudo-argument correctly.

        ohno : ¬ (2 ≡.≡ 1)
        ohno ()
        
        𝒩 : Magma
        𝒩 = MkMagma ℕ _⟪_

        𝑵 : Semigroup
        𝑵 = Functor.F₀ FreeM 𝒩
        _⊕_ = Magma.Op (Functor.F₀ (ForgetM lzero) 𝑵 )

        inj : MagmaHom 𝒩 (Functor.F₀ (ForgetM lzero) 𝑵)
        inj = η unit 𝒩
        
        inj₀ = MagmaHom.mor inj

        -- the components of the unit are monic precisely when the left adjoint is faithful
        .work : {X Y : Magma} {F G : MagmaHom X Y}
             → morₘ (η unit Y) ∘ morₘ F ≐ morₘ (η unit Y) ∘ morₘ G
             → morₘ F ≐ morₘ G
        work {X} {Y} {F} {G} ηF≈ηG =
          let 𝑴₀   = Functor.F₀ FreeM
              𝑴    = Functor.F₁ FreeM
              _∘ₘ_  = Category._∘_ (MagmaCat lzero)
              εY    = mor (η counit (𝑴₀ Y))
              ηY    = η unit Y
          in faithfull F G (begin⟨ ≐-setoid (Carrier (𝑴₀ X)) (Carrier (𝑴₀ Y)) ⟩
          mor (𝑴 F)                     ≈⟨ ∘-≐-cong₁ (mor (𝑴 F)) zig ⟩
          (εY ∘ mor (𝑴 ηY)) ∘ mor (𝑴 F)   ≡⟨ ≡.refl ⟩
          εY ∘ (mor (𝑴 ηY)  ∘ mor (𝑴 F))   ≈⟨ ∘-≐-cong₂ εY (≐-sym (homomorphism FreeM)) ⟩
          εY ∘  mor (𝑴 (ηY ∘ₘ F))           ≈⟨ ∘-≐-cong₂ εY (F-resp-≡ FreeM ηF≈ηG) ⟩
          εY ∘ mor (𝑴 (ηY ∘ₘ G))            ≈⟨ ∘-≐-cong₂ εY (homomorphism FreeM) ⟩
          εY ∘ (mor (𝑴 ηY)   ∘ mor (𝑴 G))  ≡⟨ ≡.refl ⟩
          (εY ∘ mor (𝑴 ηY)) ∘ mor (𝑴 G)    ≈⟨ ∘-≐-cong₁ (mor (𝑴 G)) (≐-sym zig) ⟩                 
          mor (𝑴 G) ∎)
          where open import Relation.Binary.SetoidReasoning

        postulate inj-is-injective : {x y : ℕ} → inj₀ x ≡ inj₀ y → x ≡ y

        open import Data.Unit
        𝒯 : Magma
        𝒯 = MkMagma ⊤ (λ _ _ → tt)
        --
        -- ★ It may be that monics do not correspond to the underlying/mor function being injective for MagmaCat.
        -- ‼ .cminj-is-injective : {x y : ℕ} → {!!} -- inj₀ x ≡ inj₀ y → x ≡ y
        -- ‼ cminj-is-injective {x} {y} = work {𝒯} {𝒩} {F = MkHom (λ x → 0) (λ{ {tt} {tt} → {!!}})} {G = {!!}} {!!} 
        --
        -- ToDo! … perhaps this lives in the libraries someplace?
          
        bad : Hom (Functor.F₀ FreeM (Functor.F₀ (ForgetM _) 𝑵)) 𝑵
        bad = η counit 𝑵

        crash : inj₀ 2 ≡ inj₀ 1
        crash = let open ≡.≡-Reasoning {A = Carrier 𝑵} in begin
          inj₀ 2
            ≡⟨ ≡.refl ⟩
          inj₀ ( (0 ⟪ 666) ⟪ 1 )
            ≡⟨ MagmaHom.preservation inj ⟩
          inj₀ (0 ⟪ 666) ⊕ inj₀ 1
            ≡⟨ ≡.cong (_⊕ inj₀ 1) (MagmaHom.preservation inj) ⟩
          (inj₀ 0 ⊕ inj₀ 666) ⊕ inj₀ 1
            ≡⟨ ≡.sym (assoc 𝑵) ⟩
          inj₀ 0 ⊕ (inj₀ 666 ⊕ inj₀ 1)
            ≡⟨ ≡.cong (inj₀ 0 ⊕_) (≡.sym (MagmaHom.preservation inj)) ⟩
          inj₀ 0 ⊕ inj₀ (666 ⟪ 1)
            ≡⟨ ≡.sym (MagmaHom.preservation inj) ⟩
          inj₀ (0 ⟪ (666 ⟪ 1) )
            ≡⟨ ≡.refl ⟩
          inj₀ 1
            ∎

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
