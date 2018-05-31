\section{Monoids: Lists}

%{{{ Imports
\begin{code}
module Structures.Monoid where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.List using (List; _∷_ ; []; [_]; _++_; foldr; map)
open import Data.List.Properties

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (id ; _∘_ ; const)
open import Function2             using (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties

\end{code}
%}}}

%{{{ Some remarks about recursion principles
\subsection{Some remarks about recursion principles}
( To be relocated elsewhere )

\begin{spec}
open import Data.List

rcList : {X : Set} {Y : List X → Set} (g₁ : Y []) (g₂ : (x : X) (xs : List X) → Y xs → Y (x ∷ xs)) → (xs : List X) → Y xs
rcList g₁ g₂ [] = g₁
rcList g₁ g₂ (x ∷ xs) = g₂ x xs (rcList g₁ g₂ xs)

open import Data.Nat hiding (_*_)

rcℕ : {ℓ : Level} {X : ℕ → Set ℓ} (g₁ : X zero) (g₂ : (n : ℕ) → X n → X (suc n)) → (n : ℕ) → X n
rcℕ g₁ g₂ zero = g₁
rcℕ g₁ g₂ (suc n) = g₂ n (rcℕ g₁ g₂ n)
\end{spec}

Each constructor |c : Srcs → Type| becomes an argument |(ss : Srcs) → X ss → X (c ss)|, more or less :-)
to obtain a “recursion theorem” like principle.
The second piece |X ss| may not be possible due to type considerations.
Really, the induction principle is just the *dependent* version of folding/recursion!

Observe that if we instead use arguments of the form |{ss : Srcs} → X ss → X (c ss)| then, for one reason or
another, the dependent type |X| needs to be supplies explicity --yellow Agda! Hence, it behooves us to use explicits
in this case. Sometimes, the yellow cannot be avoided.
%}}}

%{{{ Monoid ; Hom
\subsection{Definition}
\begin{code}
record Monoid ℓ : Set (lsuc ℓ) where
  field
    Carrier   :   Set ℓ
    Id        :   Carrier
    _*_       :   Carrier → Carrier → Carrier
    leftId    :   {x : Carrier} → Id * x ≡ x
    rightId   :   {x : Carrier} → x * Id ≡ x
    assoc     :   {x y z : Carrier} → (x * y) * z ≡ x * (y * z)

open Monoid

record Hom {ℓ} (Src Tgt : Monoid ℓ) : Set ℓ where
  constructor MkHom
  open Monoid Src renaming (_*_ to _*₁_)
  open Monoid Tgt renaming (_*_ to _*₂_)
  field
    mor     :  Carrier Src → Carrier Tgt
    pres-Id : mor (Id Src) ≡ Id Tgt
    pres-Op : {x y : Carrier Src} → mor (x *₁ y)  ≡  mor x *₂ mor y

open Hom
\end{code}

%}}}

%{{{ MonoidAlg ; MonoidCat
\subsection{Category}
\begin{code}
MonoidAlg : {ℓ : Level} → OneSortedAlg ℓ
MonoidAlg {ℓ} = record
   { Alg         =   Monoid ℓ
   ; Carrier     =   Carrier
   ; Hom         =   Hom {ℓ}
   ; mor         =   mor
   ; comp        =   λ F G → record
     { mor       =   mor F ∘ mor G
     ; pres-Id   =   ≡.cong (mor F) (pres-Id G) ⟨≡≡⟩ pres-Id F
     ; pres-Op   =   ≡.cong (mor F) (pres-Op G) ⟨≡≡⟩ pres-Op F
     }
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl ≡.refl
   ; Id-is-id    =   ≐-refl
   }

MonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
MonoidCat ℓ = oneSortedCategory ℓ MonoidAlg
\end{code}
%}}}

%{{{ forgetful functor
\subsection{Forgetful Functor (to Sets)}
Forget all structure, and maintain only the underlying carrier

\begin{code}
Forget : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget ℓ = record
  { F₀             =   Carrier
  ; F₁             =   mor
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡       =   _$ᵢ
  }
  
-- Why do we have both?

Forget-alg : (ℓ : Level) → Functor (MonoidCat ℓ) (Sets ℓ)
Forget-alg ℓ = mkForgetful ℓ MonoidAlg
\end{code}
%}}}

%{{{ Useful kit
\begin{code}
ind : {ℓ ℓ′ : Level} {Y : Set ℓ} (P : List Y → Set ℓ′)
    → (P [])
    → ((y : Y) (ys : List Y) → P ys → P (y ∷ ys))
    → (ys : List Y) → P ys
ind _ n _ []         =   n
ind P n c (x ∷ xs)   =   c x xs (ind P n c xs)
\end{code}
}}}%

%{{{ Free functor; ListLeft
\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (MonoidCat ℓ)
Free ℓ = record
  { F₀ = λ a → record
    { Carrier = List a
    ; Id = []
    ; _*_ = _++_
    ; leftId = ≡.refl
    ; rightId = λ {x} → ++-identityʳ x
    ; assoc = λ {x y z} → ++-assoc x y z
    }
  ; F₁ = λ f → MkHom (map f) ≡.refl λ {xs} {ys} → map-++-commute f xs ys
  ; identity = map-id
  ; homomorphism = map-compose
  ; F-resp-≡ = λ F≐G → map-cong λ x → F≐G {x}
  }

ListLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
ListLeft ℓ = record
  { unit = record { η = λ _ x → [ x ]
                  ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ X →
    let fold = foldr (_*_ X) (Id X)
        _+_ = _*_ X
        e   = Id X in
    MkHom fold ≡.refl
          λ {x} {y} → ind (λ l → fold (l ++ y) ≡ fold l + fold y)
                          (≡.sym (leftId X))
                          (λ z zs eq → ≡.trans (≡.cong (z +_) eq) (≡.sym (assoc X))) x
                    ; commute = λ {X} {Y} f l →
   let foldX = foldr (_*_ X) (Id X)
       foldY = foldr (_*_ Y) (Id Y)
       _+_ = _*_ Y in
       ind (λ ll → foldY (map (mor f) ll) ≡ mor f (foldX ll))
           (≡.sym (pres-Id f))
           (λ z zs eq → ≡.trans (≡.cong ((mor f z) +_) eq) (≡.sym (pres-Op f)) ) l }
  ; zig = λ l → ind (λ ll → ll ≡ foldr _++_ [] (map [_] ll)) ≡.refl (λ y ys eq → ≡.cong (y ∷_) eq) l
  ; zag = λ {X} → ≡.sym (rightId X)
  }
\end{code}
%}}}

%{{{ Zero object

Singleton sets form both the initial and terminal monoid.

\begin{code}
open import Structures.OneCat hiding (initial ; terminal)
open import Categories.Object.Initial
open import Categories.Object.Terminal

{- In some sense this is a degenerate monoid since
we have the non-free equation: ∀ x. x ≈ ε.
-}
One-Monoid : {ℓ : Level} → Monoid ℓ
One-Monoid = record
   { Carrier   =   One
   ; Id        =   ⋆
   ; _*_       =   𝑲₂ ⋆
   ; leftId    =   λ { {⋆} → ≡.refl}
   ; rightId   =   λ { {⋆} → ≡.refl}
   ; assoc     =   ≡.refl
   }

initial : {ℓ : Level} → Initial (MonoidCat ℓ)
initial = record
  { ⊥        =  One-Monoid
  ; !         =  λ {X} → MkHom (λ _ → Id X) ≡.refl (≡.sym (leftId X))
  ; !-unique  =  λ f →  λ{ ⋆ → ≡.sym (pres-Id f) }
  }

terminal : {ℓ : Level} → Terminal (MonoidCat ℓ)
terminal = record
  { ⊤        =  One-Monoid
  ; !         =  λ {X} → MkHom (𝑲 ⋆) ≡.refl ≡.refl
  ; !-unique  =  λ _  _ → uip-One
  }

OneFreeMonoid : {ℓ : Level} → Monoid ℓ
OneFreeMonoid = record
    { Carrier = List One
    ; Id      = []
    ; _*_     = _++_
    ; leftId  = ≡.refl
    ; rightId = λ {x} → ++-identityʳ x
    ; assoc   = λ {x y z} → ++-assoc x y z
    }

OneCat₀ : (ℓ₁ ℓ₂ ℓ₃ : Level) → Category ℓ₁ ℓ₂ ℓ₃
OneCat₀ ℓ₁ ℓ₂ ℓ₃ = record
  { Obj        =  One {ℓ₁}
  ; _⇒_       =   𝑲₂ (One {ℓ₂})
  ; _≡_       =   𝑲₂ (One {ℓ₃})
  ; id         =  ⋆
  ; _∘_        =  𝑲₂ ⋆
  ; assoc      =  ⋆
  ; identityˡ  =  ⋆
  ; identityʳ  =  ⋆
  ; equiv     =  record
    { refl    =  ⋆
    ; sym     =  λ _ → ⋆
    ; trans   =  𝑲₂ ⋆
    }
  ; ∘-resp-≡ = 𝑲₂ ⋆
  }
--
-- By Axiom of Choice we have OneCat ≅ OneCat₀ --possibly without choice since all objects indistinguishable in the former.

Free₁ : (ℓ : Level) → Functor (OneCat₀ ℓ ℓ ℓ) (MonoidCat ℓ)
Free₁ ℓ = record
  { F₀           = 𝑲 OneFreeMonoid
  ; F₁           = λ{ {A} {B} ⋆ → MkHom id ≡.refl ≡.refl}
  ; identity     = λ _ → ≡.refl
  ; homomorphism = λ{ {⋆} {⋆} {⋆} {⋆} {⋆} _ → ≡.refl}
  ; F-resp-≡     = λ{ {⋆} {⋆} {⋆} {⋆} ⋆ → λ _ → ≡.refl }
  }
-- Had we used OneCat instead of OneCat₀, then F₁ would be λ{ {A} {B} ⋆ → MkHom f ⋯ }, where f : List A → List B, not possible.

-- It is clear that: OneFreeMonoid ≅ ℕ.
-- e.g.,
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Nat.Properties
ℕ-monoid : Monoid _
ℕ-monoid = record
   { Carrier   =   ℕ
   ; Id        =   0
   ; _*_       =   _+_
   ; leftId    =   λ {x} → +-identityˡ x
   ; rightId   =   λ {x} → +-identityʳ x
   ; assoc     =   λ {x} {y} {z} → +-assoc x y z
   }
-- Should be, but is not, in the standard library!
replicate-homo : {ℓ : Level} {A : Set ℓ} {a : A} ({n} m : ℕ)
               → replicate (m + n) a ≡ replicate m a ++ replicate n a
replicate-homo zero = ≡.refl
replicate-homo {a = a} (suc m) = ≡.cong (a ∷_) (replicate-homo m)
fromℕ : Hom ℕ-monoid OneFreeMonoid
fromℕ = MkHom (λ n → replicate n ⋆) ≡.refl (λ {m} → replicate-homo m)
toℕ : Hom OneFreeMonoid ℕ-monoid
toℕ = MkHom length ≡.refl (λ {x} → length-++ x)
import Level as Level
open import Categories.Morphisms (MonoidCat Level.zero)
from-to : (x : List (One {Level.zero})) → replicate (length x) ⋆ ≡ x
from-to [] = ≡.refl
from-to (⋆ ∷ x) = ≡.cong (⋆ ∷_) (from-to x)
OneFreeMonoid≅ℕ : OneFreeMonoid ≅ ℕ-monoid
OneFreeMonoid≅ℕ = record
  { f = toℕ
  ; g = fromℕ
  ; iso = record
     { isoˡ = from-to
     ; isoʳ = λ x → length-replicate x {⋆}
     }
  }
Forget₁ : (ℓ : Level) → Functor (MonoidCat ℓ) (OneCat₀ ℓ ℓ ℓ)
Forget₁ _ = record
  { F₀             =  λ _ → ⋆
  ; F₁             =  𝑲 ⋆
  ; identity       =  ⋆
  ; homomorphism   =  ⋆
  ; F-resp-≡      =   𝑲 ⋆
  }
FreedomSad : {ℓ : Level} → Adjunction (Free₁ ℓ) (Forget₁ ℓ)
FreedomSad = record
  { unit     =   record { η = id ; commute = id }
  ; counit   =   record { η = λ X → MkHom (𝑲 (Id X)) ≡.refl (≡.sym (leftId X))
                        ; commute = λ f x → ≡.sym (pres-Id f) }
  ; zig      =   {!It is here that we are forced to have the equation: ∀ x. x ≈ ε!}
  ; zag      =   ⋆
  }
\end{code}
%}}}

%{{{ 0-Ary version
\begin{code}
module ZeroAryAdjoint where

  Forget-0 : (ℓ : Level) → Functor (MonoidCat ℓ) (OneCat ℓ ℓ ℓ)
  Forget-0 ℓ = MakeForgetfulFunctor Carrier

  -- OneCat can be, itself, viewed as a Monoid
  Free-0 : (ℓ : Level) → Functor (OneCat ℓ ℓ ℓ) (MonoidCat ℓ)
  Free-0 ℓ = MakeFreeFunctor One-Monoid

  Left : {ℓ : Level} → Adjunction (Free-0 ℓ) (Forget-0 ℓ)
  Left = Make-Free⊢Forget Carrier initial

  Right : {ℓ : Level} → Adjunction (Forget-0 ℓ) (Free-0 ℓ)
  Right = Make-Forget⊢CoFree Carrier terminal
\end{code}
%}}}

-- ToDo ∷ forget to the underlying semigroup

-- ToDo ∷ forget to the underlying pointed

-- ToDo ∷ forget to the underlying magma

-- ToDo ∷ forget to the underlying binary relation, with |x ∼ y ∶≡ (∀ z → x * z ≡ y * z)|
          -- the monoid-indistuighability equivalence relation


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
