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
  { F₀ = Carrier
  ; F₁ = mor
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≡ = _$ᵢ
  }

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

%{{{ 0-Ary version
\begin{code}
module ZeroAryAdjoint where

  open import Structures.OneCat

  Forget-0 : (ℓ : Level) → Functor (MonoidCat ℓ) (OneCat ℓ ℓ ℓ)
  Forget-0 ℓ = record
    { F₀ = Carrier
    ; F₁ = λ _ → ⋆
    ; identity = ⋆
    ; homomorphism = ⋆
    ; F-resp-≡ = λ _ → ⋆
    }

  -- OneCat can be, itself, viewed as a Monoid
  Free-0 : (ℓ : Level) → Functor (OneCat ℓ ℓ ℓ) (MonoidCat ℓ)
  Free-0 ℓ = record
     { F₀             =  λ _ → record
                                 { Carrier = One
                                 ; Id = ⋆
                                 ; _*_ = 𝑲₂ ⋆
                                 ; leftId = λ { {⋆} → ≡.refl}
                                 ; rightId = λ { {⋆} → ≡.refl}
                                 ; assoc = ≡.refl
                                 }
     ; F₁             =  λ _ → MkHom id ≡.refl ≡.refl
     ; identity       =  λ _ → ≡.refl
     ; homomorphism   =  λ _ → ≡.refl
     ; F-resp-≡      =   λ _ _ → ≡.refl
     }

  Left : (ℓ : Level) → Adjunction (Free-0 ℓ) (Forget-0 ℓ)
  Left ℓ = record
    { unit        =   record { η = λ _ → ⋆ ; commute = id }
    ; counit      =   record
      { η         =   λ X → MkHom (λ _ → Id X) ≡.refl (≡.sym (leftId X {Id X}))
      ; commute   =    λ f x → ≡.sym (pres-Id f)
      }
    ; zig         =    λ { ⋆ → ≡.refl}
    ; zag         =    ⋆
    }
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
