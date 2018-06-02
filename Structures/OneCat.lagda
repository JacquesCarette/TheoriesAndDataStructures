\section{|OneCat|: Constant Functions}

Working out the details of an adjunction between sets and
a one-object one-arrow category yields us with the notion
of \emph{constant functions}: Those operations that completely
ignore their input and always yield the same output.

(
  That is, when proving the adjunction, the pattern of constant
  functions --i.e., ignoring arguments in-preference of pre-determined
  or only possible output-- keeps occuring.
)

...Examples of such operations in the wild (i.e., ``real programming'')?...

%{{{ Imports
\begin{code}
module Structures.OneCat where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category     using   (Category)
open import Categories.Functor      using   (Functor)
open import Categories.Adjunction   using   (Adjunction)
open import Categories.Agda         using   (Sets)
open import Function                using   (id ; _∘_ ; const)
open import Helpers.Function2       using   (_$ᵢ)

open import Relation.Nullary  -- for showing some impossibility

open import Helpers.Forget
open import Helpers.EqualityCombinators
open import Helpers.DataProperties

-- 𝑲onstant
𝑲 : {a b : Level} {A : Set a} {B : Set b} → A → B → A
𝑲 a _ = a

-- It will be seen that |𝑲₂ ⋆| forms a monoidal operation on |One|.
𝑲₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A → B → C → A
𝑲₂ a _ _ = a
\end{code}
%}}}

%{{{ |OneCat|
\begin{code}
-- The “formal” object and morphism names coincide; for brevity.
data One {ℓ : Level} : Set ℓ where
  ⋆ : One

-- The One-object One-arrow Category
OneCat : (ℓ₁ ℓ₂ ℓ₃ : Level) → Category (lsuc ℓ₁) ℓ₂ ℓ₃
OneCat ℓ₁ ℓ₂ ℓ₃ = record
  { Obj        =  Set ℓ₁
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
\end{code}
%}}}

%{{{ Δ⊢Id

Arrows in the one-object one-arrow category correspond to the functions
to a singleton set.
( Both the former and latter collection of arrows have cardinality 1. )

\begin{code}

-- Given a way to realise an object as a set, we forget any additional structure
-- the object may have to obtain a functor to OneCat.
MakeForgetfulFunctor : {a b c d e f : Level} {C : Category a b c}
                     → (obj : Category.Obj C → Set d)
                     → Functor C (OneCat d e f)
MakeForgetfulFunctor obj = record
  { F₀             =  obj
  ; F₁             =  𝑲 ⋆
  ; identity       =  ⋆
  ; homomorphism   =  ⋆
  ; F-resp-≡      =   𝑲 ⋆
  }                     

Forget : {ℓ₁ ℓ₂ ℓ₃ : Level} → Functor (Sets ℓ₁) (OneCat ℓ₁ ℓ₂ ℓ₃)
Forget {ℓ} = MakeForgetfulFunctor id

-- The constant functor.
𝒦 : {a b c d e f : Level} {C : Category a b c} {D : Category d e f}
  → (X : Category.Obj D) → Functor C D
𝒦 {D = D} X = let module D = Category D in record
   { F₀             =   λ _ → X
   ; F₁             =   𝑲 D.id
   ; identity       =   D.Equiv.refl
   ; homomorphism   =   D.Equiv.sym D.identityˡ
   ; F-resp-≡       =   𝑲 D.Equiv.refl
   }

-- Given an elected object in any target category, we obtain a functor.
-- That is: Objects in any category correspond to functors to that category from OneCat xD
MakeFreeFunctor : {a b c d e f : Level} {C : Category a b c}
      → (uno : Category.Obj C) → Functor (OneCat d e f) C
MakeFreeFunctor = 𝒦
 -- MA: Notice how the constant functor arises naturally when considering functors out of OneCat :-)

Free : {ℓ : Level} → Functor (OneCat ℓ ℓ ℓ) (Sets ℓ)
Free {ℓ} = MakeFreeFunctor (One {ℓ})

{-
In the case C = Set:

The problem here is with F₀.

If we set `F₀ = id`, realising the only set of OneCat as an object of Set,
then we are faced with `F₁`: We must produce a function `A → B` given
the only arrow of OneCat, ⋆. However, we cannot produce arbitrary functions
and so we are forced to define `F₀ = 𝑲 One`.
-}

--
-- There is no left adjoint because you can't create objects of an arbitrary
-- type out of nothing.  This is most glaring when there are indeed none.

NoLeftAdjoint : {ℓ : Level} → ¬ Adjunction (Free {ℓ}) (Forget {ℓ})
NoLeftAdjoint {ℓ} adj = ⊥-elim (η counit ⊥ ⋆)
  where open Adjunction adj
        open import Categories.NaturalTransformation hiding (id ; _≡_)
        open NaturalTransformation

-- Since ⊥ is not a pointed set, this argument does not carry over to
-- the category of pointed sets for which such an adjunction does exist.

-- If a (concrete) category C were to have a terminal object then
-- there would be an (co)adjunction!

open import Categories.Object.Terminal
module _ {a b c d e f : Level} {C : Category a b c}
    (obj : Category.Obj C → Set d) (Uno : Terminal C)
    where    

  private

    open Terminal Uno renaming (⊤ to oneish)
    
    R : Functor C (OneCat d e f)
    R = MakeForgetfulFunctor obj

    L : Functor (OneCat d e f) C
    L = MakeFreeFunctor oneish

  Make-Forget⊢CoFree : Adjunction R L
  Make-Forget⊢CoFree = let module C = Category C in record
    { unit        =   record { η = λ X → ! {X} ; commute = λ f → !-unique₂ _ _ }
    ; counit      =   record { η = 𝑲 ⋆ ; commute = 𝑲 ⋆ }
    ; zig         =   ⋆
    ; zag         =   C.Equiv.sym (C.Equiv.trans C.identityˡ (⊤-id !))
    }

uip-One : {ℓ : Level} {x : One {ℓ}} → ⋆ ≡ x
uip-One {_} {⋆} = ≡.refl

terminal : {ℓ : Level} → Terminal (Sets ℓ)
terminal = record
  { ⊤         =   One
  ; !         =   𝑲 ⋆
  ; !-unique  =   λ _ → uip-One
  }  

RightAdjoint : {ℓ : Level} → Adjunction {D = Sets ℓ} Forget Free
RightAdjoint = Make-Forget⊢CoFree id terminal

-- If a (concrete) category C were to have an initial object then
-- there would be an adjunction!

-- open import Categories.Functor hiding (equiv; assoc; identityˡ; identityʳ; ∘-resp-≡) renaming (id to idF; _≡_ to _≡F_; _∘_ to _∘F_)
-- open import Categories.NaturalTransformation hiding (equiv; setoid) renaming (id to idT; _≡_ to _≡T_)

open import Categories.Object.Initial
module _ {a b c d e f : Level} {C : Category a b c}
    (obj : Category.Obj C → Set d) (Uno : Initial C)
    -- (uno : Category.Obj C)
    -- (uno-initial : NaturalTransformation (𝒦 {C = C} {D = C} uno) idF)
    where    

  private

    open Initial Uno renaming (⊥ to oneish)

    R : Functor C (OneCat d e f)
    R = MakeForgetfulFunctor obj

    L : Functor (OneCat d e f) C
    L = MakeFreeFunctor oneish

  Make-Free⊢Forget : Adjunction L R
  Make-Free⊢Forget = let module C = Category C in record
    { unit        =   record { η = 𝑲 ⋆ ; commute = 𝑲 ⋆ }
    ; counit      =   record
      { η         =   λ X → ! {X}
      ; commute   =   λ f → !-unique₂ _ _
      }
    ; zig         =   C.Equiv.sym (C.Equiv.trans C.identityʳ (⊥-id !))
    ; zag         =   ⋆
    }

initial : {ℓ : Level} → Initial (Sets ℓ)
initial = record
  { ⊥         =   ⊥
  ; !         =   λ{ () }
  ; !-unique  =   λ{ _ {()} }
  }

YesLeftAdjoint : {ℓ : Level} → Adjunction {D = OneCat ℓ ℓ ℓ} (MakeFreeFunctor ⊥) Forget
YesLeftAdjoint = Make-Free⊢Forget id initial

-- MA: Adjoints are unique and so we have, MakeFreeFunctor ⊥  ≅  Free
-- What does this tell us?

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
