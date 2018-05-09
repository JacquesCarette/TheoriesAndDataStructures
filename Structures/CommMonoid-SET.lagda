%% In this file, only CommMonoid up to CMonoidCat & Forget are defined.
%% The ``free commutative
\section{Structures.CommMonoid-SET}

A SET based variant of |Structure.CommMonoid|.

%{{{ Imports
\begin{code}
module Structures.CommMonoid-SET where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)

open import Data.Product      using (Σ; proj₁; proj₂; _,_)
open import Function using (id ; _∘_)

open import Relation.Binary.Sum
import Algebra.FunctionProperties as AFP
open AFP using (Op₂)
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\subsection{Definitions}

Some of this is borrowed from the standard library's |Algebra.Structures|
and |Algebra|.  But un-nested and made direct.

Splitting off the properties is useful when defining structures which
are commutative-monoid-like, but differ in other ways.  The core
properties can be re-used.
\begin{code}
open import EqualityCombinators

record IsCommutativeMonoid {ℓ} {A : Set ℓ} (_∙_ : Op₂ A) (ε : A) : Set ℓ where
  
  open AFP (_≡_ {ℓ} {A = A})
  field
    left-unit   : LeftIdentity ε _∙_
    right-unit  : RightIdentity ε _∙_
    assoc       : Associative _∙_
    comm        : Commutative _∙_
\end{code}

There are many equivalent ways of defining a |CommMonoid|.  But it
boils down to this: Agda's dependent records are \textbf{telescopes}.
Sometimes, one wants to identify a particular initial sub-telescope
that should be shared between two instances.  This is hard (impossible?)
to do with holistic records.  But if split, via |Σ|, this becomes
easy.

For our purposes, it is very convenient to split the |Setoid|
part of the definition.

\begin{code}
record CommMonoid {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  constructor MkCommMon
  field
    e            : X
    _*_          : X → X → X  -- \edcomm{MA}{Why is this `e` but above is `·`?}
    -- \edcomm{MA}{The field name really oughtn't be abbreviated!}
    isCommMonoid : IsCommutativeMonoid _*_ e

  open IsCommutativeMonoid isCommMonoid public

  _⟨≡⟩_ = ≡.trans

  infix -666 eq-in
  eq-in = ≡._≡_
  syntax eq-in M x y  =  x ≡ y ∶ M   -- ghost colon

record Hom {ℓ : Level} {X Y : Set ℓ} (CMX : CommMonoid X) (CMY : CommMonoid Y) : Set ℓ where
  constructor MkHom
  open CommMonoid  CMX  using () renaming (e to e₁; _*_ to _*₁_      )
  open CommMonoid  CMY  using () renaming (e to e₂; _*_ to _*₂_      )

  field mor    : X → Y
  field
    pres-e : mor e₁ ≡ e₂
    pres-* : {x y : X} → mor (x *₁ y)  ≡  mor x *₂ mor y

  cong : {a b : X} → a ≡ b → mor a ≡ mor b
  cong = ≡.cong mor

open Hom using (mor)
open Hom renaming (mor to _⟨$⟩_)
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.
%}}}

%{{{ CommMonoidCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
CommMonoidCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
CommMonoidCat ℓ = let open CommMonoid using (eq-in) in record
  { Obj = Σ (Set ℓ) CommMonoid
  ; _⇒_ = λ{ (X , CMX) (Y , CMY) → Hom CMX CMY}
  ; _≡_ = λ { {X , CMX} {Y , CMY} F G → ∀ {x : X} → F ⟨$⟩ x ≡ G ⟨$⟩ x }
  ; id  = λ { {A , _} → MkHom id ≡.refl ≡.refl }
  ; _∘_ = λ { {C = _ , C} F G → let open CommMonoid C in record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  cong F (pres-e G) ⟨≡≡⟩ pres-e F
    ; pres-*   =  cong F (pres-* G) ⟨≡≡⟩ pres-* F
    } }
  ; assoc     = ≡.refl
  ; identityˡ =  ≡.refl
  ; identityʳ = ≡.refl
  ; equiv     = λ { {_} {B , _} → record
    { refl  = ≡.refl
    ; sym   = λ F≈G → ≡.sym F≈G
    ; trans = λ F≈G G≈H → F≈G ⟨≡≡⟩ G≈H }
    }
  ; ∘-resp-≡ = λ { {C = C , _} {f = F} F≈F' G≈G' → cong F G≈G' ⟨≡≡⟩ F≈F' }
  }
  where open Hom
\end{code}

\begin{code}
open import Categories.Agda using (Sets)

Forget : (ℓ o : Level) → Functor (CommMonoidCat ℓ) (Sets ℓ)
Forget ℓ o = record
  { F₀             =   λ{ (X , CMX) → X }
  ; F₁             =   λ F → mor F
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   id
  }
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
