%% In this file, only CommMonoid up to CMonoidCat & Forget are defined.
%% The ``free commutative
\section{Structures.CommMonoid}

%{{{ Imports
\begin{code}
module Structures.CommMonoid where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; _Preserves₂_⟶_⟶_; IsEquivalence)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)

open import Relation.Binary.Sum
import Algebra.FunctionProperties as AFP
open AFP using (Op₂)

-- open import Forget
-- open import EqualityCombinators
-- open import DataProperties hiding (_,_; ⟨_,_⟩)
-- open import SetoidEquiv
-- open import ParComp
-- open import Belongs
\end{code}
%}}}

%{{{ CommMonoid ; Hom
\subsection{Definitions}

Some of this is borrowed from the standard library's |Algebra.Structures|
and |Algebra|.  But un-nested and made direct.

\begin{code}
record IsCommutativeMonoid {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
                           (_∙_ : Op₂ A) (ε : A) : Set (a ⊍ ℓ) where
  open AFP _≈_
  field
    left-unit   : LeftIdentity ε _∙_
    right-unit  : RightIdentity ε _∙_
    assoc       : Associative _∙_
    comm        : Commutative _∙_
    _⟨∙⟩_        : Congruent₂ _∙_

record CommMonoid {ℓ} {o} : Set (lsuc ℓ ⊍ lsuc o) where
  constructor MkCommMon
  field setoid : Setoid ℓ o
  open Setoid setoid public

  field
    e            : Carrier
    _*_          : Carrier → Carrier → Carrier
    isCommMonoid : IsCommutativeMonoid _≈_ _*_ e
  module ≈ = Setoid setoid
  _⟨≈⟩_ = trans

infix -666 eq-in
eq-in = CommMonoid._≈_
syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

record Hom {ℓ} {o} (A B : CommMonoid {ℓ} {o}) : Set (ℓ ⊍ o) where
  constructor MkHom
  open CommMonoid using (setoid; Carrier)
  open CommMonoid A using () renaming (e to e₁; _*_ to _*₁_; _≈_ to _≈₁_)
  open CommMonoid B using () renaming (e to e₂; _*_ to _*₂_; _≈_ to _≈₂_)

  field mor    : setoid A ⟶ setoid B
  private mor₀ = Π._⟨$⟩_ mor
  field
    pres-e : mor₀ e₁ ≈₂ e₂
    pres-* : {x y : Carrier A} → mor₀ (x *₁ y)  ≈₂  mor₀ x *₂ mor₀ y

  open Π mor public
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.

%}}}

%{{{ MonoidCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (o ⊍ ℓ)
MonoidCat ℓ o = record
  { Obj = CommMonoid {ℓ} {o}
  ; _⇒_ = Hom
  ; _≡_ = λ {A} {B} F G → ∀ {x} → F ⟨$⟩ x ≈ G ⟨$⟩ x ∶ B
  ; id  = λ {A} → let open CommMonoid A in MkHom id refl refl
  ; _∘_ = λ { {C = C} F G → let open CommMonoid C in record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  (cong F (pres-e G)) ⟨≈⟩ (pres-e F)
    ; pres-*   =  (cong F (pres-* G)) ⟨≈⟩ (pres-* F)
    } }
  ; assoc     = λ { {D = D} → CommMonoid.refl D}
  ; identityˡ = λ {_} {B} → CommMonoid.refl B
  ; identityʳ = λ {_} {B} → CommMonoid.refl B
  ; equiv     = λ {_} {B} → record
    { refl  = CommMonoid.refl B
    ; sym   = λ F≈G → CommMonoid.sym B F≈G
    ; trans = λ F≈G G≈H → CommMonoid.trans B F≈G G≈H
    }
  ; ∘-resp-≡ = λ { {C = C} {f = F} F≈F' G≈G' → CommMonoid.trans C (cong F G≈G') F≈F' }
  }
  where open Hom
\end{code}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ o) (Setoids ℓ o)
Forget ℓ o = record
  { F₀             =   λ C → record { CommMonoid C }
  ; F₁             =   λ F → record { Hom F }
  ; identity       =   λ {A} → ≈.refl A
  ; homomorphism   =   λ {A} {B} {C} → ≈.refl C
  ; F-resp-≡      =   λ F≈G {x} → F≈G {x}
  }
  where open CommMonoid using (module ≈)
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
