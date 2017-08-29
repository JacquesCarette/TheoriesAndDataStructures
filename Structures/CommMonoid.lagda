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

open import Data.Product      using (Σ; proj₁; proj₂; _,_)
open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)

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
record IsCommutativeMonoid {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
                           (_∙_ : Op₂ A) (ε : A) : Set (a ⊍ ℓ) where
  open AFP _≈_
  field
    left-unit   : LeftIdentity ε _∙_
    right-unit  : RightIdentity ε _∙_
    assoc       : Associative _∙_
    comm        : Commutative _∙_
    _⟨∙⟩_        : Congruent₂ _∙_
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
record CommMonoid {ℓ} {o} (X : Setoid ℓ o) : Set (lsuc ℓ ⊍ lsuc o) where
  constructor MkCommMon
  open Setoid X renaming (Carrier to X₀)

  field
    e            : X₀
    _*_          : X₀ → X₀ → X₀
    isCommMonoid : IsCommutativeMonoid _≈_ _*_ e
  module ≈ = Setoid X
  _⟨≈⟩_ = trans

  infix -666 eq-in
  eq-in = ≈._≈_
  syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

-- Alternative presentation where the setoid is a part of the packaging
record CommutativeMonoid (ℓ c : Level) : Set (lsuc ℓ ⊍ lsuc c) where
  constructor MkCommMon
  field
    setoid : Setoid ℓ c

  open Setoid setoid renaming (Carrier to X₀)

  field    
    e            : X₀
    _*_          : X₀ → X₀ → X₀
    isCommMonoid : IsCommutativeMonoid _≈_ _*_ e

  infix -666 eq-in
  eq-in = Setoid._≈_ setoid
  syntax eq-in M x y  =  x ≈ y ∶ M   -- ghost colon

asCommutativeMonoid : {ℓ c : Level} {X : Setoid ℓ c} → CommMonoid X → CommutativeMonoid ℓ c
asCommutativeMonoid {X = X} comm = let open CommMonoid comm in MkCommMon X e _*_ isCommMonoid

record Hom {ℓ} {o} (A B : Σ (Setoid ℓ o) CommMonoid) : Set (ℓ ⊍ o) where
  constructor MkHom
  open Setoid (proj₁ A) using () renaming (_≈_ to _≈₁_; Carrier to A₀)
  open Setoid (proj₁ B) using () renaming (_≈_ to _≈₂_)
  open CommMonoid (proj₂ A) using () renaming (e to e₁; _*_ to _*₁_)
  open CommMonoid (proj₂ B) using () renaming (e to e₂; _*_ to _*₂_)

  field mor    : proj₁ A ⟶ proj₁ B
  private mor₀ = Π._⟨$⟩_ mor
  field
    pres-e : mor₀ e₁ ≈₂ e₂
    pres-* : {x y : A₀} → mor₀ (x *₁ y)  ≈₂  mor₀ x *₂ mor₀ y

  open Π mor public
\end{code}

Notice that the last line in the record, |open Π mor public|, lifts the setoid-homomorphism
operation |_⟨$⟩_| and |cong| to work on our monoid homomorphisms directly.
%}}}

%{{{ CommutativeMonoidArrows

\begin{code}
record CMArrow {ℓ c ℓ' c' : Level} (Src : CommutativeMonoid ℓ c) (Tgt : CommutativeMonoid ℓ' c')
  : Set (ℓ ⊍ c ⊍ c' ⊍ ℓ') where

  _₀ : {ll cc : Level} → CommutativeMonoid ll cc → Set ll
  _₀ CM = Setoid.Carrier (CommutativeMonoid.setoid CM)

  open CommutativeMonoid Src using (eq-in) renaming (e to eₛ ; _*_ to _*ₛ_)
  open CommutativeMonoid Tgt using () renaming (e to eₜ ; _*_ to _*ₜ_)
  open CommutativeMonoid
  open Setoid (setoid Tgt) using (_≈_)

  field
    mor : setoid Src ⟶ setoid Tgt

  open Π
  field
    identity  :  mor ⟨$⟩ eₛ ≈ eₜ
    homo      :  {x y : Src ₀} → mor ⟨$⟩ (x *ₛ y) ≈ (mor ⟨$⟩ x) *ₜ (mor ⟨$⟩ y)
\end{code}
%}}}

%{{{ MonoidCat ; Forget
\subsection{Category and Forgetful Functor}
\begin{code}
MonoidCat : (ℓ o : Level) → Category (lsuc ℓ ⊍ lsuc o) (o ⊍ ℓ) (o ⊍ ℓ)
MonoidCat ℓ o = let open CommMonoid using (eq-in) in record
  { Obj = Σ (Setoid ℓ o) CommMonoid
  ; _⇒_ = Hom
  ; _≡_ = λ { {_} {_ , B} F G → ∀ {x} → F ⟨$⟩ x ≈ G ⟨$⟩ x ∶ B }
  ; id  = λ { {A , _} → MkHom id (refl A) (refl A) }
  ; _∘_ = λ { {C = _ , C} F G → let open CommMonoid C in record
    { mor      =  mor F ∘ mor G
    ; pres-e   =  (cong F (pres-e G)) ⟨≈⟩ (pres-e F)
    ; pres-*   =  (cong F (pres-* G)) ⟨≈⟩ (pres-* F)
    } }
  ; assoc     = λ { {D = D , _} → refl D}
  ; identityˡ = λ { {_} {B , _} → refl B }
  ; identityʳ = λ { {_} {B , _} → refl B }
  ; equiv     = λ { {_} {B , _} → record
    { refl  = refl B
    ; sym   = λ F≈G → sym B F≈G
    ; trans = λ F≈G G≈H → trans B F≈G G≈H }
    }
  ; ∘-resp-≡ = λ { {C = C , _} {f = F} F≈F' G≈G' → trans C (cong F G≈G') F≈F' }
  }
  where open Hom; open Setoid
\end{code}

\begin{code}
Forget : (ℓ o : Level) → Functor (MonoidCat ℓ o) (Setoids ℓ o)
Forget ℓ o = record
  { F₀             =   λ C → record { Setoid (proj₁ C) }
  ; F₁             =   λ F → record { Hom F }
  ; identity       =   λ {A} → ≈.refl (proj₂ A)
  ; homomorphism   =   λ {_} {_} {C} → ≈.refl (proj₂ C)
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
