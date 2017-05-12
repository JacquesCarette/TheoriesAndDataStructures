%{{{ Imports
\begin{code}
module Structures.InvolutiveAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category   using (Category; module Category)
open import Categories.Functor    using (Functor; Contravariant)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Categories.Monad      using (Monad)
open import Categories.Comonad    using (Comonad)

open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])          renaming (map to map⊎)
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; swap) renaming (map to map× ; <_,_> to ⟨_,_⟩)
open import Function     using (const ; flip)                    renaming (id to idF; _∘_ to _◎_)
open import Function2    using (_$ᵢ)
open import Equiv        using (_∼_; refl∼; sym∼; trans∼; ∘-resp-∼ ; isEquivalence∼)


-- MA: avoid renaming by using this handy-dandy trick. Now write |≡.refl| and |≡.trans| ;)
import Relation.Binary.PropositionalEquality
private module ≡ = Relation.Binary.PropositionalEquality
open ≡ using (_≡_)
\end{code}
%}}}

%{{{ Inv and Hom

\begin{code}
record Inv {ℓ} : Set (lsuc ℓ) where
  field
    A : Set ℓ
    _ᵒ : A → A
    involutive : ∀ (a : A) → a ᵒ ᵒ ≡ a

open Inv renaming (A to Carrier ; _ᵒ to inv)

record Hom {ℓ} (X Y : Inv {ℓ}) : Set ℓ where
  open Inv X ; open Inv Y renaming (_ᵒ to _ᴼ)
  field
    f       :  Carrier X → Carrier Y
    pres-ᵒ  :  ∀ x → f (x ᵒ) ≡ (f x) ᴼ

open Hom renaming (f to mor)
\end{code}
%}}}

%{{{ InvCat and foregtful functor U

\begin{code}
InvCat : ∀ {ℓ} → Category _ ℓ ℓ
InvCat = record
   { Obj = Inv
   ; _⇒_ = Hom
   ; _≡_ = λ h₁ h₂ → f h₁ ∼ f h₂
   ; id = record { f = idF ; pres-ᵒ = refl∼ }
   ; _∘_ = λ B⇒C A⇒B → record
     { f = f B⇒C ◎ f A⇒B
     ; pres-ᵒ = λ a → ≡.trans (≡.cong (f B⇒C) (pres-ᵒ A⇒B a)) (pres-ᵒ B⇒C (f A⇒B a)) }
   ; assoc = refl∼
   ; identityˡ = refl∼
   ; identityʳ = refl∼
   ; equiv = record { IsEquivalence isEquivalence∼ }
   ; ∘-resp-≡ = ∘-resp-∼
   }
   where open Hom ; open import Relation.Binary using (IsEquivalence)

U : (o : Level) → Functor (InvCat {o}) (Sets o)
U  _ = record
  { F₀            =   Carrier
  ; F₁            =   mor
  ; identity      =   ≡.refl
  ; homomorphism  =   ≡.refl
  ; F-resp-≡     =   _$ᵢ
  }
\end{code}
%}}}

%{{{ |swap₊| and |from⊎|

The double of a type has an involution on it by swapping the tags:

\begin{code}
swap₊ : {ℓ : Level} {A : Set ℓ} → A ⊎ A → A ⊎ A
swap₊ = [ inj₂ , inj₁ ]

from⊎ : ∀ {ℓ} {A : Set ℓ} → A ⊎ A → A
from⊎ = [ idF , idF ]
\end{code}
%}}}

%{{{ Left and AdjLeft

\begin{code}
Left : ∀ o → Functor (Sets o) (InvCat {o})
Left o = record
  { F₀ = λ A → record { A = A ⊎ A ; _ᵒ = swap₊ ; involutive = [ refl∼ , refl∼ ] }
  ; F₁ = λ f → record { f = map⊎ f f ; pres-ᵒ = [ refl∼ , refl∼ ] }
  ; identity = [ refl∼ , refl∼ ]
  ; homomorphism = [ refl∼ , refl∼ ]
  ; F-resp-≡ = λ F∼G → [ (λ _ → ≡.cong inj₁ F∼G) , (λ _ → ≡.cong inj₂ F∼G) ] -- there has to be a better way!
  }
\end{code}

There are actually two left adjoints.  It seems the choice of inj₁ / inj₂ is free.
But that choice does force the order of 'idF _ᵒ' in map⊎ (else zag does not hold).

\begin{code}
AdjLeft : ∀ o → Adjunction (Left o) (U o)
AdjLeft o = record
  { unit   = record { η = λ _ → inj₁ ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ A  → record
          { f      =  [ idF , inv A ]                        -- |≡  from⊎ ◎ map⊎ idF _ᵒ|
          ; pres-ᵒ  =  [ refl∼ , ≡.sym ◎ involutive A ]
          }
    ; commute = λ F → [ refl∼ , ≡.sym ◎ Hom.pres-ᵒ F ]
    }
  ; zig = [ refl∼ , refl∼ ]
  ; zag = ≡.refl
  }

-- but there's another!
AdjLeft₂ : ∀ o → Adjunction (Left o) (U o)
AdjLeft₂ o = record
  { unit = record { η = λ _ → inj₂ ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ A → record
          { f     = [ inv A , idF ]                          -- |≡  from⊎ ◎ map⊎ _ᵒ idF |
          ; pres-ᵒ = [ ≡.sym ◎ involutive A , refl∼ ]
          }
    ; commute = λ F → [ ≡.sym ◎ Hom.pres-ᵒ F , refl∼ ]
    }
  ; zig = [ refl∼ , refl∼ ]
  ; zag = ≡.refl
  }
\end{code}
%}}}

%{{{ Right, diag, AdjRight

\begin{code}
-- for the proofs below, we "cheat" and let η for records make things easy.
Right : ∀ o → Functor (Sets o) (InvCat {o})
Right o = record
  { F₀ = λ B → record { A = B × B ; _ᵒ = swap ; involutive = refl∼ }
  ; F₁ = λ g → record { f = map× g g ; pres-ᵒ = refl∼ }
  ; identity      =  refl∼
  ; homomorphism  =  refl∼
  ; F-resp-≡     =  λ F≡G a → ≡.cong₂ _,_ (F≡G {proj₁ a}) F≡G
  }

diag : ∀ {ℓ} {A : Set ℓ} (a : A) → A × A
diag a = a , a

AdjRight : ∀ o → Adjunction (U o) (Right o)
AdjRight o = record
  { unit = record
    { η = λ A → record
      { f      =  ⟨ idF , inv A ⟩
      ; pres-ᵒ  =  ≡.cong₂ _,_ ≡.refl ◎ involutive A
      }
    ; commute = λ f → ≡.cong₂ _,_ ≡.refl ◎ ≡.sym ◎ Hom.pres-ᵒ f
    }
  ; counit   =   record { η = λ _ → proj₁ ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   refl∼
  }

-- MA: and here's another ;)
AdjRight₂ : ∀ o → Adjunction (U o) (Right o)
AdjRight₂ o = record
  { unit = record
    { η = λ A → record
      { f      =  ⟨ inv A , idF ⟩
      ; pres-ᵒ  =  flip (≡.cong₂ _,_) ≡.refl ◎ involutive A
      }
    ; commute = λ f → flip (≡.cong₂ _,_) ≡.refl ◎ ≡.sym ◎ Hom.pres-ᵒ f
    }
  ; counit   =   record { η = λ _ → proj₂ ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   refl∼
  }
\end{code}

Note that we have TWO proofs for AdjRight since we can construe |A×A| as
|{ (a , aᵒ) ∣ a ∈ A}| or as |{(aᵒ , a) ∣ a ∈ A}| ---similarly for why
we have two AdjLeft proofs.

%}}}

%{{{ Monad constructions

\begin{code}
SetMonad : ∀ {o} → Monad (Sets o)
SetMonad {o} = Adjunction.monad (AdjLeft o)

InvComonad : ∀ {o} → Comonad (InvCat {o})
InvComonad {o} = Adjunction.comonad (AdjLeft o)
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
