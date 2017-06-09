‼ This module is not being called from anywhere ‼  June 9, 2017.

\section{RATH}

This module is intended to house material copied over from the |RATH-Agda| libraries.

\begin{code}
module RATH where

open import Level public
   renaming ( _⊔_ to  _⊍_ ; zero to ℓ₀ ; suc to ℓsuc )

open import Relation.Binary
open import Relation.Binary.Sum using (_⊎-setoid_)

infix 1 _⊎⊎_
_⊎⊎_ : {i₁ i₂ k₁ k₂ : Level} → Setoid i₁ k₁ → Setoid i₂ k₂ → Setoid (i₁ ⊍ i₂) (i₁ ⊍ i₂ ⊍ k₁ ⊍ k₂)
A ⊎⊎ B = A ⊎-setoid B
\end{code}

\centerline{\textbf{** Everything that follows, in this section, is not live code ** }}

Z-style notation for sums,
\begin{spec}
open import Data.Product public renaming (<_,_> to ⟨_,_⟩) hiding (Σ-syntax)
Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊍ b)
Σ∶• = Data.Product.Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B
\end{spec}

From private repos of Wolfram Kahl,

\begin{spec}
import Relation.Binary.Indexed as IS

record IsDepEquivalence {a b c ℓ} {I : Setoid a b} {A : Setoid.Carrier I → Set c}
                       (_≈_ : IS.Rel A ℓ)
                       : Set (a ⊍ b ⊍ c ⊍ ℓ) where
                       
  open Setoid I using () renaming (Carrier to I₀ ; _≈_ to _≈ᵢ_)     
  field
      reflexive     : {i j : Setoid.Carrier I} → i ≈ᵢ j → (x : A i) → Σ y ∶ A j • x ≈ y
      sym           : IS.Symmetric A _≈_
      trans         : IS.Transitive A _≈_

  -- Derived component saying that |_≈_| is an Indexed equivalence relation:
  isEquivalence  : IS.IsEquivalence A _≈_
  isEquivalence = record
    { refl = λ {i} {x} → let x≈x′ = proj₂ (reflexive (Setoid.refl I) x) in trans x≈x′ (sym x≈x′)
    ; sym = sym
    ; trans = trans
    }

  open IS.IsEquivalence isEquivalence public using (refl)

record DepSetoid {a b : Level} (I : Setoid a b) c ℓ : Set (ℓsuc (c ⊍ a ⊍ b ⊍ ℓ)) where
  infix 4 _≈_
  open Setoid I using () renaming (Carrier to I₀ ; _≈_ to _≈ᵢ_) 
  field
    Carrier           : I₀ → Set c
    _≈_               : IS.Rel Carrier ℓ
    isDepEquivalence  : IsDepEquivalence {I = I} {A = Carrier} _≈_

  open IsDepEquivalence isDepEquivalence public
  indexedSetoid : IS.Setoid I₀ c ℓ
  indexedSetoid = record { Carrier = Carrier; _≈_ = _≈_; isEquivalence = isEquivalence }

ΣΣ : {s₁ s₂ c ℓ : Level} (I : Setoid c ℓ) → DepSetoid I s₁ s₂ → Setoid (s₁ ⊍ c) (s₂ ⊍ ℓ)
ΣΣ I S = let open DepSetoid S in record
  { Carrier = Σ (Setoid.Carrier I) Carrier
  ; _≈_ = λ x y → proj₁ x ≈ᵢ proj₁ y × proj₂ x ≈ proj₂ y
  ; isEquivalence = record
    { refl = Setoid.refl I , refl
    ; sym = λ x≈y → Setoid.sym I (proj₁ x≈y) , sym (proj₂ x≈y)
    ; trans = λ x≈y y≈z → Setoid.trans I (proj₁ x≈y) (proj₁ y≈z) , trans (proj₂ x≈y) (proj₂ y≈z)
    }
  } where open Setoid I using () renaming (_≈_ to _≈ᵢ_)
\end{spec}

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
