Forgetful functor builder for single-sorted algebras to Sets

%{{{ Imports
\begin{code}
module Forget where

open import Level

open import Categories.Category using (Category;_[_,_])
open import Categories.Functor using (Functor)
open import Categories.Agda using (Sets)

open import Equiv hiding (_●_)
open import Function2

open import Function renaming (id to idF; _∘_ to _◎_)
open import Relation.Binary.PropositionalEquality using ()
  renaming (_≡_ to _≣_; cong to ≣-cong; trans to _●_; sym to ≣-sym)
\end{code}
%}}}

%{{{ OneSortedAlg
\begin{code}
record OneSortedAlg {ℓ} : Set (suc (suc ℓ)) where
  field
    Alg : Set (suc ℓ)
    obj : Alg → Set ℓ
    Hom : Alg → Alg → Set ℓ
    func : ∀ {a b : Alg} → Hom a b → (obj a → obj b)
    comp : ∀ {a b c : Alg} → Hom b c → Hom a b →  Hom a c
    .o-is-∘ : ∀ {a b c : Alg} {g : Hom b c} {f : Hom a b} → func (comp g f) ∼ (func g) ◎ (func f)
    idH : ∀ {a} → Hom a a
    .idH-is-id : ∀ {a : Alg} → func (idH {a}) ∼ idF
\end{code}
%}}}

%{{{ oneSorted
\begin{code}
oneSorted : ∀ o → OneSortedAlg {o} → Category (suc o) o o
oneSorted o A = record
  { Obj = Alg
  ; _⇒_ = Hom
  ; _≡_ = λ h₁ h₂ → (func h₁) ∼ (func h₂)
  ; id = idH
  ; _∘_ = comp
  ; assoc = λ {A} {_} {_} {_} {f} {g} {h} x → o-is-∘ x ● (o-is-∘ (func f x) ● (≣-cong (func h) (≣-sym (o-is-∘ x)) ● ≣-sym (o-is-∘ _)))
  ; identityˡ = λ {_} {_} {f} → trans∼ o-is-∘ (λ x → idH-is-id (func f x))
  ; identityʳ = λ {_} {_} {f} → trans∼ o-is-∘ (λ x → ≣-cong (func f) (idH-is-id x))
  ; equiv = record { refl = refl∼ ; sym = sym∼ ; trans = trans∼ }
  ; ∘-resp-≡ = λ f≡h g≡i → trans∼ o-is-∘ (trans∼ (∘-resp-∼ f≡h g≡i) (sym∼ o-is-∘))
  }
  where open OneSortedAlg A
\end{code}
%}}}

%{{{ mkForgetful
\begin{code}
mkForgetful : ∀ o → (A : OneSortedAlg {o}) → Functor (oneSorted o A) (Sets o)
mkForgetful o A = record
  { F₀ = obj
  ; F₁ = func
  ; identity = λ {_} {x} → idH-is-id x
  ; homomorphism = λ { {x = x} → o-is-∘ x}
  ; F-resp-≡ =  _$ᵢ
  }
  where
    open OneSortedAlg A
    module B = Category (oneSorted o A)
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

