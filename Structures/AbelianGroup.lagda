\section{Structures.AbelianGroup}
%{{{ Imports
\begin{code}
module Structures.AbelianGroup where

open import Level renaming (suc to lsuc; zero to lzero)

open import Helpers.Categorical

open import Function              using (const ; id ; _∘_ ; _$_)
open import Data.Empty
open import Relation.Unary        using (Pred; _∈_; _∪_; _∩_)
open import Algebra hiding (Monoid)
open import Algebra.Structures

open import Helpers.Function2             using (_$ᵢ)
open import Helpers.EqualityCombinators
open import Helpers.DataProperties hiding (⊥ ; ⊥-elim)

open import Data.Nat                using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin                using (Fin; inject+; raise)
open import Data.Integer            using (ℤ; _+_; +_; -_)
open import Data.Integer.Properties using (+-*-commutativeRing)
\end{code}

%}}}

%{{{ G1

The retract of an abelian group is an Abelian group;
we only show this for the case of ℤ.

\begin{code}
G1 : ∀ (c : Level) (A : Set c) → AbelianGroup c c
G1 c A = record
  { Carrier   =   A → ℤ
  ; _≈_       =   _≐_
  ; _∙_       =   λ f g a → f a + g a
  ; ε         =   λ _ → + 0
  ; _⁻¹        =   λ f a → - f a
  ; isAbelianGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isEquivalence = ≐-isEquivalence
          ; assoc = λ f g h a → AG.+-assoc (f a) (g a) (h a)
          ; ∙-cong = λ x≈y u≈v a → AG.+-cong (x≈y a) (u≈v a)
          }
        ; identity =  (λ h a → proj₁ AG.+-identity (h a)) , (λ h a → proj₂ AG.+-identity (h a))
        }
      ; inverse = (λ h a → proj₁ AG.-‿inverse (h a)) , (λ h a → proj₂ AG.-‿inverse (h a))
      ; ⁻¹-cong = λ i≈j a → ≡.cong (λ z → - z) (i≈j a)
      }
    ; comm = λ f g a → AG.+-comm (f a) (g a)
    }
  }
  where
    module AG = CommutativeRing +-*-commutativeRing
\end{code}

%}}}

%{{{ Hom

MA: One of our aims is to live in SET; yet the overall design of AbelianGroup,
in the standard library, is via SETOID. Perhaps it would be prudent to make our
own SET version? Otherwise, we run into a hybrid of situations such as those
below regarding cong and expected derivable preservation properties.
--cf the cong in the injective proof of G2 near the bottom.

\begin{code}
record Hom {o ℓ} (X Y : AbelianGroup o ℓ) : Set (o ⊔ ℓ) where
  constructor MkHom
  open AbelianGroup X using () renaming (_∙_ to _+₁_; ε to 0₁; _⁻¹ to -₁_; _≈_ to _≈₁_)
  open AbelianGroup Y using () renaming (_∙_ to _+₂_; ε to 0₂; _⁻¹ to -₂_ ; _≈_ to _≈₂_)
  open AbelianGroup using (Carrier)
  field
    mor       :  Carrier X → Carrier Y
    pres-+    :  ∀ x y → mor (x +₁ y) ≡ mor x +₂ mor y
    pres-0    :  mor 0₁ ≡ 0₂
    pres-inv  :  ∀ x → mor (-₁ x) ≡ -₂ (mor x)

  inv-char : {x y : Carrier Y} → x +₂ y ≈₂ 0₂ → y ≈₂ -₂ x
  inv-char {x} {y} x+y≈0 = begin⟨ (record {AbelianGroup Y }) ⟩
    y                 ≈˘⟨ proj₁ identity y                   ⟩
    0₂ +₂ y           ≈˘⟨ ∙-cong (proj₁ inverse x) refl      ⟩
    (-₂ x +₂ x) +₂ y  ≈⟨ assoc _ _ _                         ⟩
     -₂ x +₂ (x +₂ y) ≈⟨ ∙-cong refl x+y≈0                   ⟩
     -₂ x +₂ 0₂       ≈⟨ proj₂ identity _                    ⟩
    -₂ x              ∎
    where open import Relation.Binary.SetoidReasoning
          open AbelianGroup Y

  postulate expected : {x y : Carrier X} → x ≈₁ y → mor x ≈₂ mor y
  pres-inv-redundant : {x : Carrier X} → mor (-₁ x) ≈₂ -₂ (mor x)
  pres-inv-redundant {x} = inv-char (begin⟨ (record {AbelianGroup Y }) ⟩
    mor x +₂ mor (-₁ x) ≡⟨ ≡.sym (pres-+ _ _)                        ⟩
    mor (x +₁ -₁ x)     ≈⟨  expected (proj₂ (AbelianGroup.inverse X) _) ⟩
    mor 0₁              ≡⟨ pres-0                                     ⟩
    0₂                  ∎)
    where open import Relation.Binary.SetoidReasoning

open Hom
\end{code}

%}}}

%{{{ AbelianGroupCat ; Forget

\begin{code}
AbelianGroupCat : ∀ o ℓ → Category (lsuc (o ⊔ ℓ)) (o ⊔ ℓ) o
AbelianGroupCat o ℓ = record
  { Obj   =   AbelianGroup o ℓ
  ; _⇒_  =   Hom
  ; _≡_  =   λ f g → mor f ≐ mor g
  ; id    =   MkHom id (λ _ → ≐-refl) ≡.refl ≐-refl
  ; _∘_   =   λ F G → record
    { mor       =  mor F ∘ mor G
    ; pres-+    =  λ x y → ≡.cong (mor F) (pres-+ G x y) ⟨≡≡⟩ pres-+ F (mor G x) (mor G y)
    ; pres-0    =  ≡.cong (mor F) (pres-0 G) ⟨≡≡⟩ pres-0 F
    ; pres-inv  =  λ x → ≡.cong (mor F) (pres-inv G x) ⟨≡≡⟩ pres-inv F (mor G x)
    }
  ; assoc     =   ≐-refl
  ; identityˡ  =   ≐-refl
  ; identityʳ  =   ≐-refl
  ; equiv      =   record { IsEquivalence ≐-isEquivalence}
  ; ∘-resp-≡  =   ∘-resp-≐
  }
    where open AbelianGroup
          open import Relation.Binary using (IsEquivalence)

Forget : (o ℓ : Level) → Functor (AbelianGroupCat o ℓ) (Sets o)
Forget o ℓ = record
  { F₀             =   AbelianGroup.Carrier
  ; F₁             =   Hom.mor
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   _$ᵢ
  }
\end{code}

%}}}

\begin{code}
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection using (Injection; _↣_; module Injection)
open import Relation.Nullary using (¬_)
\end{code}

\begin{code}
record DirectSum {o : Level} (A : Set o) : Set (lsuc o) where
  constructor FormalSum
  field
    f       :   A → ℤ
    B        :   Pred A o                     -- basis?
    finite   :   Σ ℕ (λ n → (Σ A B ↣ Fin n))

open DirectSum
\end{code}

|⁉|
• f is the injection of the “|A|lphabet” as “words” with possibly ``negative multiplicity''.
• B is the subset of all words that contains only the reduced words.
• finite is the proof that our construction has finite support.

%{{{ drop-suc ; inject+-inject ; raise-inject ; raise≢inject+ ; on-right₁ ; on-right₂
\begin{code}
private
  -- JC: why is this defined in Data.Fin.Properties but not exported?
  drop-suc : ∀ {o} {m n : Fin o} → Fin.suc m ≡ Fin.suc n → m ≡ n
  drop-suc ≡.refl = ≡.refl

  inject+-inject : ∀ {m n} → {i j : Fin m} → inject+ n i ≡ inject+ n j → i ≡ j
  inject+-inject {i = Fin.zero} {Fin.zero} ≡.refl = ≡.refl
  inject+-inject {i = Fin.zero} {Fin.suc _} ()
  inject+-inject {i = Fin.suc i} {Fin.zero} ()
  inject+-inject {i = Fin.suc i} {Fin.suc j} pf = ≡.cong Fin.suc (inject+-inject (drop-suc pf))

  raise-inject : ∀ {m n} → {i j : Fin m} → raise n i ≡ raise n j → i ≡ j
  raise-inject {n = ℕ.zero} pf = pf
  raise-inject {n = suc n} pf = raise-inject {n = n} (drop-suc pf)

  raise≢inject+ : (m n : ℕ) (i : Fin m) (j : Fin n) → ¬ (raise n i ≡ inject+ m j)
  raise≢inject+ m (suc n) i Fin.zero ()
  raise≢inject+ m _ i (Fin.suc j) eq = raise≢inject+ m _ i j (drop-suc eq)

  on-right₁ : {ℓ ℓ′ : Level} {A : Set ℓ} {B₁ B₂ : A → Set ℓ′} {a₁ a₂ : A} {b₁ : B₁ a₁} {b₂ : B₁ a₂}
            → (a₁ , b₁) ≡ (a₂ , b₂) → _≡_ {_} {Σ A (B₁ ∪ B₂)} (a₁ , inj₁ b₁) (a₂ , inj₁ b₂)
  on-right₁ ≡.refl = ≡.refl

  on-right₂ : {ℓ ℓ′ : Level} {A : Set ℓ} {B₁ B₂ : A → Set ℓ′} {a₁ a₂ : A} {b₁ : B₂ a₁} {b₂ : B₂ a₂}
            → (a₁ , b₁) ≡ (a₂ , b₂) → _≡_ {_} {Σ A (B₁ ∪ B₂)} (a₁ , inj₂ b₁) (a₂ , inj₂ b₂)
  on-right₂ ≡.refl = ≡.refl
\end{code}

%}}}

%{{{ G2

The DirectSum datatype furnishes any type with the structure of an AbelianGroup.
This is a step in constructing a Free functor.

\begin{code}
G2 : ∀ (c : Level) (A : Set c) → AbelianGroup (lsuc c) c
G2 c A = record
  { Carrier = DirectSum A
  ; _≈_ = λ a₁ a₂ → f a₁ ≐ f a₂
  ; _∙_ = λ{ (FormalSum f₁ B₁ (n₁ , fin₁)) (FormalSum f₂ B₂ (n₂ , fin₂)) → record
    { f       =  λ e → f₁ e + f₂ e
    ; B       =  B₁ ∪ B₂
    ; finite  =  n₁ +ℕ n₂ , record
      { to        = record
        { _⟨$⟩_ = λ { (a , inj₁ b) → inject+ n₂ (to fin₁ ⟨$⟩ (a , b))
                   ; (a , inj₂ b) → raise n₁ (to fin₂ ⟨$⟩ (a , b))
                   }
        ; cong = λ { {i} {.i} ≡.refl → ≡.refl }
        }
      ; injective = λ { {(a₁ , inj₁ b₁)} {(a₂ , inj₁ b₂)} pf → on-right₁ (injective fin₁ (inject+-inject pf))
                      ; {(a₁ , inj₂ b₁)} {(a₂ , inj₁ b₂)} pf → ⊥-elim (raise≢inject+ _ _ _ _ pf)
                      ; {(a₁ , inj₁ b₁)} {(a₂ , inj₂ b₂)} pf → ⊥-elim (raise≢inject+ _ _ _ _ (≡.sym pf))
                      ; {(a₁ , inj₂ b₁)} {(a₂ , inj₂ b₂)} pf → on-right₂ (injective fin₂ (raise-inject {n = n₁} pf))
                      }
      }
    }}
  ; ε = record
      { f       =  λ _ → + 0
      ; B       =  λ _ → Lift ⊥
      ; finite  =  0 , record
        { to        = record
          { _⟨$⟩_  = λ {(_ , lift ())}
          ; cong  = λ { {i} {.i} ≡.refl → ≡.refl }
          }
        ; injective = λ { {(_ , lift ())} }
        }
      }
  ; _⁻¹ = λ F → FormalSum (λ a → - f F a) (B F) (finite F)
  ; isAbelianGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isEquivalence = record { IsEquivalence ≐-isEquivalence}
          ; assoc = λ F G H a → AG.+-assoc (f F a) (f G a) (f H a)
          ; ∙-cong = λ x≈y u≈v a → AG.+-cong (x≈y a) (u≈v a)
          }
        ; identity = (λ F a → proj₁ AG.+-identity (f F a)) , (λ F a → proj₂ AG.+-identity (f F a))
        }
      ; inverse = (λ F a → proj₁ AG.-‿inverse (f F a)) , (λ F a → proj₂ AG.-‿inverse (f F a))
      ; ⁻¹-cong = λ i≈j a → ≡.cong (λ z → - z) (i≈j a)
      }
    ; comm = λ F G a → AG.+-comm (f F a) (f G a)
    }
  }
  where
    module AG = CommutativeRing +-*-commutativeRing
    open DirectSum
    open Injection
    open import Relation.Binary using (IsEquivalence)
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
