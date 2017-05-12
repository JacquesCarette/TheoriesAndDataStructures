\begin{code}
module Structures.UnaryAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor; Contravariant)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function renaming (id to idF; _∘_ to _◎_)

open import Data.List

open import Equiv
open import Forget
open import Function2
open import Structures.Pointed using (PointedCat; Pointed; _●_) renaming (Hom to PHom ; MkHom to MkPHom)

import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ using (_≡_)

open import Data.Product using (_×_; _,_)

record Unary {ℓ} : Set (lsuc ℓ) where
  constructor MkUnary
  field
    Carrier : Set ℓ
    Op      : Carrier → Carrier

open Unary

record Hom {ℓ} (X Y : Unary {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor        :  Carrier X → Carrier Y
    pres-op    :  mor ◎ Op X ≐  Op Y ◎ mor

open Hom

UnaryAlg : ∀ {o} → OneSortedAlg o
UnaryAlg = record
  { Alg = Unary
  ; Carrier = Carrier
  ; Hom = Hom
  ; mor = mor
  ; comp = λ F G → record
    { mor      =  mor F ◎ mor G
    ; pres-op  =  λ a → ≡.trans (≡.cong (mor F) (pres-op G a)) (pres-op F (mor G a))
    }
  ; comp-is-∘     =  ≐-refl
  ; Id        =  MkHom idF ≐-refl
  ; Id-is-id  =  ≐-refl
  }

UnaryCat : ∀ {ℓ} → Category _ ℓ ℓ
UnaryCat {o} = oneSortedCategory o UnaryAlg

Forget : ∀ o → Functor (UnaryCat {o}) (Sets o)
Forget o = mkForgetful o UnaryAlg

-- Type-polymorphic naturals
data ℕ {ℓ} : Set ℓ where
  zero : ℕ {ℓ}
  suc  : ℕ {ℓ} → ℕ {ℓ}
  
iter : ∀ {ℓ o} {A : Set o} (n : ℕ {ℓ}) (g : A → A) → A → A
iter zero    g a = a
iter (suc n) g a = iter n g (g a)

-- eliminator
induct : ∀ {ℓ o} {P : ℕ {ℓ} → Set o}
  (base : P zero) (inductiveStep : ∀ (i : ℕ) → P i → P (suc i) )
  → (n : ℕ) → P n
induct base step zero    = base
induct base step (suc n) = step n (induct base step n)

-- |iter g n| is essentially |gⁿ| and so |g ∙ gⁿ = gⁿ · g|, as expected.
iter-nat : ∀ {ℓ o} (n : ℕ {ℓ}) → ∀ {A : Set o} (g : A → A) → iter n g ◎ g ≐ g ◎ iter n g
iter-nat = induct {P = λ n →  ∀ {A} (g : A → A) (a : A) → iter n g (g a) ≡ g (iter n g a)} (λ g a → ≡.refl) (λ i pf g a → pf g (g a))
--
-- MA: This looks unnatural, a shorter and more natural approach seems to be direct pattern matching.

-- MA: A new maybe-nat hybrid type
data ForeverMaybe {ℓ} (A : Set ℓ) : Set ℓ where
  base : A → ForeverMaybe A
  step : ForeverMaybe A → ForeverMaybe A
--
-- Elements of this type are of the form |stepⁿ (base a)| for |a : A|.
--
-- really this is the ``term algebra'' over unary signatures.

fromFM : ∀{ℓ} {A : Set ℓ} → ForeverMaybe A → A
fromFM (base x) = x
fromFM (step m) = fromFM m
--
-- More generally,
--
iterateFM : ∀ {ℓ } {A : Set ℓ} (f : A → A) → ForeverMaybe A → A
iterateFM f (base x) = x
iterateFM f (step x) = f (iterateFM f x)
--
-- that is, |iterateFM f (stepⁿ base x) ≈ fⁿ x|

fmMap : ∀{a b}{A : Set a}{B : Set b} → (A → B) → ForeverMaybe A → ForeverMaybe B
fmMap F (base x) = base (F x)
fmMap F (step e) = step (fmMap F e)
--
-- note that fmMap preserves the number of |step|s
--
fmMap-nat : ∀{ℓ a b}  {A : Set a} {B : Set b} {f : A → B} { n : ℕ {ℓ}}
  → fmMap f ◎ iter n step ≐ iter n step ◎ fmMap f
fmMap-nat {f = f} {zero} e   =  ≡.refl
fmMap-nat {f = f} {suc n} e  =  fmMap-nat {n = n} (step e)


iterateFM-nat : ∀ {o} {X Y : Unary {o}} (F : Hom X Y)
              → iterateFM (Op Y) ◎ fmMap (mor F) ≐ mor F ◎ iterateFM (Op X)
iterateFM-nat F (base x) = ≡.refl
iterateFM-nat {X = X} {Y = Y} F (step x) = begin
  (iterateFM (Op Y) ◎ fmMap (mor F) ◎ step) x
    ≡⟨ ≡.refl ⟩  -- definitions of fmMap and then iterateFM
  (Op Y ◎ iterateFM (Op Y) ◎ fmMap (mor F)) x
    ≡⟨ ≡.cong (Op Y) (iterateFM-nat F x) ⟩
  (Op Y ◎ mor F ◎ iterateFM (Op X)) x
    ≡⟨ ≡.sym (pres-op F _) ⟩ 
  (mor F ◎ Op X ◎ iterateFM (Op X)) x
    ≡⟨ ≡.refl ⟩ -- definition of iterateFM, in reverse
  (mor F ◎ iterateFM (Op X) ◎ step) x
     ∎
     where open ≡.≡-Reasoning {A = Carrier Y}

iterateFM-fmMap-id : ∀ {o} {X : Set o} → idF {A = ForeverMaybe X} ≐ iterateFM step ◎ fmMap base
iterateFM-fmMap-id (base x) = ≡.refl
iterateFM-fmMap-id (step x) = ≡.cong step (iterateFM-fmMap-id x)

fmMap-id : ∀{a}  {A : Set a} → fmMap (idF {A = A}) ≐ idF
fmMap-id (base e) = ≡.refl
fmMap-id (step e) = ≡.cong step (fmMap-id e)

fmMap-∘ : ∀ {o} {X Y Z : Set o} {f : X → Y} {g : Y → Z}
        →  fmMap (g ◎ f) ≐ fmMap g ◎ fmMap f
fmMap-∘ (base x) = ≡.refl
fmMap-∘ (step e) = ≡.cong step (fmMap-∘ e)

fmMap-cong : ∀{o} {A B : Set o} {F G : A → B} → F ≐ G → fmMap F ≐ fmMap G
fmMap-cong eq (base x) = ≡.cong base (eq x)
fmMap-cong eq (step x) = ≡.cong step (fmMap-cong eq x)

-- MA: This orginally had |F₀ = λ A → MkUnary ℕ suc|, which seems exceedingly suspcious
-- since no mention of |A| occurs on the LHS. So I've changed things.
Free : ∀ o → Functor (Sets o) (UnaryCat {o})
Free o = record
  { F₀             =   λ A → MkUnary (ForeverMaybe A) step
  ; F₁             =   λ f → MkHom (fmMap f) ≐-refl
  ; identity       =   fmMap-id
  ; homomorphism   =   fmMap-∘
  ; F-resp-≡      =   λ F≈G → fmMap-cong (λ _ → F≈G)
  }

AdjLeft : ∀ o → Adjunction (Free o) (Forget o)
AdjLeft o = record
  { unit     =   record { η = λ _ → base ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ { (MkUnary A f) → MkHom (iterateFM f) ≐-refl} ; commute = iterateFM-nat }
  ; zig      =   iterateFM-fmMap-id
  ; zag      =   ≡.refl
  }

open import Relation.Nullary using (¬_)
open import Data.Empty
open import Data.Bool
open import Relation.Unary

contr : .(true ≡ false) → ⊥
contr ()

NoFree : ∀ o → (Free : Functor (Sets o) UnaryCat) → ¬ Adjunction Free (Forget o)
NoFree o record { F₀ = F₀ ; F₁ = F₁ ; identity = identity ; homomorphism = homomorphism ; F-resp-≡ = F-resp-≡ }
         record { unit = record { η = η′ ; commute = commute′ } ; counit = record { η = η ; commute = commute } ; zig = zig ; zag = zag } =
     let swap : Lift {lzero} {o} Bool → Lift Bool
         swap = λ {(lift true) → lift false; (lift false) → lift true} in
     let u = MkUnary (Lift Bool) swap in
     let v = MkUnary (Lift Bool) swap in
     let hh = MkHom {o} {u} {v} swap (λ {(lift true) → ≡.refl; (lift false) → ≡.refl}) in
      contr (≡.cong lower (≡.trans (zag {u} {lift true})
                          (≡.trans {!!} (≡.sym (zag {v} {lift false})))))

-- Hom.pres-f (η (unar (Lift Bool) (λ {(lift true) → lift false; (lift false) → lift true})))
{-
-- for the proofs below, we "cheat" and let η for records make things easy.
Right : ∀ o → Functor (Sets o) (InvCat {o})
Right o = record
  { F₀ = λ B → record { A = B × B ; _ᵒ = swap ; involutive = ≐-refl }
  ; F₁ = λ g → record { f = map× g g ; pres-ᵒ = ≐-refl }
  ; identity = ≐-refl
  ; homomorphism = ≐-refl
  ; F-resp-≡ = λ F≡G a → ≡.cong₂ _,_ (F≡G {proj₁ a}) F≡G
  }

diag : ∀ {ℓ} {A : Set ℓ} (a : A) → A × A
diag a = a , a

AdjRight : ∀ o → Adjunction (U o) (Right o)
AdjRight o = record
  { unit = record { η = λ inv → record { f = λ a → map× idF (_ᵒ inv) (diag a)
                                       ; pres-ᵒ = λ a → ≡.cong₂ _,_ ≡.refl (involutive inv a) }
                  ; commute = λ f a → ≡.cong₂ _,_ ≡.refl (≡.sym (Hom.pres-ᵒ f a)) }
  ; counit = record { η = λ _ → proj₁ ; commute = λ _ → ≡.refl }
  ; zig = ≡.refl
  ; zag = λ _ → ≡.refl
  }
  where open Inv
-}


\end{code}

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
