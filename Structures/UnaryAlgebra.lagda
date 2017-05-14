\begin{code}
module Structures.UnaryAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor; Contravariant)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda using (Sets)
open import Function renaming (id to idF; _∘_ to _◎_)

open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)

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

-- An 'Eventually' type
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
\end{code}

And now for a different way of looking at the same algebra.

\begin{code}
Free² : ∀ o → Functor (Sets o) (UnaryCat {o})
Free² o = record
  { F₀ = λ A → MkUnary (A × ℕ) (λ { (x , n) → (x , suc n) })
  ; F₁ = λ f → MkHom (λ { (x , n) → (f x , n) }) (λ _ → ≡.refl)
  ; identity = ≐-refl
  ; homomorphism = ≐-refl
  ; F-resp-≡ = λ F≡G → λ { (x , n) → ≡.cong₂ _,_ (F≡G {x}) ≡.refl }
  }

iter : {o : Level} {A : Set o} (f : A → A) (n : ℕ) → A → A
iter f ℕ.zero x = x
iter f (suc n) x = iter f n (f x)

AdjLeft² : ∀ o → Adjunction (Free² o) (Forget o)
AdjLeft² o = record
  { unit = record { η = λ _ x → x , 0 ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ { (MkUnary A f) → MkHom (λ { (x , n) → iter f n x }) {!!} }
    ; commute = {!!} }
  ; zig = {!!}
  ; zag = ≡.refl
  }
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
