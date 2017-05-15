%{{{ Imports
\begin{code}
module Structures.UnaryAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)

open import Categories.Category   using (Category; module Category)
open import Categories.Functor    using (Functor; Contravariant)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Forget

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_ ; Σ; proj₁; proj₂; uncurry; map)

open import Function2
open import Function

open import EqualityCombinators
\end{code}
%}}}

%{{{ Unary ; Hom ; UnaryAlg ; UnaryCat ; Forget

A single-sorted |Unary| algebra consists of a type along with a function on that type.
For example, the naturals and addition-by-1 or lists and the reverse operation.

Along with functions that preserve the elected operation, such algberas form a category.

\begin{code}
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
    pres-op    :  mor ∘ Op X ≐  Op Y ∘ mor

open Hom

UnaryAlg : {ℓ : Level} → OneSortedAlg ℓ
UnaryAlg = record
  { Alg       = Unary
  ; Carrier   = Carrier
  ; Hom       = Hom
  ; mor       = mor
  ; comp      = λ F G → record
    { mor     =  mor F ∘ mor G
    ; pres-op =  λ a → ≡.trans (≡.cong (mor F) (pres-op G a)) (pres-op F (mor G a))
    }
  ; comp-is-∘ =  ≐-refl
  ; Id        =  MkHom id ≐-refl
  ; Id-is-id  =  ≐-refl
  }

UnaryCat : {ℓ : Level} → Category (lsuc ℓ) ℓ ℓ
UnaryCat {ℓ} = oneSortedCategory ℓ UnaryAlg

Forget : (ℓ : Level) → Functor (UnaryCat {ℓ}) (Sets ℓ)
Forget ℓ = mkForgetful ℓ UnaryAlg
\end{code}

%}}}

%{{{ Eventually ; 

We now turn to finding a free unary algebra.

Indeed, we do so by simply not ``interpreting'' the single function symbol that is required
as part of the definition. That is, we form the ``term algebra'' over the signature for
unary algebras.

\begin{code}
data Eventually {ℓ} (A : Set ℓ) : Set ℓ where
  base : A → Eventually A
  step : Eventually A → Eventually A
\end{code}
The elements of this type are of the form |stepⁿ (base a)| for |a : A|.

Alternatively, |Eventually A   ≅   Σ n ∶ ℕ • A| viz |stepⁿ (base a) ↔ (n , a)| ---cf |Free²| below.
Consequently, |Eventually ⊤ ≅ ℕ|.

Given an unary algebra |(B, 𝒷, 𝓈)| we can interpret the terms of |Eventually A|
where the injection |base| is reified by |𝒷| and the unary operation |step| is
reified by |𝓈|.

\begin{code}
⟦_,_⟧ : {a b : Level} {A : Set a} {B : Set b} (𝒷 : A → B) (𝓈 : B → B) → Eventually A → B
⟦ 𝒷 , 𝓈 ⟧ (base x) = 𝒷 x
⟦ 𝒷 , 𝓈 ⟧ (step e) = 𝓈 (⟦ 𝒷 , 𝓈 ⟧ e)
--
-- “The number of 𝓈teps is preserved” : ⟦ 𝒷 , 𝓈 ⟧ ∘ stepⁿ ≐ 𝓈ⁿ ∘ ⟦ 𝒷 , 𝓈 ⟧
--
-- Essentially, ⟦ 𝒷 , 𝓈 ⟧ (stepⁿ base x) ≈ 𝓈ⁿ 𝒷 x

indE : {ℓ a : Level} {A : Set a} {P : Eventually A → Set ℓ}
     → ({x : A} → P (base x))
     → ({sofar : Eventually A} → P sofar → P (step sofar))
     → (ev : Eventually A) → P ev
indE {P = P} b s (base x) = b
indE {P = P} b s (step ev) = s (indE {P = P} b s ev)
\end{code}

There's gotta be a way to put these two together into a single operation...

   %{{{ mapeE ; ⟦⟧-naturality
Eventually is clearly a functor,

\begin{code}
mapE : {a b : Level} {A : Set a} {B : Set b} → (A → B) → (Eventually A → Eventually B)
mapE f = ⟦ base ∘ f , step ⟧
\end{code}

Whence the folding operation is natural,

\begin{code}
⟦⟧-naturality : {a b : Level} {A : Set a} {B : Set b}
              → {𝒷′ 𝓈′ : A → A} {𝒷 𝓈 : B → B} {f : A → B}
              → (basis : 𝒷 ∘ f ≐ f ∘ 𝒷′)
              → (next  : 𝓈 ∘ f ≐ f ∘ 𝓈′)
              → ⟦ 𝒷 , 𝓈 ⟧ ∘ mapE f ≐ f ∘ ⟦ 𝒷′ , 𝓈′ ⟧
⟦⟧-naturality {𝓈 = 𝓈} basis next = indE (basis $ᵢ) (λ ind → ≡.trans (≡.cong 𝓈 ind) (next _))
\end{code}
%}}}

   %{{{ fromE ; iterateE ; iterateE-nat

Other instances of the fold include:

\begin{code}
fromE : ∀{ℓ} {A : Set ℓ} → Eventually A → A
fromE = ⟦ id , id ⟧ -- cf |from⊎| ;)

-- More generally,

iterateE : ∀ {ℓ } {A : Set ℓ} (f : A → A) → Eventually A → A
iterateE f = ⟦ id , f ⟧
--
-- that is, |iterateE f (stepⁿ base x) ≈ fⁿ x|

iterateE-nat : {ℓ : Level} {X Y : Unary {ℓ}} (F : Hom X Y)
              → iterateE (Op Y) ∘ mapE (mor F) ≐ mor F ∘ iterateE (Op X)
iterateE-nat F = ⟦⟧-naturality {f = mor F} ≐-refl (≡.sym ∘ pres-op F)
\end{code}

%}}}

   %{{{ iterateE-mapeE-id , mapE-id , mapE-∘ , mapE-cong

The induction rule yields identical looking proofs for clearly distinct results:

\begin{code}
iterateE-mapE-id : {ℓ : Level} {X : Set ℓ} → id {A = Eventually X} ≐ iterateE step ∘ mapE base
iterateE-mapE-id = indE ≡.refl (≡.cong step)

mapE-id : {a : Level}  {A : Set a} → mapE (id {A = A}) ≐ id
mapE-id = indE ≡.refl (≡.cong step)

mapE-∘ : {ℓ : Level} {X Y Z : Set ℓ} {f : X → Y} {g : Y → Z}
        →  mapE (g ∘ f) ≐ mapE g ∘ mapE f
mapE-∘ = indE ≡.refl (≡.cong step)

mapE-cong : ∀{o} {A B : Set o} {F G : A → B} → F ≐ G → mapE F ≐ mapE G
mapE-cong eq = indE (≡.cong base ∘ eq $ᵢ) (≡.cong step)
\end{code}

These results could be generalised to ⟦_,_⟧ if needed.

%}}}

   %{{{ Free ; AdjLeft

That |Eventually| furnishes a set with its free unary algebra can now be realised.

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (UnaryCat {ℓ})
Free ℓ = record
  { F₀             =   λ A → MkUnary (Eventually A) step
  ; F₁             =   λ f → MkHom (mapE f) ≐-refl
  ; identity       =   mapE-id
  ; homomorphism   =   mapE-∘
  ; F-resp-≡      =   λ F≈G → mapE-cong (λ _ → F≈G)
  }

AdjLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
AdjLeft ℓ = record
  { unit     =   record { η = λ _ → base ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ A → MkHom (iterateE (Op A)) ≐-refl ; commute = iterateE-nat }
  ; zig      =   iterateE-mapE-id
  ; zag      =   ≡.refl
  }
\end{code}

%}}}

%{{{ Direct representation

And now for a different way of looking at the same algebra.
We ``mark'' a piece of data with its depth.

\begin{code}
Free² : ∀ o → Functor (Sets o) (UnaryCat {o})
Free² o = record
  { F₀             =   λ A → MkUnary (A × ℕ) (map id suc)
  ; F₁             =   λ f → MkHom (map f id) (λ _ → ≡.refl)
  ; identity       =   ≐-refl
  ; homomorphism   =   ≐-refl
  ; F-resp-≡      =   λ F≈G → λ { (x , n) → ≡.cong₂ _,_ (F≈G {x}) ≡.refl }
  }

_^_ : {a : Level} {A : Set a} (f : A → A) → ℕ → (A → A)
f ^ ℕ.zero = id
f ^ suc n = f ^ n ∘ f

-- important property of iteration that allows it to be defined in an alternative fashion
iter-alt : {ℓ : Level} {A : Set ℓ} {f : A → A} {n : ℕ} → (f ^ n) ∘ f ≐ f ∘ (f ^ n)
iter-alt {n = ℕ.zero} = ≐-refl
iter-alt {f = f} {n = suc n} = ∘-≐-cong₁ f iter-alt

iter : {o : Level} {A : Set o} (f : A → A) → A → ℕ → A
iter f x n = (f ^ n) x

iter-ℕ : {o : Level} {A : Set o} {f : A → A} (a : A) (n : ℕ) → iter f (f a) n ≡ f (iter f a n)
iter-ℕ {f = f} a n = iter-alt {f = f} {n = n} a

-- iteration of commutable functions
iter-comm : {o : Level} {B C : Set o} {f : B → C} {g : B → B} {h : C → C} → (f ∘ g ≐ h ∘ f) →
  ∀ (b : B) (n : ℕ) → iter h (f b) n ≡ f (iter g b n)
iter-comm eq a ℕ.zero = ≡.refl
iter-comm {f = f} {g} {h} eq a (suc n) = 
  begin
    iter h (h (f a)) n ≡⟨ iter-ℕ (f a) n ⟩
    h (iter h (f a) n) ≡⟨ ≡.cong h (iter-comm eq a n) ⟩
    h (f (iter g a n)) ≡⟨ ≡.sym (eq (iter g a n)) ⟩
    f (g (iter g a n)) ≡⟨ ≡.cong f (≡.sym (iter-ℕ a n))  ⟩
    f (iter g (g a) n)
  ∎
  where open ≡.≡-Reasoning

×-induct : {a b c : Level} {A : Set a} {B : A → Set b} {C : Σ A B → Set c}
  (g : (a : A) (b : B a) → C (a , b)) → ((p : Σ A B) → C p)
×-induct g = uncurry g

-- There has to be a simpler way, but this will do
zig′ : {a : Level} {A : Set a} (x : A) (n : ℕ) →
  (x , n) ≡ iter (map id suc) (x , 0) n
zig′ _ ℕ.zero = ≡.refl
zig′ x (suc n) = ≡.sym (
  begin
    iter (map id suc) (map id suc (x , 0)) n ≡⟨ iter-ℕ (x , 0) n ⟩
    map id suc (iter (map id suc) (x , 0) n) ≡⟨ ≡.cong (map id suc) (≡.sym (zig′ x n)) ⟩
    map id suc (x , n) ≡⟨ ≡.refl ⟩
    (x , suc n)
  ∎)
  where open ≡.≡-Reasoning

AdjLeft² : ∀ o → Adjunction (Free² o) (Forget o)
AdjLeft² o = record
  { unit = record { η = λ _ x → x , 0 ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ { (MkUnary A f) → MkHom (uncurry (iter f)) (uncurry iter-ℕ) }
    ; commute = λ { {MkUnary X x̂} {MkUnary Y ŷ} (MkHom f pres) → 
      uncurry (iter-comm {f = f} {x̂} {ŷ} pres) } }
  ; zig = uncurry zig′
  ; zag = ≡.refl
  }
  where
    open ≡.≡-Reasoning
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
