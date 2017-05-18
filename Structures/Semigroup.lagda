
%{{{ Imports
\begin{code}
module Structures.Semigroup where

open import Level renaming (suc to lsuc; zero to lzero)

open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Function              using (const ; id ; _∘_)
open import Data.Product          using (_×_; _,_)
open import Data.List             using (List; map; []; _∷_; _++_)

open import Function2 using (_$ᵢ)
open import EqualityCombinators
open import Forget
\end{code}
%}}}

%{{{ Semigroup ; _⟨_⟩_ ; Hom

A Free Semigroup is a Non-empty list
\begin{code}
record Semigroup {a} : Set (lsuc a) where
  constructor MkSG
  infixr 5 _*_
  field
    Carrier : Set a
    _*_     : Carrier → Carrier → Carrier
    assoc   : {x y z : Carrier} → x * (y * z) ≡ (x * y) * z

open Semigroup renaming (_*_ to Op)
bop = Semigroup._*_
syntax bop A x y = x ⟨ A ⟩ y

record Hom {ℓ} (Src Tgt : Semigroup {ℓ}) : Set ℓ where
  constructor MkHom
  field
    mor   :  Carrier Src → Carrier Tgt
    pres  :  {x y : Carrier Src} → mor (x ⟨ Src ⟩ y)   ≡  (mor x) ⟨ Tgt ⟩ (mor y)

open Hom
\end{code}

%}}}

%{{{ SGAlg ; SemigroupCat ; Forget
\begin{code}
SGAlg : {ℓ : Level} → OneSortedAlg ℓ
SGAlg = record
   { Alg         =   Semigroup
   ; Carrier     =   Semigroup.Carrier
   ; Hom         =   Hom
   ; mor         =   Hom.mor
   ; comp        =   λ F G → MkHom (mor F ∘ mor G) (≡.cong (mor F) (pres G) ⟨≡≡⟩ pres F)
   ; comp-is-∘   =   ≐-refl
   ; Id          =   MkHom id ≡.refl
   ; Id-is-id    =   ≐-refl
   }

SemigroupCat : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
SemigroupCat ℓ = oneSortedCategory ℓ SGAlg

Forget : (ℓ : Level) → Functor (SemigroupCat ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ SGAlg
\end{code}
%}}}

\begin{code}
NEList : {a : Level} → Set a → Set a
NEList A = A × List A

mapNE : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → NEList A → NEList B
mapNE f (x , l) = (f x) , map f l

{-
induct : ∀ {a c} {A : Set a} {P : Tree A → Set c}
  → ((x : A) → P (Leaf x)) → ({t₁ t₂ : Tree A} → P t₁ → P t₂ → P (Branch t₁ t₂))
  → (t : Tree A) → P t
induct         f g (Leaf x)     = f x
induct {P = P} f g (Branch s t) = g (induct {P = P} f g s) (induct {P = P} f g t)

fold : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → B → B) → Tree A → B
fold f g (Leaf x)      = f x
fold f g (Branch s t) = g (fold f g s) (fold f g t)
-}

concat : ∀ {a} {A : Set a} → NEList A → NEList A → NEList A
concat (x₀ , l₀) (x₁ , l₁) = (x₀ , l₀ ++ (x₁ ∷ l₁))

Free : ∀ o → Functor (Sets o) (SemigroupCat o)
Free o = record
  { F₀ = λ A → MkSG (NEList A) concat {!!}
  ; F₁ = λ f → MkHom (mapNE f) {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ F≡G → {!!}
  }

TreeLeft : ∀ o → Adjunction (Free o) (Forget o)
TreeLeft o = record
  { unit   = record { η = λ _ x → x , [] ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ {(MkSG Carrier _*_ _) → MkHom {!!} {!!}} ; commute = {!!} }
  ; zig = {!!}
  ; zag = {!!} }

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
