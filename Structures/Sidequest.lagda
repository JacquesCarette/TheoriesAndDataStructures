\section{Structures.Sidequest}

%{{{ Imports
\begin{code}
module Structures.Sidequest where

open import Level renaming (zero to lzero; suc to lsuc ; _⊔_ to _⊍_) hiding (lift)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

-- open import Categories.Category   using (Category)
open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Setoids)

open import Function.Equality using (Π ; _⟶_ ; id ; _∘_)

open import DataProperties hiding (⟨_,_⟩)
open import ParComp
open import EqualityCombinators
open import Belongs
open import Structures.CommMonoid renaming (Hom to CMArrow)

open import Data.List using (monoid)

open Π          using () renaming (_⟨$⟩_ to _⟨$⟩₀_)
open CMArrow    using (_⟨$⟩_ ; mor ; pres-e ; pres-*)
-- open CommMonoid using (eq-in ; isCommMonoid)
\end{code}
%}}}

%{{{ approach via vectors rather than lists

\begin{code}
module Lemmas {l c : Level} {𝒮 : Setoid c l} {𝒞 : CommMonoid 𝒮} where

  open CommMonoid 𝒞
  open IsCommutativeMonoid isCommMonoid -- \edcomm{MA}{The field name really oughtn't be abbreviated!}

  open import Data.Vec
  open import Data.Nat hiding (fold ; _*_)
  open import Data.Fin hiding (_+_ ; fold)

  -- Sequences
  open Setoid 𝒮
  Seq = Vec Carrier

  -- `k`omponent-wise equality on sequences ;; MA: Subscript `c` not directly available.
  data _≈ₖ_ : {n : ℕ} → Seq n → Seq n → Set (c ⊍ l) where
    nil  : [] ≈ₖ []
    cons : {x y : Carrier} {n : ℕ} {xs ys : Seq n} → x ≈ y → xs ≈ₖ ys → (x ∷ xs) ≈ₖ (y ∷ ys)

  -- MA: It is a simple matter to show that this is an equivalence relation. TODO.
  
  -- fold is a setoid homomorphism

  fold : {n : ℕ} → Seq n → Carrier
  fold = foldr (λ _ → Carrier) _*_ e

  fold-cong : {n : ℕ} {xs ys : Seq n} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong {_} {[]} {.[]} nil = refl
  fold-cong {_} {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = x≈y ⟨∙⟩ fold-cong xs≈ys
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

  -- from copumkin's library
  
  data Permutation : ℕ → Set where
    nil  : Permutation 0
    cons : {n : ℕ} → (p : Fin (1 + n)) → (ps : Permutation n) → Permutation (1 + n)

  insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
  insert xs zero a = a ∷ xs
  insert [] (suc ()) a
  insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

  permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
  permute nil [] = []
  permute (cons p ps) (x ∷ xs) = insert (permute ps xs) p x

  data _≈ᵥ_ {n : ℕ} (xs : Seq n) (ys : Seq n) : Set (c ⊍ l) where
    yes : (p : Permutation n) → permute p xs ≈ₖ ys → xs ≈ᵥ ys

  open import Relation.Binary.SetoidReasoning

  -- commutativity here!
  proposition₄ : {n : ℕ} {zs : Seq n} {x y : Carrier}
               → fold (x ∷ y ∷ zs) ≈ fold (y ∷ x ∷ zs)
  proposition₄ {n} {zs} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ zs)
    ≈˘⟨ assoc _ _ _ ⟩
      (x * y) * fold zs
    ≈⟨ comm _ _ ⟨∙⟩ refl ⟩
      (y * x) * fold zs
    ≈⟨ assoc _ _ _ ⟩
      fold (y ∷ x ∷ zs)
    ∎

  proposition₃ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x y : Carrier}
               → fold (x ∷ y ∷ xs) ≈ fold (y ∷ insert xs i x)
  proposition₃ {.0} {[]} {zero} =  proposition₄ 
  proposition₃ {.0} {[]} {suc ()}
  proposition₃ {.(suc _)} {x ∷ xs} {zero} = proposition₄ 
  proposition₃ {.(suc _)} {hd ∷ xs} {suc i} {x} {y} = begin⟨ 𝒮 ⟩
      fold (x ∷ y ∷ hd ∷ xs)
    ≈⟨ proposition₄ ⟩
      fold (y ∷ x ∷ hd ∷ xs)
    ≡⟨ ≡.refl ⟩
      y * fold (x ∷ hd ∷ xs)
    ≈⟨ refl ⟨∙⟩ proposition₃ ⟩
      y * fold (hd ∷ insert xs i x)
    ≡⟨ ≡.refl ⟩
      fold (y ∷ hd ∷ insert xs i x)
    ∎
  
  proposition₂ : {n : ℕ} {xs : Seq n} {i : Fin (suc n)} {x : Carrier}
               → fold (x ∷ xs) ≈ fold (insert xs i x)
  proposition₂ {.0} {[]} {zero} = refl
  proposition₂ {.0} {[]} {suc ()}
  proposition₂ {.(suc _)} {y ∷ xs} {zero} = refl
  proposition₂ {.(suc _)} {y ∷ xs} {suc i} = proposition₃

  open import Relation.Binary.PropositionalEquality using (inspect; [_])

  proposition₁ : {n : ℕ} {xs : Seq n} {p : Permutation n} → fold xs ≈ fold (permute p xs) 
  proposition₁ {.0} {[]} {nil} = refl
  proposition₁ {.(suc _)} {x ∷ xs} {cons zero ps} = refl ⟨∙⟩ proposition₁
  proposition₁ {.(suc _)} {x ∷ xs} {cons (suc p) ps} with permute ps xs | inspect (permute ps) xs
  proposition₁ {.(suc 0)} {x ∷ xs} {cons (suc ()) ps} | [] | _
  proposition₁ {.(suc (suc _))} {x ∷ xs} {cons (suc p) ps} | x′ ∷ xs′ | [ ps-on-xs≈xs′ ] = begin⟨ 𝒮 ⟩
      x * fold xs
    ≈⟨ refl ⟨∙⟩ proposition₁ ⟩
      x * fold (permute ps xs)
    ≡⟨ ≡.cong (λ zs → x * fold zs) ps-on-xs≈xs′ ⟩
      x * fold (x′ ∷ xs′)
    ≡⟨ ≡.refl ⟩
      fold (x ∷ x′ ∷ xs′)
    ≈⟨ proposition₄ ⟩
      fold (x′ ∷ x ∷ xs′)
    ≡⟨ ≡.refl ⟩
      x′ * fold (x ∷ xs′)
    ≈⟨ refl ⟨∙⟩ proposition₂ ⟩
      x′ * fold (insert xs′ p x)
    ∎

  -- This is essentially |Multiset.fold-permute|, the pesky-hole from the summer.
  proposition₀ : {n : ℕ} {xs ys : Seq n} → xs ≈ᵥ ys → fold xs ≈ fold ys 
  proposition₀ (yes p p-on-xs≈ys) = trans proposition₁ (fold-cong p-on-xs≈ys)
\end{code}  
%}}}


%{{{ attempting to connect the above with work in BagEq
\begin{spec}
  open BagEq 𝒮
  _≈ᵥᵥ_ : {n : ℕ} → Seq n → Seq n → Set (c ⊍ l)
  _≈ᵥᵥ_ = λ xs ys → toList xs ⇔ toList ys

  open Locations 𝒮
  -- no.
  bridge₁ : {n : ℕ} {xs ys : Seq n} {a b : Carrier} → (a ∷ xs) ≈ᵥᵥ (b ∷ ys) → a ≈ b ⊎ a ∈₀ toList ys
  bridge₁ {.0} {[]} {[]} eq = {!!}
  bridge₁ {.(suc _)} {x ∷ xs} {x₁ ∷ ys} eq = {!!}

  bridge : {n : ℕ} {xs ys : Seq n} → xs ≈ᵥᵥ ys → xs ≈ᵥ ys
  bridge {.0} {[]} {[]} eq = yes nil nil
  bridge {.(suc _)} {x ∷ xs} {y ∷ ys} eq = {!This may require decidable equality on elements.!}
\end{spec}
%}}}

%{{{ Ignore: Lists approach requires some transformations between with Fin's
\begin{spec}
open import Algebra   using (CommutativeMonoid)
module Lemmas′ {l c : Level} {𝒞 : CommutativeMonoid c l} where

  open CommutativeMonoid 𝒞
  open import Relation.Binary.SetoidReasoning -- renaming (_∎ to _■)

  open import Data.List     using (List; []; _++_; _∷_; foldr; length)  renaming (map to mapL)
  open import Data.List.Properties using (map-++-commute; map-id; map-compose)

  open import Data.Nat hiding (fold)
  open import Data.Fin hiding (_+_ ; fold)

  -- Sequences
  Seq = List Carrier

  -- `k`omponent-wise equality on sequences ;; MA: Subscript `c` not directly available.
  data _≈ₖ_ : Seq → Seq → Set (c ⊍ l) where
    nil  : [] ≈ₖ []
    cons : {x y : Carrier} {xs ys : Seq} → x ≈ y → xs ≈ₖ ys → (x ∷ xs) ≈ₖ (y ∷ ys)

  -- MA: It is a simple matter to show that this is an equivalence relation. TODO.
  
  -- fold is a setoid homomorphism

  fold : Seq → Carrier
  fold = foldr _∙_ ε

  fold-cong : {xs ys : Seq} → xs ≈ₖ ys → fold xs ≈ fold ys
  fold-cong {[]} {.[]} nil = refl
  fold-cong {x ∷ xs} {y ∷ ys} (cons x≈y xs≈ys) = begin⟨ setoid ⟩
      fold (x ∷ xs)
    ≡⟨ ≡.refl ⟩
      x ∙ fold xs
    ≈⟨ ∙-cong x≈y (fold-cong xs≈ys) ⟩
      y ∙ fold ys
    ≡⟨ ≡.refl ⟩
      fold (y ∷ ys)
    ∎
  -- commutativity is not used here and so this result is valid for non-commutative monoids as well.

  -- from copumkin's library
  data Permutation : ℕ → Set where
    nil  : Permutation 0
    cons : {n : ℕ} (p : Fin (1 + n)) (ps : Permutation n) → Permutation (1 + n)

  -- insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
  insert : (xs : Seq) → Fin (1 + length xs) → Carrier → Seq
  insert xs zero a = a ∷ xs
  insert [] (suc ()) a
  insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

  -- permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
  mutual
  
    permute : (xs : Seq) → Permutation (length xs) → Seq
    permute [] nil = []
    permute (x ∷ xs) (cons p ps)  = insert (permute xs ps) (cast p) x
    --
    -- Note that we switch the order as compared to copumkin since we're using lists.

    cast : {xs : Seq} {p : Permutation (length xs)}
         → Fin (1 + length xs) → Fin (1 + length (permute xs p))
    cast {[]} {nil} i = i
    cast {x ∷ xs} {cons p p₁} zero = zero
    cast {x ∷ xs} {cons p p₁} (suc i) = {!!} -- suc (insert-cast {!!}) -- (insert-cast {!!})

    insert-cast : {xs : Seq} {i : Fin (1 + length xs)} {x : Carrier}
                  {ps : Permutation (length xs)}
              → Fin (length xs) → Fin (length (insert (permute xs ps) (cast i) x))
    insert-cast = {!!}
\end{spec}
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
