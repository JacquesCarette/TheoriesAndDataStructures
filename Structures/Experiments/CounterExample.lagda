\section{CounterExample}

This code used to be part of |Some|.  It shows the reason why |BagEq xs ys |
is not just |{x} → x ∈ xs ≅ x ∈ ys| : This is insufficiently representation
independent.

%{{{ Imports
\begin{code}
module CounterExample where

open import Level renaming (zero to lzero; suc to lsuc) hiding (lift)
open import Relation.Binary    using  (Setoid)
open import Function.Equality  using  (Π; _⟨$⟩_)
open import Data.List          using  (List ; _∷_ ; [])
open import DataProperties     using  (⊥)
open import SetoidEquiv
open import Some
\end{code}
%}}}

%{{{ Definition of _≋₀_ and some kit around it.
\subsection{Preliminaries}
Define a kind of heterogeneous version of |_≋₀_|, and some normal `kit' to go with it.

\restorecolumns
\begin{code}
module HetEquiv {ℓS ℓs : Level} (S : Setoid ℓS ℓs) where
  open Locations
  open Setoid S renaming (trans to _⟨≈≈⟩_)
  open Membership S

  ≋₀-strengthen  : {ys : List Carrier} {y : Carrier} {pf pf' : y ∈₀ ys}
                 →  pf ≋₀ pf' → pf ≋ pf'
  ≋₀-strengthen (hereEq y≈x z≈y y′≈x z′≈y′) = hereEq z≈y z′≈y′ y≈x y′≈x
  ≋₀-strengthen (thereEq eq) = thereEq (≋₀-strengthen eq)

  infix  3 _□₀
  infixr 2 _≋₀⟨_⟩_
  infixr 2 _≋₀˘⟨_⟩_

  _≋₀⟨_⟩_ : {x y z : Carrier} {xs : List Carrier} (X : x ∈₀ xs) {Y : y ∈₀ xs} {Z : z ∈₀ xs}
        →  X ≋₀ Y → Y ≋₀ Z → X ≋₀ Z
  X ≋₀⟨ X≋₀Y ⟩ Y≋₀Z = ≋₀-trans X≋₀Y Y≋₀Z

  _≋₀˘⟨_⟩_ : {x y z : Carrier} {xs : List Carrier} (X : x ∈₀ xs) {Y : y ∈₀ xs} {Z : z ∈₀ xs}
        →  Y ≋₀ X → Y ≋₀ Z → X ≋₀ Z
  X ≋₀˘⟨ Y≋₀X ⟩ Y≋₀Z = ≋₀-trans (≋₀-sym Y≋₀X) Y≋₀Z

  _□₀ : {x : Carrier} {xs : List Carrier} (X : x ∈₀ xs) → X ≋₀ X
  X □₀ = ≋₀-refl

  ∈₀-subst₁-elim′ : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y) (x∈xs : x ∈₀ xs) →
    ∈₀-subst₁ x≈y x∈xs ≋₀ x∈xs
  ∈₀-subst₁-elim′ x≈y (here sm px) = hereEq _ _ _ _
  ∈₀-subst₁-elim′ x≈y (there x∈xs) = thereEq (∈₀-subst₁-elim′ x≈y x∈xs)

  ∈₀-subst₁-cong′ : {x y : Carrier} {xs : List Carrier} (x≈y : x ≈ y)
                  {i j : x ∈₀ xs} → i ≋₀ j → ∈₀-subst₁ x≈y i ≋₀ ∈₀-subst₁ x≈y j
  ∈₀-subst₁-cong′ x≈y (hereEq px qy x≈z y≈z) = hereEq _ _ _ _ -- (sym x≈y ⟨≈≈⟩ px ) (sym x≈y ⟨≈≈⟩ qy) x≈z y≈z
  ∈₀-subst₁-cong′ x≈y (thereEq i≋j) = thereEq (∈₀-subst₁-cong′ x≈y i≋j)
\end{code}
%}}}

%{{{ Trying
\subsection{Unfinished}
\edcomm{WK}{Trying --- unfinished --- |∈₀-subst₁-elim″| would be sufficient for |∈₀-subst₂-cong′| --- commented out:
\restorecolumns
\begin{spec}
  ∈₀-subst₁-elim″ :  {xs ys : List Carrier} (xs≅ys : BagEq xs ys) {x x′ : Carrier} (x≈x′ : x ≈ x′) (x∈xs : x ∈₀ xs) →
      ∈₀-subst₂ xs≅ys (∈₀-subst₁ x≈x′ x∈xs) ≋₀ ∈₀-subst₂ xs≅ys x∈xs
  ∈₀-subst₁-elim″ xs≅ys x≈x′ x∈xs@(here sm px) with ∈₀-subst₁ x≈x′ x∈xs | inspect (∈₀-subst₁ x≈x′) x∈xs
  ∈₀-subst₁-elim″ xs≅ys x≈x′ (here sm px) | here sm₁ px₁ | [ eq ] = {!!}
  ∈₀-subst₁-elim″ xs≅ys x≈x′ (here sm px) | there p | [ () ]
  ∈₀-subst₁-elim″ xs≅ys x≈x′ (there p) = {!!}

  ∈₀-subst₂-cong′  : {x x′ : Carrier} {xs ys : List Carrier} (xs≅ys : BagEq xs ys)
                  → x ≈ x′
                  → {p : x ∈₀ xs} {q : x′ ∈₀ xs}
                  → p ≋₀ q
                  → ∈₀-subst₂ xs≅ys p ≋₀ ∈₀-subst₂ xs≅ys q
  ∈₀-subst₂-cong′ xs≅ys x≈x′ {p} {q} p≋₀q =
      ∈₀-subst₂ xs≅ys p
    ≋₀⟨ {!!} ⟩
      ∈₀-subst₂ xs≅ys (∈₀-subst₁ x≈x′ p)
    ≋₀⟨ ≋→≋₀ (cong (∈₀-Subst₂ xs≅ys)
        (≋₀-strengthen (
             ∈₀-subst₁ x≈x′ p
           ≋₀⟨ ∈₀-subst₁-elim′ x≈x′ p ⟩
             p
           ≋₀⟨ p≋₀q ⟩
             q
           □₀))) ⟩
      ∈₀-subst₂ xs≅ys q
    □₀

  ∈₀-subst₁-to : {a b : Carrier} {zs ws : List Carrier} {a≈b : a ≈ b}
      → (zs≅ws : BagEq zs ws) (a∈zs : a ∈₀ zs)
      → ∈₀-subst₁ a≈b (∈₀-subst₂ zs≅ws a∈zs) ≋ ∈₀-subst₂ zs≅ws (∈₀-subst₁ a≈b a∈zs)
  ∈₀-subst₁-to {a} {b} {zs} {ws} {a≈b} zs≅ws a∈zs =
    ≋₀-strengthen (
      ∈₀-subst₁ a≈b (∈₀-subst₂ zs≅ws a∈zs)
    ≋₀⟨ ∈₀-subst₁-elim′ a≈b (∈₀-subst₂ zs≅ws a∈zs) ⟩
      ∈₀-subst₂ zs≅ws a∈zs
    ≋₀˘⟨ ∈₀-subst₂-cong′ zs≅ws (sym a≈b) (∈₀-subst₁-elim′ a≈b a∈zs) ⟩
      ∈₀-subst₂ zs≅ws (∈₀-subst₁ a≈b a∈zs)
    □₀)
\end{spec}
}%edcomm
%}}}

%{{{ |module NICE|: |∈₀-subst₂-cong′| and |∈₀-subst₁-to| do not hold
\subsection{module NICE}
|∈₀-subst₂-cong′| and |∈₀-subst₁-to| actually do not hold ---
the following module serves to provide a counterexample:

\begin{code}
module NICE where
  data E : Set where
    E₁ E₂ E₃ : E

  data _≈E_ : E → E → Set where
    ≈E-refl : {x : E} → x ≈E x
    E₁₂ : E₁ ≈E E₂
    E₂₁ : E₂ ≈E E₁

  ≈E-sym : {x y : E} → x ≈E y → y ≈E x
  ≈E-sym ≈E-refl = ≈E-refl
  ≈E-sym E₁₂ = E₂₁
  ≈E-sym E₂₁ = E₁₂

  ≈E-trans : {x y z : E} → x ≈E y → y ≈E z → x ≈E z
  ≈E-trans ≈E-refl ≈E-refl = ≈E-refl
  ≈E-trans ≈E-refl E₁₂ = E₁₂
  ≈E-trans ≈E-refl E₂₁ = E₂₁
  ≈E-trans E₁₂ ≈E-refl = E₁₂
  ≈E-trans E₁₂ E₂₁ = ≈E-refl
  ≈E-trans E₂₁ ≈E-refl = E₂₁
  ≈E-trans E₂₁ E₁₂ = ≈E-refl

  E-setoid : Setoid lzero lzero
  E-setoid = record
    { Carrier = E
    ; _≈_ = _≈E_
    ; isEquivalence = record
      { refl = ≈E-refl
      ; sym = ≈E-sym
      ; trans = ≈E-trans
      }
    }

  xs ys : List E
  xs = E₁ ∷ E₁ ∷ E₃ ∷ []
  ys = E₃ ∷ E₁ ∷ E₁ ∷ []

  open Membership E-setoid
  open HetEquiv E-setoid
  open Locations

  xs⇒ys : (x : E) → x ∈₀ xs → x ∈₀ ys
  xs⇒ys E₁ (here sm px) = there (here sm px)
  xs⇒ys E₁ (there p) = there (there (here ≈E-refl ≈E-refl))
  xs⇒ys E₂ (here sm px) = there (there (here sm px))
  xs⇒ys E₂ (there p) = there (here ≈E-refl E₂₁)
  xs⇒ys E₃ p = here ≈E-refl ≈E-refl

  xs⇒ys-cong : (x : E) {p p′ : x ∈₀ xs} → p ≋ p′ → xs⇒ys x p ≋ xs⇒ys x p′
  xs⇒ys-cong E₁ (hereEq px qy x≈z y≈z) = thereEq (hereEq _ _ _ _)
  xs⇒ys-cong E₁ (thereEq e) = thereEq (thereEq (hereEq _ _ _ _))
  xs⇒ys-cong E₂ (hereEq px qy x≈z y≈z) = thereEq (thereEq (hereEq _ _ _ _))
  xs⇒ys-cong E₂ (thereEq e) = thereEq (hereEq _ _ _ _)
  xs⇒ys-cong E₃ e = hereEq _ _ _ _

  ys⇒xs : (x : E) → x ∈₀ ys → x ∈₀ xs
  ys⇒xs E₁ (here ≈E-refl ())
  ys⇒xs E₁ (there (here sm px)) = here sm px
  ys⇒xs E₁ (there (there e)) = there (here ≈E-refl ≈E-refl)
  ys⇒xs E₂ (here ≈E-refl ())
  ys⇒xs E₂ (there (here sm px)) = there (here E₂₁ ≈E-refl)
  ys⇒xs E₂ (there (there e)) = here ≈E-refl E₂₁
  ys⇒xs E₃ e = there (there (here ≈E-refl ≈E-refl))

  ys⇒xs-cong : (x : E) {p p′ : x ∈₀ ys} → p ≋ p′ → ys⇒xs x p ≋ ys⇒xs x p′
  ys⇒xs-cong E₁ (hereEq ≈E-refl ≈E-refl x≈z ())
  ys⇒xs-cong E₁ (hereEq ≈E-refl E₁₂ x≈z ())
  ys⇒xs-cong E₁ (hereEq E₁₂ ≈E-refl x≈z ())
  ys⇒xs-cong E₁ (hereEq E₁₂ E₁₂ x≈z ())
  ys⇒xs-cong E₁ (thereEq (hereEq px qy x≈z y≈z)) = hereEq px qy x≈z y≈z
  ys⇒xs-cong E₁ (thereEq (thereEq eq)) = thereEq (hereEq _ _ _ _)
  ys⇒xs-cong E₂ (hereEq ≈E-refl ≈E-refl x≈z ())
  ys⇒xs-cong E₂ (hereEq ≈E-refl E₂₁ x≈z ())
  ys⇒xs-cong E₂ (hereEq E₂₁ ≈E-refl x≈z ())
  ys⇒xs-cong E₂ (hereEq E₂₁ E₂₁ x≈z ())
  ys⇒xs-cong E₂ (thereEq (hereEq px qy x≈z y≈z)) = thereEq (hereEq _ _ _ _)
  ys⇒xs-cong E₂ (thereEq (thereEq eq)) = hereEq _ _ _ _
  ys⇒xs-cong E₃ _ = thereEq (thereEq (hereEq _ _ _ _))

  leftInv : (e : E) (p : e ∈₀ xs) → ys⇒xs e (xs⇒ys e p) ≋ p
  leftInv E₁ (here sm px) = hereEq px px sm sm
  leftInv E₁ (there (here sm px)) = thereEq (hereEq ≈E-refl px ≈E-refl sm)
  leftInv E₁ (there (there (here ≈E-refl ())))
  leftInv E₁ (there (there (there ())))
  leftInv E₂ (here sm px) = hereEq E₂₁ px ≈E-refl sm
  leftInv E₂ (there (here sm px)) = thereEq (hereEq ≈E-refl px E₂₁ sm)
  leftInv E₂ (there (there (here ≈E-refl ())))
  leftInv E₂ (there (there (there ())))
  leftInv E₃ (here ≈E-refl ())
  leftInv E₃ (here E₂₁ ())
  leftInv E₃ (there (here ≈E-refl ()))
  leftInv E₃ (there (here E₂₁ ()))
  leftInv E₃ (there (there (here sm px))) = thereEq (thereEq (hereEq ≈E-refl px ≈E-refl sm))
  leftInv E₃ (there (there (there ())))

  rightInv : (e : E) (p : e ∈₀ ys) → xs⇒ys e (ys⇒xs e p) ≋ p
  rightInv E₁ (here ≈E-refl ())
  rightInv E₁ (there (here sm px)) = thereEq (hereEq px px sm sm)
  rightInv E₁ (there (there (here sm px))) = thereEq (thereEq (hereEq ≈E-refl px ≈E-refl sm))
  rightInv E₁ (there (there (there ())))
  rightInv E₂ (here ≈E-refl ())
  rightInv E₂ (there (here sm px)) = thereEq (hereEq E₂₁ px ≈E-refl sm)
  rightInv E₂ (there (there (here sm px))) = thereEq (thereEq (hereEq E₂₁ px ≈E-refl sm))
  rightInv E₂ (there (there (there ())))
  rightInv E₃ (here sm px) = hereEq ≈E-refl px ≈E-refl sm
  rightInv E₃ (there (here ≈E-refl ()))
  rightInv E₃ (there (here E₂₁ ()))
  rightInv E₃ (there (there (here ≈E-refl ())))
  rightInv E₃ (there (there (here E₂₁ ())))
  rightInv E₃ (there (there (there ())))

  OldBagEq : (xs ys : List E) → Set
  OldBagEq xs ys = {x : E} → (x ∈ xs) ≅ (x ∈ ys)

  xs≊ys : OldBagEq xs ys
  xs≊ys {e} = record
    { to = record { _⟨$⟩_ = xs⇒ys e ; cong = xs⇒ys-cong e }
    ; from = record { _⟨$⟩_ = ys⇒xs e ; cong = ys⇒xs-cong e }
    ; inverse-of = record
      { left-inverse-of = leftInv e
      ; right-inverse-of = rightInv e
      }
    }

  ¬-∈₀-subst₂-cong′  : ({x x′ : E} {xs ys : List E} (xs≅ys : OldBagEq xs ys)
                  → x ≈E x′
                  → {p : x ∈₀ xs} {q : x′ ∈₀ xs}
                  → p ≋₀ q
                  → _≅_.to xs≅ys ⟨$⟩ p ≋₀ _≅_.to xs≅ys ⟨$⟩ q) → ⊥ {lzero}
  ¬-∈₀-subst₂-cong′ ∈₀-subst₂-cong′ with
    ∈₀-subst₂-cong′ {E₁} {E₂} {xs} {ys} xs≊ys E₁₂ {here {a = E₁} ≈E-refl ≈E-refl} {here {a = E₂} E₂₁ ≈E-refl} (hereEq _ _ _ _)
  ¬-∈₀-subst₂-cong′ ∈₀-subst₂-cong′ | thereEq ()

  ¬-∈₀-subst₁-to : ({a b : E} {zs ws : List E} {a≈b : a ≈E b}
      → (zs≅ws : OldBagEq zs ws) (a∈zs : a ∈₀ zs)
      → ∈₀-subst₁ a≈b (_≅_.to zs≅ws ⟨$⟩ a∈zs) ≋ _≅_.to zs≅ws ⟨$⟩ (∈₀-subst₁ a≈b a∈zs)
      ) → ⊥ {lzero}
  ¬-∈₀-subst₁-to ∈₀-subst₁-to with
    ∈₀-subst₁-to {E₁} {E₂} {xs} {ys} {E₁₂} xs≊ys (here {a = E₁} ≈E-refl ≈E-refl)
  ¬-∈₀-subst₁-to ∈₀-subst₁-to | thereEq ()
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
