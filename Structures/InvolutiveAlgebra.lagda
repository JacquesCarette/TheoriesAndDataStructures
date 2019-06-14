\section{Involutive Algebras: Sum and Product Types}

Free and cofree constructions wrt these algebras ``naturally'' give rise to
the notion of single-variable sum and product types.

%{{{ Imports
\begin{code}
module Structures.InvolutiveAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function

open import Helpers.Categorical
open import Helpers.Function2    using (_$ᵢ)
open import Helpers.DataProperties
open import Helpers.EqualityCombinators
\end{code}
%}}}

%{{{ Inv and Hom
\subsection{Definition}
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
    mor       :  Carrier X → Carrier Y
    pres      :  (x : Carrier X) → mor (x ᵒ) ≡ (mor x) ᴼ

open Hom
\end{code}
%}}}

%{{{ Involutives and foregtful functor U
\subsection{Category and Forgetful Functor}

\edcomm{MA}{can regain via onesortedalgebra construction}

\begin{code}
Involutives : (ℓ : Level) → Category _ ℓ ℓ
Involutives ℓ = record
   { Obj         =   Inv
   ; _⇒_         =   Hom
   ; _≡_         =   λ F G → mor F ≐ mor G
   ; id          =   record { mor = id ; pres = ≐-refl }
   ; _∘_         =   λ F G → record
     { mor       =   mor F ∘ mor G
     ; pres      =   λ a → ≡.cong (mor F) (pres G a) ⟨≡≡⟩ pres F (mor G a)
     }
   ; assoc       =   ≐-refl
   ; identityˡ   =   ≐-refl
   ; identityʳ   =   ≐-refl
   ; equiv       =   record { IsEquivalence ≐-isEquivalence }
   ; ∘-resp-≡    =   ∘-resp-≐
   }
   where open Hom ; open import Relation.Binary using (IsEquivalence)

Forget : (o : Level) → Functor (Involutives o) (Sets o)
Forget  _ = record
  { F₀            =   Carrier
  ; F₁            =   mor
  ; identity      =   ≡.refl
  ; homomorphism  =   ≡.refl
  ; F-resp-≡     =   _$ᵢ
  }
\end{code}
%}}}

%{{{ Left and AdjLeft
\subsection{Free Adjunction: Part 1 of a toolkit}

The double of a type has an involution on it by swapping the tags:

\begin{code}
swap₊ : {ℓ : Level} {X : Set ℓ} → X ⊎ X → X ⊎ X
swap₊ = [ inj₂ , inj₁ ]

swap² : {ℓ : Level} {X : Set ℓ} → swap₊ ∘ swap₊ ≐ id {A = X ⊎ X}
swap² = [ ≐-refl , ≐-refl ]
\end{code}

\begin{code}
2×_ : {ℓ : Level} {X Y : Set ℓ}
    → (X →  Y)
    → X ⊎ X → Y ⊎ Y
2× f = f ⊎₁ f

2×-over-swap : {ℓ : Level} {X Y : Set ℓ} {f : X → Y}
             → 2× f ∘ swap₊ ≐ swap₊ ∘ 2× f
2×-over-swap = [ ≐-refl , ≐-refl ]

2×-id≈id : {ℓ : Level} {X : Set ℓ} → 2× id ≐ id {A = X ⊎ X}
2×-id≈id = [ ≐-refl , ≐-refl ]

2×-∘ : {ℓ : Level} {X Y Z : Set ℓ} {f : X → Y} {g : Y → Z}
       → 2× (g ∘ f) ≐ 2× g ∘ 2× f
2×-∘ = [ ≐-refl , ≐-refl ]

2×-cong : {ℓ : Level} {X Y : Set ℓ} {f g : X → Y}
        → f ≐ᵢ g
        → 2× f ≐ 2× g
2×-cong F≈G = [ (λ _ → ≡.cong inj₁ F≈G) , (λ _ → ≡.cong inj₂ F≈G) ]

Left : (ℓ : Level) → Functor (Sets ℓ) (Involutives ℓ)
Left ℓ = record
  { F₀             =   λ A → record { A = A ⊎ A ; _ᵒ = swap₊ ; involutive = swap² }
  ; F₁             =   λ f → record { mor = 2× f ; pres = 2×-over-swap }
  ; identity       =   2×-id≈id
  ; homomorphism   =   2×-∘
  ; F-resp-≡       =   2×-cong
  }
\end{code}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item |2×|: usually functions can be packaged-up to work on syntax of unary algebras.
\item |2×-id≈id|: the identity function leaves syntax alone; or: |map id| can be replaced with a constant
  time algorithm, namely, |id|.
\item |2×-∘|: sequential substitutions on syntax can be efficiently replaced with a single substitution.
\item |2×-cong|: observably indistinguishable substitutions can be used in place of one another, similar to the
      transparency principle of Haskell programs.
\item |2×-over-swap|: \unfinished
\item |swap₊|: \unfinished
\item |swap²|: \unfinished
\item  \unfinished
\end{itemize}

There are actually two left adjoints.  It seems the choice of |inj₁ / inj₂| is free.
But that choice does force the order of |id _ᵒ| in map⊎ (else zag does not hold).

\begin{code}
AdjLeft : (ℓ : Level) → Adjunction (Left ℓ) (Forget ℓ)
AdjLeft ℓ = record
  { unit   = record { η = λ _ → inj₁ ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ A  → record
          { mor      =  [ id , inv A ]                        -- |≡  from⊎ ∘ map⊎ idF _ᵒ|
          ; pres  =  [ ≐-refl , ≡.sym ∘ involutive A ]
          }
    ; commute = λ F → [ ≐-refl , ≡.sym ∘ pres F ]
    }
  ; zig = [ ≐-refl , ≐-refl ]
  ; zag = ≡.refl
  }

-- but there's another!
AdjLeft₂ : (ℓ : Level) → Adjunction (Left ℓ) (Forget ℓ)
AdjLeft₂ ℓ = record
  { unit = record { η = λ _ → inj₂ ; commute = λ _ → ≡.refl }
  ; counit = record
    { η = λ A → record
          { mor     = [ inv A , id ]                          -- |≡  from⊎ ∘ map⊎ _ᵒ idF |
          ; pres = [ ≡.sym ∘ involutive A , ≐-refl ]
          }
    ; commute = λ F → [ ≡.sym ∘ pres F , ≐-refl ]
    }
  ; zig = [ ≐-refl , ≐-refl ]
  ; zag = ≡.refl
  }
\end{code}

\edcomm{MA}{ToDo :: extract functions out of adjunction proofs!}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item  \unfinished
\end{itemize}

%}}}

%{{{ Right, diag, AdjRight
\subsection{CoFree Adjunction}

\begin{code}
-- for the proofs below, we "cheat" and let |η| for records make things easy.
Right : (ℓ : Level) → Functor (Sets ℓ) (Involutives ℓ)
Right ℓ = record
  { F₀ = λ B → record { A = B × B ; _ᵒ = swap ; involutive = ≐-refl }
  ; F₁ = λ g → record { mor = g ×₁ g ; pres = ≐-refl }
  ; identity      =  ≐-refl
  ; homomorphism  =  ≐-refl
  ; F-resp-≡     =  λ F≡G a → ≡.cong₂ _,_ (F≡G {proj₁ a}) F≡G
  }

AdjRight : (ℓ : Level) → Adjunction (Forget ℓ) (Right ℓ)
AdjRight ℓ = record
  { unit = record
    { η = λ A → record
      { mor     =  ⟨ id , inv A ⟩
      ; pres    =  ≡.cong₂ _,_ ≡.refl ∘ involutive A
      }
    ; commute = λ f → ≡.cong₂ _,_ ≡.refl ∘ ≡.sym ∘ pres f
    }
  ; counit   =   record { η = λ _ → proj₁ ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl
  }

-- MA: and here's another ;)
AdjRight₂ : (ℓ : Level) → Adjunction (Forget ℓ) (Right ℓ)
AdjRight₂ ℓ = record
  { unit = record
    { η = λ A → record
      { mor      =  ⟨ inv A , id ⟩
      ; pres  =  flip (≡.cong₂ _,_) ≡.refl ∘ involutive A
      }
    ; commute = λ f → flip (≡.cong₂ _,_) ≡.refl ∘ ≡.sym ∘ pres f
    }
  ; counit   =   record { η = λ _ → proj₂ ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl
  }
\end{code}

Note that we have TWO proofs for AdjRight since we can construe |A×A| as
|{ (a , aᵒ) ∣ a ∈ A}| or as |{(aᵒ , a) ∣ a ∈ A}| ---similarly for why
we have two AdjLeft proofs.

\edcomm{MA}{ToDo :: extract functions out of adjunction proofs!}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item  \unfinished
\end{itemize}

%}}}

%{{{ Monad constructions
\subsection{Monad constructions}
\begin{code}
SetMonad : {o : Level} → Monad (Sets o)
SetMonad {o} = Adjunction.monad (AdjLeft o)

InvComonad : {o : Level} → Comonad (Involutives o)
InvComonad {o} = Adjunction.comonad (AdjLeft o)
\end{code}

\edcomm{MA}{Prove that free functors are faithful, see Semigroup, and mention monad constructions elsewhere?}
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
