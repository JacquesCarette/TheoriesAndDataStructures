\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\section{UnaryAlgebra}

Unary algebras are tantamount to an OOP interface with a single operation.
The associated free structure captures the ``syntax'' of such interfaces, say, for the sake
of delayed evaluation in a particular interface implementation.

This example algebra serves to set-up the approach we take in more involved settings.

\edcomm{MA}{This section requires massive reorganisation.}

%{{{ Imports
\begin{code}
module Structures.UnaryAlgebra where

open import Level renaming (suc to lsuc; zero to lzero)
open import Function
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; suc ; zero)

open import Helpers.Categorical
open import Helpers.Function2
open import Helpers.Forget
open import Helpers.DataProperties
open import Helpers.EqualityCombinators
\end{code}
%}}}

%{{{ \subsection{Definition} Unary ; Hom
\subsection{Definition}
A single-sorted |Unary| algebra consists of a type along with a function on that type.
For example, the naturals and addition-by-1 or lists and the reverse operation.

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
    pres-op    :  mor ∘ Op X  ≐ᵢ  Op Y ∘ mor

open Hom
\end{code}
%}}}

%{{{ \subsection{Category and Forgetful Functor} UnaryAlg ; UnaryCat ; Forget
\subsection{Category and Forgetful Functor}

Along with functions that preserve the elected operation, such algberas form a category.

\begin{code}
UnaryAlg : {ℓ : Level} → OneSortedAlg ℓ
UnaryAlg = record
  { Alg       = Unary
  ; Carrier   = Carrier
  ; Hom       = Hom
  ; mor       = mor
  ; comp      = λ F G → record
    { mor     =  mor F ∘ mor G
    ; pres-op =  ≡.cong (mor F) (pres-op G) ⟨≡≡⟩ pres-op F
    }
  ; comp-is-∘ =  ≐-refl
  ; Id        =  MkHom id ≡.refl
  ; Id-is-id  =  ≐-refl
  }

Unarys : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
Unarys ℓ = oneSortedCategory ℓ UnaryAlg

Forget : (ℓ : Level) → Functor (Unarys ℓ) (Sets ℓ)
Forget ℓ = mkForgetful ℓ UnaryAlg
\end{code}

%}}}

%{{{ \subsection{Free Structure} Eventually ; ⟦_,_⟧ ; indE
\subsection{Free Structure}
We now turn to finding a free unary algebra.

Indeed, we do so by simply not ``interpreting'' the single function symbol that is required
as part of the definition. That is, we form the ``term algebra'' over the signature for
unary algebras.

\begin{code}
data Eventually {ℓ} (A : Set ℓ) : Set ℓ where
  base   :              A → Eventually A
  step   :   Eventually A → Eventually A
\end{code}
The elements of this type are of the form |stepⁿ (base a)| for |a : A|.
This leads to an alternative presentation, |Eventually A   ≅   Σ n ∶ ℕ • A|
viz |stepⁿ (base a) ↔ (n , a)| ---cf |Free²| below.
Incidentally, or promisingly, |Eventually ⊤ ≅ ℕ|.

For |(n , a)|, the tag |n| may be interpreted as “the delay time” before the value |a| is obtained.
Alternatively, it can be interpreted to be the number of times that method |a| is to be executed.
Finally, these can be thought of as constant lists with value |a| of length |n| ;-)

\begin{code}
delay : ∀ {ℓ} {A : Set ℓ} → ℕ → A → Eventually A
delay zero    = base
delay (suc n) = step ∘ delay n
\end{code}

We will realise this claim later on. For now, we turn to the dependent-eliminator/induction/recursion principle:
\begin{code}
elim : {ℓ a : Level} {A : Set a} {P : Eventually A → Set ℓ}
     → ({x : A} → P (base x))
     → ({sofar : Eventually A} → P sofar → P (step sofar))
     → (ev : Eventually A) → P ev
elim b s (base x) = b {x}
elim {P = P} b s (step e) = s {e} (elim {P = P} b s e)
\end{code}

Given an unary algebra |(B, 𝒷, 𝓈)| we can interpret the terms of |Eventually A|
where the injection |base| is reified by |𝒷| and the unary operation |step| is
reified by |𝓈|.

\begin{code}
open import Function using (const)
⟦_,_⟧ : {a b : Level} {A : Set a} {B : Set b} (𝒷 : A → B) (𝓈 : B → B) → Eventually A → B
⟦ 𝒷 , 𝓈 ⟧ = elim (λ {a} → 𝒷 a) 𝓈
\end{code}

Notice that: The number of |𝓈|teps is preserved, |⟦ 𝒷 , 𝓈 ⟧ ∘ stepⁿ ≐ 𝓈ⁿ ∘ ⟦ 𝒷 , 𝓈 ⟧|.
Essentially, |⟦ 𝒷 , 𝓈 ⟧ (stepⁿ base x) ≈ 𝓈ⁿ 𝒷 x|. A similar general remark applies to |elim|.

\begin{code}
reflection : {a : Level} {A : Set a} → ⟦ base , step ⟧ ≐ id {A = Eventually A}
reflection = elim ≡.refl (≡.cong step)
\end{code}
%}}}

%{{{ mapeE ; ⟦⟧-naturality
Eventually is clearly a functor,

\begin{code}
map : {a b : Level} {A : Set a} {B : Set b} → (A → B) → (Eventually A → Eventually B)
map f = ⟦ base ∘ f , step ⟧

map-computation : {a b : Level} {A : Set a} {B : Set b} {f : A → B} {e : Eventually A}
                → map f (step e) ≡ step (map f e)
map-computation = ≡.refl
\end{code}

Whence the folding operation is natural,

\begin{code}
⟦⟧-naturality : {a b : Level} {A : Set a} {B : Set b}
              → {𝒷′ 𝓈′ : A → A} {𝒷 𝓈 : B → B} {f : A → B}
              → (basis : 𝒷 ∘ f ≐ᵢ f ∘ 𝒷′)
              → (next  : 𝓈 ∘ f ≐ᵢ f ∘ 𝓈′)
              → ⟦ 𝒷 , 𝓈 ⟧ ∘ map f ≐ f ∘ ⟦ 𝒷′ , 𝓈′ ⟧
⟦⟧-naturality {𝓈 = 𝓈} basis next = elim basis (λ ind → ≡.cong 𝓈 ind ⟨≡≡⟩ next)
\end{code}
%}}}

%{{{ fromE ; iterateE ; iterateE-nat

Other instances of the fold include:

\begin{code}
{- “force” -}
extract : ∀{ℓ} {A : Set ℓ} → Eventually A → A
extract = ⟦ id , id ⟧ -- cf |from⊎| ;)
\end{code}

More generally,
\begin{code}
iterate : ∀ {ℓ} {A : Set ℓ} (f : A → A) → Eventually A → A
iterate  f = ⟦ id , f ⟧
--
-- that is, |iterateE f (stepⁿ base x) ≈ fⁿ x|

iterate-nat : {ℓ : Level} {X Y : Unary {ℓ}} (F : Hom X Y)
              → iterate (Op Y) ∘ map (mor F) ≐ mor F ∘ iterate (Op X)
iterate-nat F = ⟦⟧-naturality {f = mor F} ≡.refl (≡.sym (pres-op F))
\end{code}

%}}}

%{{{ iterateE-mapeE-id , mapE-id , mapE-∘ , mapE-cong

The induction rule yields identical looking proofs for clearly distinct results:

\begin{code}
iterate-map-id : {ℓ : Level} {X : Set ℓ} → id {A = Eventually X} ≐ iterate step ∘ map base
iterate-map-id = elim ≡.refl (≡.cong step)

map-id : {a : Level}  {A : Set a} → map (id {A = A}) ≐ id
map-id = elim ≡.refl (≡.cong step)

map-∘ : {ℓ : Level} {X Y Z : Set ℓ} {f : X → Y} {g : Y → Z}
        →  map (g ∘ f) ≐ map g ∘ map f
map-∘ = elim ≡.refl (≡.cong step)

map-cong : ∀{o} {A B : Set o} {F G : A → B} → F ≐ G → map F ≐ map G
map-cong eq = elim (≡.cong base ∘ eq $ᵢ) (≡.cong step)

map-congᵢ : ∀{o} {A B : Set o} {F G : A → B} → F ≐ᵢ G → map F ≐ map G
map-congᵢ eq = elim (≡.cong base eq) (≡.cong step)
\end{code}

These results could be generalised to |⟦_,_⟧| if needed.

%}}}

%{{{ Free ; AdjLeft
\subsection{The Toolki Appears Naturally: Part 1}

That |Eventually| furnishes a set with its free unary algebra can now be realised.

\begin{code}
Free : (ℓ : Level) → Functor (Sets ℓ) (Unarys ℓ)
Free ℓ = record
  { F₀             =   λ A → MkUnary (Eventually A) step
  ; F₁             =   λ f → MkHom (map f) ≡.refl
  ; identity       =   map-id
  ; homomorphism   =   map-∘
  ; F-resp-≡      =   λ F≈G → map-cong (λ _ → F≈G)
  }

AdjLeft : (ℓ : Level) → Adjunction (Free ℓ) (Forget ℓ)
AdjLeft ℓ = record
  { unit     =   record { η = λ _ → base ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ A → MkHom (iterate (Op A)) ≡.refl ; commute = iterate-nat }
  ; zig      =   iterate-map-id
  ; zag      =   ≡.refl
  }
\end{code}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item |map|: usually functions can be packaged-up to work on syntax of unary algebras.
\item |map-id|: the identity function leaves syntax alone; or: |map id| can be replaced with a constant
  time algorithm, namely, |id|.
\item |map-∘|: sequential substitutions on syntax can be efficiently replaced with a single substitution.
\item |map-cong|: observably indistinguishable substitutions can be used in place of one another, similar to the
      transparency principle of Haskell programs.
\item |iterate|: given a function |f|, we have |stepⁿ base x ↦ fⁿ x|. Along with properties of this operation.
\end{itemize}

%}}}

%{{{ Iteration and properties

\begin{code}
_^_ : {a : Level} {A : Set a} (f : A → A) → ℕ → (A → A)
f ^ zero = id
f ^ suc n = f ^ n ∘ f

-- important property of iteration that allows it to be defined in an alternative fashion
iter-swap : {ℓ : Level} {A : Set ℓ} {f : A → A} (n : ℕ) → (f ^ n) ∘ f ≐ f ∘ (f ^ n)
iter-swap zero = ≐-refl
iter-swap {f = f} (suc n) = ∘-≐-cong₁ f (iter-swap n)

-- iteration of commutable functions
iter-comm : {ℓ : Level} {B C : Set ℓ} {f : B → C} {g : B → B} {h : C → C}
  → (leap-frog : f ∘ g ≐ᵢ h ∘ f)
  → {n : ℕ} → h ^ n ∘ f ≐ᵢ f ∘ g ^ n
iter-comm leap {zero} = ≡.refl
iter-comm {ℓ} {B} {C} {f} {g = g} {h} leap {suc n} {x} = ≡.cong (h ^ n) (≡.sym (leap {x})) ⟨≡≡⟩ iter-comm {ℓ} {B} {C} {f} {g} {h} leap {n} {g x}

-- exponentation distributes over product
^-over-× : {a b : Level} {A : Set a} {B : Set b} {f : A → A} {g : B → B}
         → {n : ℕ} → (f ×₁ g) ^ n ≐ (f ^ n) ×₁ (g ^ n)
^-over-× {n = zero} = λ{ (x , y) → ≡.refl}
^-over-× {f = f} {g} {n = suc n} = ^-over-× {n = n} ∘ (f ×₁ g)
\end{code}

%}}}

%{{{ Direct representation
\subsection{The Toolki Appears Naturally: Part 2}

And now for a different way of looking at the same algebra.
We ``mark'' a piece of data with its depth.

\begin{code}
Free² : (ℓ : Level) → Functor (Sets ℓ) (Unarys ℓ)
Free² ℓ = record
  { F₀             =   λ A → MkUnary (ℕ × A) (suc ×₁ id)
  ; F₁             =   λ f → MkHom (id ×₁ f) ≡.refl
  ; identity       =   ≐-refl
  ; homomorphism   =   ≐-refl
  ; F-resp-≡      =   λ F≈G → λ { (n , x) → ≡.cong₂ _,_ ≡.refl (F≈G {x}) }
  }

-- tagging operation
at : {a : Level} {A : Set a} → ℕ → A → ℕ × A
at n = λ x → (n , x)

ziggy : {a : Level} {A : Set a} (n : ℕ) → at n  ≐  (suc ×₁ id {A = A}) ^ n ∘ at 0
ziggy zero = ≐-refl
ziggy {A = A} (suc n) = begin⟨ ≐-setoid A (ℕ × A) ⟩
   (suc ×₁ id)             ∘ at n                            ≈⟨ ∘-≐-cong₂ (suc ×₁ id) (ziggy n) ⟩
   (suc ×₁ id)             ∘ (suc ×₁ id {A = A}) ^ n ∘ at 0  ≈⟨ ∘-≐-cong₁ (at 0) (≐-sym (iter-swap n )) ⟩
   (suc ×₁ id {A = A}) ^ n ∘ (suc ×₁ id)             ∘ at 0  ∎
  where open import Relation.Binary.SetoidReasoning

AdjLeft² : ∀ o → Adjunction (Free² o) (Forget o)
AdjLeft² o = record
  { unit        =   record { η = λ _ → at 0 ; commute = λ _ → ≡.refl }
  ; counit      =   record
    { η         =   λ A → MkHom (uncurry (Op A ^_)) (λ{ {n , a} → iter-swap n a})
    ; commute   =   λ {X} {Y} F → uncurry λ x y → iter-comm {f = mor F} {g = Op X} {h = Op Y} (pres-op F) {n = x} {y}
    }
  ; zig         =   uncurry ziggy
  ; zag         =   ≡.refl
  }
\end{code}

Notice that the adjunction proof forces us to come-up with the operations and properties about them!
\begin{itemize}
\item |iter-comm|: \unfinished
\item |_^_|: \unfinished
\item |iter-swap|: \unfinished
\item |ziggy|: \unfinished
\end{itemize}
%}}}

%{{{ Right Adjoint - can't decide if it has none, or I just can't quite find it.
\begin{code}

Right : (ℓ : Level) → Functor (Sets ℓ) (Unarys ℓ)
Right ℓ = record
            { F₀ = λ A → MkUnary {!!} {!!}
            ; F₁ = λ f → MkHom {!!} {!!}
            ; identity = {!!}
            ; homomorphism = {!!}
            ; F-resp-≡ = {!!}
            }

Adj : (ℓ : Level) → Adjunction (Forget ℓ) (Right ℓ)
Adj ℓ = record
  { unit = record { η = λ X → MkHom {!!} {!!}
                  ; commute = λ { (MkHom mor₁ pres-op₁) x → {!!} } }
  ; counit = record { η = λ X x → {!!}
                    ; commute = λ f → {!!} }
  ; zig = {!!}
  ; zag = λ x → {!!}}

NoRight : {ℓ : Level} → (CoFree : Functor (Sets ℓ) (Unarys ℓ)) → ¬ (Adjunction (Forget ℓ) CoFree)
NoRight {ℓ} record { F₀ = F₀ ; F₁ = F₁ ; identity = identity ; homomorphism = homomorphism ; F-resp-≡ = F-resp-≡ } adj =
  ⊥-elim (η (counit adj) ⊥ {!mor (η (unit adj) (F₀ ⊥))!})
  where open Adjunction
        open NaturalTransformation
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
