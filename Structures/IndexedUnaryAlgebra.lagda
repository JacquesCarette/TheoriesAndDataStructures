\section{Indexed Unary Algebras}

%{{{ Necessary Imports
\begin{code}
module Structures.IndexedUnaryAlgebra where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)
open import Function hiding (_$_)
open import Data.List

open import Helpers.Categorical

open import Helpers.Forget
open import Helpers.Function2
open import Helpers.EqualityCombinators
open import Helpers.DataProperties
\end{code}
%}}}

%{{{ _UnaryAlg
An \emph{|I| indexed unary algebra} consists of a carrier |Q| and for each
index |i : I| a unary morphism |Opᵢ : Q → Q| on the carrier. In general, an
operation of type |I × Q → Q| is also known as an \emph{|I| action on |Q|},
and pop-up in the study of groups and vector spaces.

\begin{code}
record UnaryAlg {a} (I : Set a) (ℓ : Level) : Set (lsuc ℓ ⊍ a) where
  constructor MkAlg
  field
    Carrier : Set ℓ
    Op      : {i : I} → Carrier → Carrier

  -- action form
  _·_ : I → Carrier → Carrier
  i · c = Op {i} c

open UnaryAlg
\end{code}
%}}}

Henceforth we work with a given indexing set,
\begin{code}
module _ {a} (I : Set a) where   -- Musa: Most likely ought to name this module.
\end{code}

%{{{ Hom
Give two unary algebras, over the same indexing set, a morphism between them
is a function of their underlying carriers that respects the actions.

\begin{code}
  record Hom {ℓ} (X Y : UnaryAlg I ℓ) : Set (lsuc ℓ ⊍ a) where
    constructor MkHom
    infixr 5 mor
    field
      mor           :  Carrier X → Carrier Y
      preservation  :  {i : I} → mor ∘ Op X {i}  ≐  Op Y {i} ∘ mor

  open Hom using (mor)
  open Hom using () renaming (mor to _$_) -- override application to take a |Hom|

  -- arguments can usually be inferred, so implicit variant
  preservation : {ℓ : Level} {X Y : UnaryAlg I ℓ} (F : Hom X Y) 
               → {i : I} {x : Carrier X} → F $ Op X {i} x  ≡  Op Y {i} (F $ x)
  preservation F = Hom.preservation F _             
\end{code}

Notice that the |preservation| proof looks like a usual homomorphism condition ---after excusing the implicits.
Rendered in action notation, it would take the shape |∀{i x} → mor (i · x) ≡ i · mor x| with the |mor|
``leap-frogging'' over the action. Admiteddly this form is also common and then |mor| is called an ``equivaraint''
function, yet this sounds like a new unfamilar concept than it really it: Homomorphism.
%}}}

%{{{ UnaryAlgCat ; Forget

Unsuprisngly, the indexed unary algebra's form a category.

\begin{code}
  UnaryAlgCat : (ℓ : Level) → Category (lsuc ℓ ⊍ a) (lsuc ℓ ⊍ a) ℓ
  UnaryAlgCat ℓ = record
    { Obj   =   UnaryAlg I ℓ
    ; _⇒_   =   Hom
    ; _≡_   =   λ F G → mor F ≐ mor G
    ; id    =   λ {A} → MkHom id ≐-refl
    ; _∘_   =   λ {A} {B} {C} F G → MkHom (mor F ∘ mor G) (λ {i} x → let open ≡.≡-Reasoning {A = Carrier C} in begin
         (mor F ∘ mor G ∘ Op A) x
            ≡⟨ ≡.cong (mor F) (preservation G) ⟩
         (mor F ∘ Op B ∘ mor G) x
            ≡⟨ preservation F ⟩
         (Op C ∘ mor F ∘ mor G) x
            ∎)
    ; assoc       =   ≐-refl
    ; identityˡ   =   ≐-refl
    ; identityʳ   =   ≐-refl
    ; equiv      =   record { IsEquivalence ≐-isEquivalence}
    ; ∘-resp-≡  = λ {A} {B} {C} {F} {G} {H} {K} F≈G H≈K x → let open ≡.≡-Reasoning {A = Carrier C} in begin
         (mor F ∘ mor H) x
            ≡⟨ F≈G _ ⟩
         (mor G ∘ mor H) x
            ≡⟨ ≡.cong (mor G) (H≈K _) ⟩
         (mor G ∘ mor K) x
            ∎ 
    }
    where
      open import Relation.Binary using (IsEquivalence)
\end{code}

Needless to say, we can ignore the extra structure to arrive at the underlying carrier.

\begin{code}
  Forget : (ℓ : Level) → Functor (UnaryAlgCat ℓ) (Sets ℓ)
  Forget ℓ = record
    { F₀             =   Carrier
    ; F₁             =   mor
    ; identity       =   ≡.refl
    ; homomorphism   =   ≡.refl
    ; F-resp-≡      =   λ F≈G {x} → F≈G x
    }
\end{code}  
%}}}

%{{{ I* ; the free I-unaryAlgebra

For each |I| indexed unary algebra |(A, Op)| with an elected element |a₀ : A|,
there is a unique homomorpism |fold : (List I, _∷_) ⟶ (A, Op)| sending |[] ↦ a₀|.

\begin{code}  
  module _ (Q : UnaryAlg I a) (q₀ : Carrier Q) where

    open import Data.Unit
    I* : UnaryAlg I a
    I* = MkAlg (List I) (λ {x} xs → x ∷ xs)

    fold₀ : List I → Carrier Q
    fold₀ []        =  q₀
    fold₀ (x ∷ xs)  =  Op Q {x} (fold₀ xs)

    fold : Hom I* Q 
    fold = MkHom fold₀ ≐-refl

    fold-point : fold $ [] ≡ q₀
    fold-point = ≡.refl

    fold-unique : (F : Hom I* Q)(point : F $ [] ≡ q₀) → mor F ≐ mor fold
    fold-unique F point [] = point
    fold-unique F point (x ∷ xs) = let open ≡.≡-Reasoning {A = Carrier Q} in begin
         mor F (x ∷ xs)
            ≡⟨ preservation F ⟩
         Op Q {x} (mor F xs)
            ≡⟨ induction-hypothesis ⟩
         Op Q {x} (fold₀ xs)
            ∎
            where induction-hypothesis = ≡.cong (Op Q) (fold-unique F point xs)
\end{code}

Perhaps it would be better to consider POINTED indexed unary algebras, where this
result may be phrased more concisely.

%}}}

WK: A signature with no constant symbols results in there being no closed terms
and so the term algebra is just the empty set of no closed terms quotiented by
the given equations and the resulting algebra has an empty carrier.

Free : build over generators  -- cf Multiset construction in CommMonoid.lagda
Initial : does not require generators

ToDo ∷ mimic the multiset construction here for generators S “over” IndexedUnaryAlgebras.
WK claims it may have carrier S × List I; then the non-indexed case is simply List ⊤ ≅ ℕ.

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

