\def\unfinished{ \LARGE unfinished }

\makeatletter
\newenvironment{spec}%
  {\tiny\verbatim}%
  {\endverbatim}

\section{Binary Heterogeneous Relations --- Bipartite graphs}

We consider two sorted algebras endowed with a binary heterogeneous relation.
An example of such a structure is a graph, or network, which has a sort for edges and a
sort for nodes and an incidence relation.

%{{{ Imports
\begin{code}
module Structures.Rel where

open import Level renaming (suc to lsuc; zero to lzero ; _⊔_ to _⊍_)
open import Categories.Category     using   (Category)
open import Categories.Functor      using   (Functor)
open import Categories.Adjunction   using   (Adjunction)
open import Categories.Agda         using   (Sets)
open import Function                using   (id ; _∘_ ; const)
open import Function2               using   (_$ᵢ)

open import Forget
open import EqualityCombinators
open import DataProperties
open import Structures.TwoSorted using (TwoSorted; Twos ; MkTwo) renaming (Hom to TwoHom ; MkHom to MkTwoHom)
\end{code}
%}}}

%{{{ HetroRel ; Hom

\subsection{Definitions}

We define the structure involved, along with a notational convenience:

\begin{code}
record HetroRel ℓ ℓ′ : Set (lsuc (ℓ ⊍ ℓ′)) where
  constructor MkHRel
  field
    One : Set ℓ
    Two : Set ℓ
    Rel : One → Two → Set ℓ′

open HetroRel
relOp = HetroRel.Rel
syntax relOp A x y = x ⟨ A ⟩ y
\end{code}

Then define the strcture-preserving operations,

\begin{code}
record Hom {ℓ ℓ′} (Src Tgt : HetroRel ℓ ℓ′) : Set (ℓ ⊍ ℓ′) where
  constructor MkHom
  field
    one   : One Src → One Tgt
    two   : Two Src → Two Tgt
    shift : {x : One Src} {y : Two Src} → x ⟨ Src ⟩ y → one x  ⟨ Tgt ⟩  two y

open Hom
\end{code}

%}}}

\subsection{Category and Forgetful Functors}
That these structures form a two-sorted algebraic category can easily be witnessed.
%{{{ Rels

\begin{code}
Rels : (ℓ ℓ′ : Level) → Category (lsuc (ℓ ⊍ ℓ′)) (ℓ ⊍ ℓ′) ℓ
Rels ℓ ℓ′ = record
  { Obj        =   HetroRel ℓ ℓ′
  ; _⇒_       =   Hom
  ; _≡_       =   λ F G → one F ≐ one G   ×  two F ≐ two G
  ; id         =   MkHom id id id
  ; _∘_        =   λ F G → MkHom (one F ∘ one G) (two F ∘ two G) (shift F ∘ shift G)
  ; assoc      =   ≐-refl , ≐-refl
  ; identityˡ  =   ≐-refl , ≐-refl
  ; identityʳ  =   ≐-refl , ≐-refl
  ; equiv     =  record
    { refl    =  ≐-refl , ≐-refl
    ; sym     =  λ { (oneEq , twoEq)  → ≐-sym oneEq , ≐-sym twoEq }
    ; trans   =  λ { (oneEq₁ , twoEq₁) (oneEq₂ , twoEq₂) → ≐-trans oneEq₁ oneEq₂ , ≐-trans twoEq₁ twoEq₂}
    }
  ; ∘-resp-≡ = λ{ (g≈₁k , g≈₂k) (f≈₁h , f≈₂h) → ∘-resp-≐ g≈₁k f≈₁h , ∘-resp-≐ g≈₂k f≈₂h }
  }
\end{code}
%}}}
%{{{ Forget¹ ; Forget² ; Forget³

We can forget about the first sort or the second to arrive at our starting
category and so we have two forgetful functors. Moreover, we can simply
forget about the relation to arrive at the two-sorted category :-)

\begin{code}
Forget¹ : (ℓ ℓ′ : Level) → Functor (Rels ℓ ℓ′) (Sets ℓ)
Forget¹ ℓ ℓ′ = record
  { F₀             =   HetroRel.One
  ; F₁             =   Hom.one
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₁G x }
  }

Forget² : (ℓ ℓ′ : Level) → Functor (Rels ℓ ℓ′) (Sets ℓ)
Forget² ℓ ℓ′ = record
  { F₀             =   HetroRel.Two
  ; F₁             =   Hom.two
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ{ (F≈₁G , F≈₂G) {x} → F≈₂G x }
  }

-- Whence, |Rels| is a subcategory of Twos
Forget³ : (ℓ ℓ′ : Level) → Functor (Rels ℓ ℓ′) (Twos ℓ)
Forget³ ℓ ℓ′ = record
  { F₀             =   λ S → MkTwo (One S) (Two S)
  ; F₁             =   λ F → MkTwoHom (one F) (two F)
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  }
\end{code}
%}}}

%{{{ Free and CoFree : 1,2,3 and 3′
\subsection{Free and CoFree Functors}

Given a (two)type, we can pair it with the empty type or the singleton type
and so we have a free and a co-free constructions. Intuitively, the empty
type denotes the empty relation which is the smallest relation and so a free
construction; whereas, the singleton type denotes the ``always true'' relation
which is the largest binary relation and so a cofree construction.

   %{{{ adjoints to forgetting the FIRST component of a HetroRel

\subsubsection*{Candidate adjoints to forgetting the \emph{first} component of a |Rels|}

\begin{code}
Free¹ : (ℓ ℓ′ : Level) → Functor (Sets ℓ) (Rels ℓ ℓ′)
Free¹ ℓ ℓ′ = record
  { F₀             =   λ A → MkHRel A ⊥ (λ{ _ ()})
  ; F₁             =   λ f → MkHom f id (λ{ {y = ()} })
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl  
  }

-- | (MkRel X ⊥ ⊥ ⟶ Alg) ≅ (X ⟶ One Alg)|
Left¹ : (ℓ ℓ′ : Level) → Adjunction (Free¹ ℓ ℓ′) (Forget¹ ℓ ℓ′)
Left¹ ℓ ℓ′ = record
  { unit   = record
    { η       = λ _ → id
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ A → MkHom (λ z → z) (λ{()}) (λ {x} {})
    ; commute = λ f → ≐-refl , (λ ())
    }
  ; zig = ≐-refl , (λ ())
  ; zag = ≡.refl
  }

CoFree¹ : (ℓ : Level) → Functor (Sets ℓ) (Rels ℓ ℓ)
CoFree¹ ℓ = record
  { F₀             =   λ A → MkHRel A ⊤ (λ _ _ → A)
  ; F₁             =   λ f → MkHom f id f 
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }

-- | (One Alg ⟶ X) ≅ (Alg ⟶ MkRel X ⊤ (λ _ _ → X)|
Right¹ :  (ℓ : Level) → Adjunction (Forget¹ ℓ ℓ) (CoFree¹ ℓ)
Right¹ ℓ  = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) (λ {x} {y} _ → x)
    ; commute = λ _ → ≐-refl , (λ x → ≡.refl)
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl , λ{ tt → ≡.refl}
  }

-- Another cofree functor:

CoFree¹′ : (ℓ : Level) → Functor (Sets ℓ) (Rels ℓ ℓ)
CoFree¹′ ℓ = record
  { F₀             =   λ A → MkHRel A ⊤ (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom f id id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ f≈g → (λ x → f≈g {x}) , ≐-refl
  }

-- | (One Alg ⟶ X) ≅ (Alg ⟶ MkRel X ⊤ (λ _ _ → ⊤)|
Right¹′ :  (ℓ : Level) → Adjunction (Forget¹ ℓ ℓ) (CoFree¹′ ℓ)
Right¹′ ℓ  = record
  { unit = record
    { η = λ _ → MkHom id (λ _ → tt) (λ {x} {y} _ → tt)
    ; commute = λ _ → ≐-refl , (λ x → ≡.refl)
    }
  ; counit   =   record { η = λ _ → id ; commute = λ _ → ≡.refl }
  ; zig      =   ≡.refl
  ; zag      =   ≐-refl , λ{ tt → ≡.refl}
  }
\end{code}

But wait, adjoints are necessarily unique, up to isomorphism, whence
|CoFree¹ ≅ Cofree¹′|.
Intuitively, the relation part is a ``subset'' of the given carriers
and when one of the carriers is a singleton then the largest relation
is the universal relation which can be seen as either the first non-singleton carrier
or the ``always-true'' relation which happens to be formalized by ignoring its arguments
and going to a singleton set.

%}}}

   %{{{ adjoints to forgetting the SECOND component of a HetroRel
\subsubsection*{Candidate adjoints to forgetting the \emph{second} component of a |Rels|}

\begin{code}
Free² : (ℓ : Level) → Functor (Sets ℓ) (Rels ℓ ℓ)
Free² ℓ = record
  { F₀             =   λ A → MkHRel ⊥ A (λ ())
  ; F₁             =   λ f → MkHom id f (λ {})
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → ≐-refl , (λ x → F≈G {x})
  }

-- | (MkRel ⊥ X ⊥ ⟶ Alg) ≅ (X ⟶ Two Alg)|
Left² : (ℓ : Level) → Adjunction (Free² ℓ) (Forget² ℓ ℓ)
Left² ℓ = record
  { unit   = record
    { η       = λ _ → id
    ; commute = λ _ → ≡.refl
    }
  ; counit = record
    { η       = λ _ → MkHom (λ ()) id (λ {})
    ; commute = λ f →  (λ ()) , ≐-refl
    }
  ; zig = (λ ()) , ≐-refl
  ; zag = ≡.refl
  }

CoFree² : (ℓ : Level) → Functor (Sets ℓ) (Rels ℓ ℓ)
CoFree² ℓ = record
  { F₀             =   λ A → MkHRel ⊤ A (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom id f id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → ≐-refl , (λ x → F≈G {x})
  }

-- |(Two Alg ⟶ X) ≅ (Alg ⟶ ⊤ X ⊤|
Right² : (ℓ : Level) → Adjunction (Forget² ℓ ℓ) (CoFree² ℓ)
Right² ℓ = record
  { unit   = record
    { η       = λ _ → MkHom (λ _ → tt) id (λ _ → tt)
    ; commute = λ f → ≐-refl , ≐-refl
    }
  ; counit = record
    { η       = λ _ → id
    ; commute = λ _ →  ≡.refl
    }
  ; zig = ≡.refl
  ; zag = (λ{ tt → ≡.refl}) , ≐-refl
  }
\end{code}

%}}}

   %{{{ adjoints to forgetting the THIRD component of a HetroRel
\subsubsection*{Candidate adjoints to forgetting the \emph{third} component of a |Rels|}   
\begin{code}
Free³ : (ℓ : Level) → Functor (Twos ℓ) (Rels ℓ ℓ)
Free³ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → ⊥)
  ; F₁             =   λ f → MkHom (one f) (two f) id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom

-- |(MkTwo X Y → Alg without Rel) ≅ (MkRel X Y ⊥ ⟶ Alg)|
Left³ : (ℓ : Level) → Adjunction (Free³ ℓ) (Forget³ ℓ ℓ)
Left³ ℓ = record
  { unit   = record
    { η       = λ A → MkTwoHom id id
    ; commute = λ F → ≐-refl , ≐-refl
    }
  ; counit = record
    { η       = λ A → MkHom id id (λ ())
    ; commute = λ F →  ≐-refl , ≐-refl
    }
  ; zig = ≐-refl , ≐-refl
  ; zag = ≐-refl , ≐-refl
  }
\end{code}

\begin{code}
CoFree³ : (ℓ : Level) → Functor (Twos ℓ) (Rels ℓ ℓ)
CoFree³ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → ⊤)
  ; F₁             =   λ f → MkHom (one f) (two f) id
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom

-- |(Alg without Rel ⟶ MkTwo X Y) ≅ (Alg ⟶ MkRel X Y ⊤)|
Right³ : (ℓ : Level) → Adjunction (Forget³ ℓ ℓ) (CoFree³ ℓ)
Right³ ℓ = record
  { unit   = record
    { η       = λ A → MkHom id id (λ _ → tt)
    ; commute = λ F → ≐-refl , ≐-refl
    }
  ; counit = record
    { η       = λ A → MkTwoHom id id
    ; commute = λ F →  ≐-refl , ≐-refl
    }
  ; zig = ≐-refl , ≐-refl
  ; zag = ≐-refl , ≐-refl
  }

CoFree³′ : (ℓ : Level) → Functor (Twos ℓ) (Rels ℓ ℓ)
CoFree³′ ℓ = record
  { F₀             =   λ S → MkHRel (One S) (Two S) (λ _ _ → One S × Two S)
  ; F₁             =   λ F → MkHom (one F) (two F) (one F ×₁ two F)
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   id
  } where open TwoSorted ; open TwoHom

-- |(Alg without Rel ⟶ MkTwo X Y) ≅ (Alg ⟶ MkRel X Y X×Y)|
Right³′ : (ℓ : Level) → Adjunction (Forget³ ℓ ℓ) (CoFree³′ ℓ)
Right³′ ℓ = record
  { unit   = record
    { η       = λ A → MkHom id id (λ {x} {y} x~y → x , y)
    ; commute = λ F → ≐-refl , ≐-refl
    }
  ; counit = record
    { η       = λ A → MkTwoHom id id
    ; commute = λ F →  ≐-refl , ≐-refl
    }
  ; zig = ≐-refl , ≐-refl
  ; zag = ≐-refl , ≐-refl
  }
\end{code}

But wait, adjoints are necessarily unique, up to isomorphism, whence
|CoFree³ ≅ CoFree³′|.
Intuitively, the relation part is a ``subset'' of the given carriers
and so the largest relation is the universal relation which can be seen as the product of the carriers
or the ``always-true'' relation which happens to be formalized by ignoring its arguments
and going to a singleton set.
%}}}

%}}}

%{{{ porting over other results
\iffalse

\subsection{\unfinished}

It remains to port over results such as Merge, Dup, and Choice from Twos to Rels.

Also to consider: sets with an equivalence relation;
whence propositional equality.

  %{{{ Merge and Dup functors ; Right₂ adjunction

The category of sets contains products and so |TwoSorted| algebras can be represented there
and, moreover, this is adjoint to duplicating a type to obtain a |TwoSorted| algebra.

\begin{spec}
-- The category of Sets has products and so the |TwoSorted| type can be reified there.
Merge : (ℓ : Level) → Functor (Twos ℓ) (Sets ℓ)
Merge ℓ = record
  { F₀             =   λ S → One S ×  Two S
  ; F₁             =   λ F → one F ×₁ two F
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≡      =   λ { (F≈₁G , F≈₂G) {x , y} → ≡.cong₂ _,_ (F≈₁G x) (F≈₂G y) }
  }

-- Every set gives rise to its square as a |TwoSorted| type.
Dup : (ℓ : Level) → Functor (Sets ℓ) (Twos ℓ)
Dup ℓ = record
  { F₀             =   λ A → MkTwo A A
  ; F₁             =   λ f → MkHom f f
  ; identity       =   ≐-refl , ≐-refl
  ; homomorphism   =   ≐-refl , ≐-refl
  ; F-resp-≡      =   λ F≈G → diag (λ _ → F≈G)
  }
\end{spec}

Then the proof that these two form the desired adjunction

\begin{spec}
Right₂ : (ℓ : Level) → Adjunction (Dup ℓ) (Merge ℓ)
Right₂ ℓ = record
  { unit     =   record { η = λ _ → diag ; commute = λ _ → ≡.refl }
  ; counit   =   record { η = λ _ → MkHom proj₁ proj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; zig      =   ≐-refl , ≐-refl
  ; zag      =   ≡.refl
  }
\end{spec}
%}}}

  %{{{ Choice ; from⊎ ; Left₂ adjunction

The category of sets admits sums and so an alternative is to represet a |TwoSorted|
algebra as a sum, and moreover this is adjoint to the aforementioned duplication functor.

\begin{spec}
Choice : (ℓ : Level) → Functor (Twos ℓ) (Sets ℓ)
Choice ℓ =   record
  { F₀             =   λ S → One S ⊎  Two S
  ; F₁             =   λ F → one F ⊎₁ two F
  ; identity       =   ⊎-id $ᵢ
  ; homomorphism   =   λ{ {x = x} → ⊎-∘ x }
  ; F-resp-≡      =   λ F≈G {x} → uncurry ⊎-cong F≈G x
  }
  
Left₂ : (ℓ : Level) → Adjunction (Choice ℓ) (Dup ℓ)
Left₂ ℓ = record
  { unit     =   record { η = λ _ → MkHom inj₁ inj₂ ; commute = λ _ → ≐-refl , ≐-refl }
  ; counit   =   record { η = λ _ → from⊎ ; commute = λ _ {x} → (≡.sym ∘ from⊎-nat) x }
  ; zig      =   λ{ {_} {x} → from⊎-preInverse x }
  ; zag      =   ≐-refl , ≐-refl
  }
\end{spec}
%}}}

\fi

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
