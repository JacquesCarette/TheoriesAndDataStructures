\subsection{Unions of |SetoidFamily|}

We need a way to put two |SetoidFamily| ``side by side'' -- a form of
parellel composition.  To achieve this requires a certain amount of
infrastructure: parallel composition of relations, and both disjoint
sum and cartesian product of |Setoid|s.  So the next couple of sections
proceed with that infrastruction, before diving in to the crux of the
matter.

%{{{ Imports
\begin{code}
module SetoidFamilyUnion where

open import Level
open import Relation.Binary    using  (Setoid; REL; Rel)
open import Function           using  (flip) renaming (id to id₀; _∘_ to _⊚_)
open import Function.Equality  using  (Π; _⟨$⟩_; cong; id; _⟶_; _∘_)
open import Function.Inverse   using  () renaming (_InverseOf_ to Inv)
open import Relation.Binary.Product.Pointwise using (_×-setoid_)

open import Categories.Category using (Category)
open import Categories.Object.Coproduct

open import DataProperties
open import SetoidEquiv
open import ISEquiv
open import ParComp

open import TypeEquiv using (swap₊; swap⋆)
\end{code}
%}}}

%{{{ \subsection{Disjoint parallel composition} |⊎⊎|
\subsection{Disjoint parallel composition}

The motivation for parallel composition is to lift this to |SetoidFamily|.
But there are two rather different cases.  First, a rather
straightforward situation when the underlying |Setoid| are different, there is
little choice but to take the union of the |Setoid|s as the |Carrier|, and
everything else follows straightforwardly.

\subsubsection{Basic definitions}

For some odd reason, the levels of the families must be the same.  Even using direct
matching (instead of |[_,_]|).
\begin{code}
infix 3 _⊎⊎_

_⊎⊎_ : {ℓS ℓs ℓT ℓt ℓA ℓa : Level} {S : Setoid ℓS ℓs} {T : Setoid ℓT ℓt}
  → SetoidFamily S ℓA ℓa → SetoidFamily T ℓA ℓa → SetoidFamily (S ⊎S T) ℓA ℓa
X ⊎⊎ Y = record
  { index = [ A.index , B.index ]
  ; reindex =
    λ { {inj₁ s₁} {inj₁ s₂} (left s₁≈s₂) → record
        { _⟨$⟩_ = _⟨$⟩_ (A.reindex s₁≈s₂)
        ; cong = Π.cong (A.reindex s₁≈s₂)
        }
      ; {inj₂ t₁} {inj₂ t₂} (right t₁≈t₂) → record
        { _⟨$⟩_ = _⟨$⟩_ (B.reindex t₁≈t₂)
        ; cong = Π.cong (B.reindex t₁≈t₂)
        }
      }
  ; id-coh =  λ { {inj₁ x} → A.id-coh ; {inj₂ y} → B.id-coh}
  ; sym-iso = λ { {inj₁ x} (left r₁) → A.sym-iso r₁ ; {inj₂ y} (right r₂) → B.sym-iso r₂}
  ; trans-coh = λ { {inj₁ x} (left r₁) (left r₂) → A.trans-coh r₁ r₂
                  ; {inj₂ y₂} (right r₂) (right r₃) → B.trans-coh r₂ r₃}
  }
    where
      module A = SetoidFamily X
      module B = SetoidFamily Y
\end{code}
%}}}

%{{{ \subsubsection{|⊎⊎-comm|}
\subsubsection{|⊎⊎-comm|}
\begin{code}
⊎⊎-comm : {ℓS ℓs ℓT ℓt ℓA ℓa : Level} {S : Setoid ℓS ℓs} {T : Setoid ℓT ℓt}
  {A₁ : SetoidFamily S ℓA ℓa} {A₂ : SetoidFamily T ℓA ℓa}
  → (A₁ ⊎⊎ A₂) ♯ (A₂ ⊎⊎ A₁)
⊎⊎-comm {S = S} {T} {A} {B} = record
  { to = FArr swap⊎ [ (λ _ → id) , (λ _ → id) ]
                    (λ { {inj₁ x} {inj₁ y} (left r₁) → Setoid.refl (index A y)
                       ; {inj₂ y} {inj₂ z} (right r₂) → Setoid.refl (index B z) })
  ; from = FArr swap⊎ (λ { (inj₁ x) → id
                         ; (inj₂ y) → id })
                   (λ { {x = inj₁ x₁} {By = By} (left r₁) → Setoid.refl (index B x₁)
                      ; {x = inj₂ x₂} {By = By} (right r₂) → Setoid.refl (index A x₂) })
  ; left-inv = record
    { ext = λ { (inj₁ x) → left (Setoid.refl T) ; (inj₂ y) → right (Setoid.refl S) }
    ; transport-ext-coh = λ { (inj₁ x) Bx → Setoid.trans (index B x) (id-coh B) (id-coh B)
                            ; (inj₂ y) Ay → Setoid.trans (index A y) (id-coh A) (id-coh A)}
    }
  ; right-inv = record
    { ext = λ { (inj₁ x) → left (Setoid.refl S) ; (inj₂ y) → right (Setoid.refl T)}
    ; transport-ext-coh = λ { (inj₁ x) Ax → Setoid.trans (index A x) (id-coh A) (id-coh A)
                            ; (inj₂ y) By → Setoid.trans (index B y) (id-coh B) (id-coh B)}
    }
  }
  where
    open SetoidFamily
    swap⊎ : ∀ {ℓA ℓa ℓB ℓb} {A : Setoid ℓA ℓa} {B : Setoid ℓB ℓb} → A ⊎S B ⟶ B ⊎S A
    swap⊎ = record
      { _⟨$⟩_ = [ inj₂ , inj₁ ]
      ; cong = λ { (left r₁) → right r₁ ; (right r₂) → left r₂ }
      }
\end{code}
%}}}

%{{{ \subsection{Common-base composition} |⊔⊔|
\subsection{Common-base composition}

The second situation is when it is known that the two underlying |Setoid|
are the same (which is actually the case we care more about), in which case
things are rather more complex.

\begin{code}
_⊔⊔_ : {ℓS ℓs ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} {S : Setoid ℓS ℓs}
  → SetoidFamily S ℓA₁ ℓa₁ → SetoidFamily S ℓA₂ ℓa₂ → SetoidFamily S (ℓA₁ ⊔ ℓA₂) (ℓa₁ ⊔ ℓa₂)
X ⊔⊔ Y = record
  { index = λ s → A.index s ⊎S B.index s
  ; reindex = λ x≈y → record
    { _⟨$⟩_ = λ { (inj₁ x) → inj₁ (A.reindex x≈y ⟨$⟩ x)
               ; (inj₂ y) → inj₂ (B.reindex x≈y ⟨$⟩ y)}
    ; cong = λ { (left r₁) → left (cong (A.reindex x≈y) r₁)
               ; (right r₂) → right (cong (B.reindex x≈y) r₂)} }
  ; id-coh = λ { {_} {inj₁ x} → left A.id-coh ; {_} {inj₂ y} → right B.id-coh}
  ; sym-iso = λ x≈y → record
    { left-inverse-of =
      λ { (inj₁ x) → left (Inv.left-inverse-of (A.sym-iso x≈y) x)
        ; (inj₂ y) → right (Inv.left-inverse-of (B.sym-iso x≈y) y)}
    ; right-inverse-of =
      λ { (inj₁ x) → left (Inv.right-inverse-of (A.sym-iso x≈y) x)
        ; (inj₂ y) → right (Inv.right-inverse-of (B.sym-iso x≈y) y)} }
  ; trans-coh =
    λ { {b = inj₁ x₁} p q → left (A.trans-coh p q)
      ; {b = inj₂ y₁} p q → right (B.trans-coh p q) }
  }
    where
      module A = SetoidFamily X
      module B = SetoidFamily Y

\end{code}

And it is commutative too:
\begin{code}
⊔⊔-comm : {ℓS ℓs ℓA ℓa ℓB ℓb : Level} {S : Setoid ℓS ℓs}
  {A₁ : SetoidFamily S ℓA ℓa} {A₂ : SetoidFamily S ℓB ℓb}
  → (A₁ ⊔⊔ A₂) ♯ (A₂ ⊔⊔ A₁)
⊔⊔-comm {S = S} {A} {B} = record
  { to = FArr id
           (λ s → record
             { _⟨$⟩_ = swap₊
             ; cong = λ { (left r₁) → right r₁ ; (right r₂) → left r₂} })
           (λ { {y} {x} {inj₁ x₁} p → right (refl (index A _))
              ; {y} {x} {inj₂ y₁} p → left (refl (index B _)) })
  ; from = FArr id
           (λ s → record
             { _⟨$⟩_ = swap₊
             ; cong = λ { (left r₁) → right r₁ ; (right r₂) → left r₂ }})
           (λ { {By = inj₁ x₁} p → right (refl (index B _))
              ; {By = inj₂ y₁} p → left (refl (index A _))})
  ; left-inv = record
    { ext = λ _ → refl S
    ; transport-ext-coh = λ { x (inj₁ x₁) → left (trans (index B x) (id-coh B) (id-coh B))
                            ; x (inj₂ y) → right (trans (index A x) (id-coh A) (id-coh A))} }
  ; right-inv = record
    { ext = λ _ → refl S
    ; transport-ext-coh = λ { x (inj₁ x₁) → left (trans (index A x) (id-coh A) (id-coh A))
                            ; x (inj₂ y) → right (trans (index B x) (id-coh B) (id-coh B))} }
  }
  where open SetoidFamily; open Setoid
\end{code}
%}}}

%{{{ \subsection{|⊎⊎₁|}
\subsection{|⊎⊎₁| - parallel composition of equivalences}
\begin{code}
_⊎⊎₁_ : {ℓS ℓs ℓT ℓt ℓU ℓu ℓV ℓv ℓA ℓa ℓC ℓc : Level}
  {S : Setoid ℓS ℓs} {T : Setoid ℓT ℓt} {U : Setoid ℓU ℓu} {V : Setoid ℓV ℓv}
  {A : SetoidFamily S ℓA ℓa} {B : SetoidFamily U ℓA ℓa}
  {C : SetoidFamily T ℓC ℓc} {D : SetoidFamily V ℓC ℓc}
  → A ♯ C → B ♯ D → (A ⊎⊎ B) ♯ (C ⊎⊎ D)
_⊎⊎₁_ {A = A} {B} {C} {D} A♯C B♯D = record
  { to = FArr (record
      { _⟨$⟩_ = [ (λ s → inj₁ (A→C.map ⟨$⟩ s)) , (λ u → inj₂ (B→D.map ⟨$⟩ u)) ]
      ; cong = λ { (left r₁) → left (cong A→C.map r₁)
                 ; (right r₂) → right (cong B→D.map r₂)} })
    [ A→C.transport , B→D.transport ]
    (λ { {By = By} (left r₁) → A→C.transport-coh {By = By} r₁
       ; {By = By} (right r₂) → B→D.transport-coh {By = By} r₂})
  ; from = FArr (record
      { _⟨$⟩_ = _⟨$⟩_ C→A.map ⊎₁ _⟨$⟩_ D→B.map
      ; cong = λ { (left r₁) → left (cong C→A.map r₁)
                 ; (right r₂) → right (cong D→B.map r₂)} })
    [ C→A.transport , D→B.transport ]
    (λ { {By = By} (left r₁) → C→A.transport-coh {By = By} r₁
       ; {By = By} (right r₂) → D→B.transport-coh {By = By} r₂})
  ; left-inv = record
    { ext = λ { (inj₁ t) → left (_≈≈_.ext (left-inv A♯C) t)
              ; (inj₂ v) → right (_≈≈_.ext (left-inv B♯D) v)}
    ; transport-ext-coh = λ { (inj₁ x) Bx → _≈≈_.transport-ext-coh (left-inv A♯C) x Bx
                            ; (inj₂ y) Bx → _≈≈_.transport-ext-coh (left-inv B♯D) y Bx} }
  ; right-inv = record
    { ext = [ (λ t → left (_≈≈_.ext (right-inv A♯C) t)) ,
              (λ v → right (_≈≈_.ext (right-inv B♯D) v)) ]
    ; transport-ext-coh = λ { (inj₁ x) Bx → _≈≈_.transport-ext-coh (right-inv A♯C) x Bx
                            ; (inj₂ y) By → _≈≈_.transport-ext-coh (right-inv B♯D) y By} }
  }
  where
    open _♯_
    open SetoidFamily

    module A→C = _⇛_ (to A♯C)
    module B→D = _⇛_ (to B♯D)
    module C→A = _⇛_ (from A♯C)
    module D→B = _⇛_ (from B♯D)
\end{code}

We can make a |Category| out of a |SetoidFamily| over a
single |Setoid|. FSSF = Fixed Setoid SetoidFamily.
We also fix it so that |_⇛_| only contains |id|-like things.

\begin{spec}
FSSF-Cat : {ℓS ℓs ℓA ℓa : Level} (S : Setoid ℓS ℓs) → Category _ _ _
FSSF-Cat {_} {_} {ℓA} {ℓa} S = record
  { Obj = SetoidFamily S ℓA ℓa
  ; _⇒_ = λ B B' → Σ (B ⇛ B') (λ arr → ∀ s → _⇛_.map arr ⟨$⟩ s ≈ s)
  ; _≡_ = λ a₁ a₂ → proj₁ a₁ ≈≈ proj₁ a₂
  ; id = id⇛ , λ _ → refl
  ; _∘_ = λ {(B⇛C , refl₁) (A⇛B , refl₂) → A⇛B ∘⇛ B⇛C , (λ s → trans (refl₁ (_⇛_.map A⇛B ⟨$⟩ s)) (refl₂ s))}
  ; assoc = {!!} -- λ { {f = f} {g} {h} → assocˡ f g h}
  ; identityˡ = {!!} -- λ { {f = f} → unitʳ f} -- flipped, because ∘⇛ is.
  ; identityʳ = {!!} -- λ { {f = f} → unitˡ f}
  ; equiv = {!!} -- record { refl = λ {f} → ≈≈-refl f ; sym = ≈≈-sym ; trans = _⟨≈≈⟩_ }
  ; ∘-resp-≡ = {!!} -- λ {A} {B} {C} {f} {h} {g} {i} f≈h g≈i → ∘⇛-cong {S = S} {S} {S} {A} {B} {C} {g} {f} {i} {h} g≈i f≈h
  }
  where open Setoid S
\end{spec}

|_⊔⊔_| is? a coproduct for |FSSF-Cat|.

\begin{spec}
⊔⊔-is-coproduct : {ℓS ℓs ℓA ℓa ℓB ℓb : Level} {S : Setoid ℓS ℓs}
  (A B : SetoidFamily S ℓA ℓa) → Coproduct (FSSF-Cat S) A B
⊔⊔-is-coproduct {S = S} A B = record
  { A+B = A ⊔⊔ B
  ; i₁ = record
    { map = id
    ; transport = λ s → record { _⟨$⟩_ = inj₁ ; cong = left }
    ; transport-coh = λ {_} {x} _ → left (refl (index A x))
    }
  ; i₂ = record
    { map = id
    ; transport = λ s → record { _⟨$⟩_ = inj₂ ; cong = right }
    ; transport-coh = λ {_} {x} _ → right (refl (index B x))
    }
  ; [_,_] = λ {C} A⇛C B⇛C → let
      C⇛B : C ⇛ B  -- putative inverses to |A⇛C| and |B⇛C|
      C⇛B = {!!}
      C⇛A : C ⇛ A
      C⇛A = {!!}
    in record
    { map = map A⇛C
    ; transport = λ sA → let  -- |sA| is thought of as an index for |A|.
         sB : Carrier S
         sB = map C⇛B ⟨$⟩ (map A⇛C ⟨$⟩ sA)
       in record
       { _⟨$⟩_ = λ  { (inj₁ x) → transport A⇛C sA ⟨$⟩ x
                    ; (inj₂ y) → {!transport B⇛C sB ⟨$⟩ y!}
                    }
       ; cong = λ   { (left r₁) → cong (transport A⇛C sA) r₁
                    ; (right r₂) → {! cong (transport {!!} sA) r₂ !}
                    }
       }
    ; transport-coh = λ { {By = inj₁ x₁} → {!!} ; {By = inj₂ y₁} → {!!}}
    }
  ; commute₁ = record { ext = {!!} ; transport-ext-coh = {!!} }
  ; commute₂ = record { ext = {!!} ; transport-ext-coh = {!!} }
  ; universal = λ x x₁ → record { ext = {!!} ; transport-ext-coh = {!!} }
  }
  where
    open Setoid; open SetoidFamily; open _⇛_
\end{spec}
However, to make |_⊔⊔₁_| ``work'', the underlying |map|s in
|A ♯ C| and |B ♯ D| must be coherent in some way.
\begin{spec}
_⊔⊔₁_ : {ℓS ℓs ℓT ℓt ℓA ℓa ℓC ℓc : Level}
  {S : Setoid ℓS ℓs} {T : Setoid ℓT ℓt}
  {A : SetoidFamily S ℓA ℓa} {B : SetoidFamily S ℓA ℓa}
  {C : SetoidFamily T ℓC ℓc} {D : SetoidFamily T ℓC ℓc}
  → A ♯ C → B ♯ D → (A ⊔⊔ B) ♯ (C ⊔⊔ D)
_⊔⊔₁_ {S = S} {T} {A} {B} {C} {D} A♯C B♯D = record
  { to = FArr A→C.map
      (λ x → record
        { _⟨$⟩_ = λ { (inj₁ Ax) → inj₁ (A→C.transport x ⟨$⟩ Ax)
                   ; (inj₂ Bx) → inj₂ (
                     reindex D (Setoid.sym T (_≈≈_.ext (left-inv B♯D) (A→C.map ⟨$⟩ x))) ∘ (B→D.transport (D→B.map ⟨$⟩ {!A→C.map ⟨$⟩ x!})) ⟨$⟩ {!!}
                    -- {!B→D.transport ? ∘ (D→B.transport (A→C.map ⟨$⟩ x))!}
                     ) }
        ; cong = {!!} })
      {!!}
  ; from = FArr {!!} {!!} {!!}
  ; left-inv = {!!}
  ; right-inv = {!!}
  }
  where
    open _♯_
    open SetoidFamily

    module A→C = _⇛_ (to A♯C)
    module B→D = _⇛_ (to B♯D)
    module C→A = _⇛_ (from A♯C)
    module D→B = _⇛_ (from B♯D)
\end{spec}

We can do product too.
\begin{code}
_××_ : {ℓS ℓs ℓA₁ ℓa₁ ℓA₂ ℓa₂ : Level} {S : Setoid ℓS ℓs}
  → SetoidFamily S ℓA₁ ℓa₁ → SetoidFamily S ℓA₂ ℓa₂ → SetoidFamily (S ×S S) _ _
X ×× Y = record
  { index = λ s → A.index (proj₁ s) ×S B.index (proj₂ s)
  ; reindex = λ { (x≈y₁ , x≈y₂) → record
    { _⟨$⟩_ = (λ y → A.reindex x≈y₁ ⟨$⟩ y) ×₁ (λ y → B.reindex x≈y₂ ⟨$⟩ y)
    ; cong =  λ { (r₁ , r₂) → (Π.cong (A.reindex x≈y₁) r₁) , (Π.cong (B.reindex x≈y₂) r₂) }
    } }
  ; id-coh = A.id-coh , B.id-coh
  ; sym-iso = λ { (x≈y₁ , x≈y₂) → record
    { left-inverse-of =  λ {(a , b) → (Inv.left-inverse-of (A.sym-iso x≈y₁) a) ,
                                      (Inv.left-inverse-of (B.sym-iso x≈y₂) b) }
    ; right-inverse-of =  λ {(a , b) → (Inv.right-inverse-of (A.sym-iso x≈y₁) a) ,
                                       (Inv.right-inverse-of (B.sym-iso x≈y₂) b) }
    } }
  ; trans-coh =  λ { (a≈b₁ , a≈b₂) (b≈c₁ , b≈c₂) → A.trans-coh a≈b₁ b≈c₁ ,
                                                   B.trans-coh a≈b₂ b≈c₂ }
  }
    where
      module A = SetoidFamily X
      module B = SetoidFamily Y
\end{code}

And it is commutative too:
\begin{code}
××-comm : {ℓS ℓs ℓA ℓa ℓB ℓb : Level} {S : Setoid ℓS ℓs}
  {A₁ : SetoidFamily S ℓA ℓa} {A₂ : SetoidFamily S ℓB ℓb}
  → (A₁ ×× A₂) ♯ (A₂ ×× A₁)
××-comm {S = S} {A} {B} = record
  { to = FArr
    (record { _⟨$⟩_ = swap⋆ ; cong = swap⋆ })
    (λ _ → record { _⟨$⟩_ = swap⋆ ; cong = swap⋆ })
    (λ _ → refl (index B _) , refl (index A _))
  ; from = FArr
    (record { _⟨$⟩_ = swap⋆ ; cong = swap⋆ })
    (λ _ → record { _⟨$⟩_ = swap⋆ ; cong = swap⋆ })
    (λ _ → refl (index A _) , refl (index B _))
  ; left-inv = record
    { ext = λ _ → refl S , refl S
    ; transport-ext-coh = λ _ _ →
      trans (index B _) (id-coh B) (id-coh B) ,
      trans (index A _) (id-coh A) (id-coh A) }
  ; right-inv = record
    { ext = λ _ → refl S , refl S
    ; transport-ext-coh = λ _ _ →
      (trans (index A _) (id-coh A) (id-coh A)) ,
      (trans (index B _) (id-coh B) (id-coh B)) }
  }
  where open SetoidFamily; open Setoid
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
