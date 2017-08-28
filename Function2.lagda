\section{Function2}

\begin{code}
module Function2 where

-- should be defined in Function ?
infix 4 _$ᵢ

_$ᵢ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → {x : A} → B x
_$ᵢ f {x} = f x
\end{code}
