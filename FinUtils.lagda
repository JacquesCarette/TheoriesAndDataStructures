\section{|FinUtils|}

\begin{code}
module FinUtils where

open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Maybe as Maybe
open import Data.Product using ( _×_ ; _,_ )
\end{code}

\begin{code}
suc′ : {n : ℕ} → Fin n → Maybe (Fin n)
suc′ {zero} ()
suc′ {suc zero} zero = nothing
suc′ {suc zero} (suc ())
suc′ {suc (suc n)} zero = just (suc zero)
suc′ {suc (suc n)} (suc i) = Maybe.map suc (suc′ i)
\end{code}

\begin{code}
infixl 6 _+′_

sucWithCarry : {n : ℕ} → Bool × Fin n → Bool × Fin n
sucWithCarry {zero} (_ , ())
sucWithCarry {suc n} (b , k) = maybe (λ j′ → b , j′) (true , zero) (suc′ k)

sucWithCarryIter : {n : ℕ} → ℕ → Bool × Fin n → Bool × Fin n
sucWithCarryIter zero p = p
sucWithCarryIter (suc k) p = sucWithCarryIter k (sucWithCarry p)

_+′_ : {n : ℕ} → Fin n → Fin n → Bool × Fin n
i +′ j = sucWithCarryIter (toℕ i) (false , j)
\end{code}
