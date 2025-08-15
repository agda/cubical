module Cubical.Data.Nat.MoreOrderProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open <-Reasoning
open import Cubical.Tactics.NatSolver

<SumLeft : {n k : ℕ} → n < n + suc k
<SumLeft {n} {k} = k , +-suc k n ∙ +-comm (suc k) n

<SumRight : {n k : ℕ} → n < suc k + n
<SumRight {n} {k} = k , +-suc k n

<-suc : {n : ℕ} → n < suc n
<-suc = 0 , refl

=→≤ : {m n : ℕ} → m ≡ n → m ≤ n
=→≤ p = 0 , p
