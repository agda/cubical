{-# OPTIONS --no-exact-split --safe #-}

module Cubical.Data.InfNat.Properties where

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.InfNat.Base
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Empty

fromInf-def : ℕ → ℕ+∞ → ℕ
fromInf-def n ∞ = n
fromInf-def _ (fin n) = n

fin-inj : (n m : ℕ) → fin n ≡ fin m → n ≡ m
fin-inj x _ eq = cong (fromInf-def x) eq

discreteInfNat : Discrete ℕ+∞
discreteInfNat ∞ ∞ = yes (λ i → ∞)
discreteInfNat ∞ (fin _) = no λ p → subst (caseInfNat ⊥ Unit) p tt
discreteInfNat (fin _) ∞ = no λ p → subst (caseInfNat Unit ⊥) p tt
discreteInfNat (fin n) (fin m) with ℕ.discreteℕ n m
discreteInfNat (fin n) (fin m) | yes p = yes (cong fin p)
discreteInfNat (fin n) (fin m) | no ¬p = no (λ p → ¬p (fin-inj n m p))
