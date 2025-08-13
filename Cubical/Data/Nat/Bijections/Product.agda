{-# OPTIONS --cubical #-}

module Cubical.Data.Nat.Bijections.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Bijections.FinN

Finℕ≅ℕ×ℕ : Iso Finℕ (ℕ × ℕ)
Iso.fun Finℕ≅ℕ×ℕ (_ , k , m , _) = m , k
Iso.inv Finℕ≅ℕ×ℕ (m , k)         = m + k , k , m , refl
Iso.rightInv Finℕ≅ℕ×ℕ _ = refl
Iso.leftInv  Finℕ≅ℕ×ℕ (n , k , m , p) = J
  (λ { n q → (Iso.inv Finℕ≅ℕ×ℕ (Iso.fun Finℕ≅ℕ×ℕ (n , k , m , q))) ≡ (n , k , m , q) }) refl p

ℕ×ℕ≅ℕ : Iso (ℕ × ℕ) ℕ
ℕ×ℕ≅ℕ = compIso (invIso Finℕ≅ℕ×ℕ) Finℕ≅ℕ
