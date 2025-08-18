module Cubical.Data.Nat.Bijections.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Bijections.Triangle

Triangle⊂ℕ×ℕ≅ℕ×ℕ : Iso Triangle⊂ℕ×ℕ (ℕ × ℕ)
Iso.fun Triangle⊂ℕ×ℕ≅ℕ×ℕ (_ , k , m , _) = m , k
Iso.inv Triangle⊂ℕ×ℕ≅ℕ×ℕ (m , k)         = m + k , k , m , refl
Iso.rightInv Triangle⊂ℕ×ℕ≅ℕ×ℕ _ = refl
Iso.leftInv  Triangle⊂ℕ×ℕ≅ℕ×ℕ (n , k , m , p) = J
  (λ n q → (Iso.inv Triangle⊂ℕ×ℕ≅ℕ×ℕ (Iso.fun Triangle⊂ℕ×ℕ≅ℕ×ℕ (n , k , m , q))) ≡ (n , k , m , q)) refl p

ℕ×ℕ≅ℕ : Iso (ℕ × ℕ) ℕ
ℕ×ℕ≅ℕ = compIso (invIso Triangle⊂ℕ×ℕ≅ℕ×ℕ) Triangle⊂ℕ×ℕ≅ℕ
