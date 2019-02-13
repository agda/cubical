{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Prod.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Prod.Base

open import Cubical.Foundations.Equiv

variable
  ℓ ℓ' : Level

proj₁ : {A : Set ℓ} {B : Set ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {A : Set ℓ} {B : Set ℓ'} → A × B → B
proj₂ (_ , x) = x

-- Swapping is an equivalence

swap : {A : Set ℓ} {B : Set ℓ'} → A × B → B × A
swap (x , y) = (y , x)

swapInv : {A : Set ℓ} {B : Set ℓ'} → (xy : A × B) → swap (swap xy) ≡ xy
swapInv (_ , _) = refl

isEquivSwap : (A : Set ℓ) (B : Set ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv (iso swap swap swapInv swapInv)

swapEquiv : (A : Set ℓ) (B : Set ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Set ℓ) (B : Set ℓ') → A × B ≡ B × A
swapEq A B = ua (swapEquiv A B)

private
  open import Cubical.Data.Nat

  -- As × is defined as a datatype this computes as expected
  -- (i.e. "C-c C-n test1" reduces to (2 , 1)). If × is implemented
  -- using Sigma this would be "transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)"
  test : ℕ × ℕ
  test = transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)

  testrefl : test ≡ (2 , 1)
  testrefl = refl
