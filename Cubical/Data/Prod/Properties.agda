{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Prod.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Prod.Base
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

-- Swapping is an equivalence

swap : A × B → B × A
swap (x , y) = (y , x)

swap-invol : (xy : A × B) → swap (swap xy) ≡ xy
swap-invol (_ , _) = refl

isEquivSwap : (A : Type ℓ) (B : Type ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv (iso swap swap swap-invol swap-invol)

swapEquiv : (A : Type ℓ) (B : Type ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Type ℓ) (B : Type ℓ') → A × B ≡ B × A
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

-- equivalence between the sigma-based definition and the inductive one
A×B≃A×ΣB : A × B ≃ A ×Σ B
A×B≃A×ΣB = isoToEquiv (iso (λ { (a , b) → (a , b)})
                          (λ { (a , b) → (a , b)})
                          (λ _ → refl)
                          (λ { (a , b) → refl }))

A×B≡A×ΣB : A × B ≡ A ×Σ B
A×B≡A×ΣB = ua A×B≃A×ΣB

-- truncation for products
isOfHLevelProd : (n : ℕ) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A × B)
isOfHLevelProd {A = A} {B = B} n h1 h2 =
  let h : isOfHLevel n (A ×Σ B)
      h = isOfHLevelΣ n h1 (λ _ → h2)
  in transport (λ i → isOfHLevel n (A×B≡A×ΣB {A = A} {B = B} (~ i))) h


×-≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
    → A ≃ C → B ≃ D → A × B ≃ C × D
×-≃ {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
   where
    φ : A × B → C × D
    φ (a , b) = equivFun f a , equivFun g b

    ψ : C × D → A × B
    ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

    η : section φ ψ
    η (c , d) i = retEq f c i , retEq g d i

    ε : retract φ ψ
    ε (a , b) i = secEq f a i , secEq g b i
