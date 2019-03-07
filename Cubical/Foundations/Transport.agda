{- Basic theory about transport:

- transport is invertible
- transport is an equivalence ([transportEquiv])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Transport where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv

transport⁻ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
transport⁻ p = transport (λ i → p (~ i))

transport⁻Transport : ∀ {ℓ} {A B : Set ℓ} → (p : A ≡ B) → (a : A) →
                          transport⁻ p (transport p a) ≡ a
transport⁻Transport p a j =
  transp (λ i → p (~ i ∧ ~ j)) j (transp (λ i → p (i ∧ ~ j)) j a)

transportTransport⁻ : ∀ {ℓ} {A B : Set ℓ} → (p : A ≡ B) → (b : B) →
                        transport p (transport⁻ p b) ≡ b
transportTransport⁻ p b j =
  transp (λ i → p (i ∨ j)) j (transp (λ i → p (~ i ∨ j)) j b)

-- Transport is an equivalence
isEquivTransport : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} {B = B} p =
  transport (λ i → isEquiv (λ x → transp (λ j → p (i ∧ j)) (~ i) x)) (idIsEquiv A)

transportEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
transportEquiv p = (transport p , isEquivTransport p)
