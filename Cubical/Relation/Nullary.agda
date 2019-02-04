{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary where

open import Cubical.Core.Everything

open import Cubical.Data.Empty

-- Negation
infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

isProp¬ : ∀ {ℓ} → (A : Set ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

-- Decidable types (inspired by standard library)
data Dec {ℓ} (P : Set ℓ) : Set ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Stable : ∀ {ℓ} → Set ℓ → Set ℓ
Stable A = ¬ ¬ A → A

Discrete : ∀ {ℓ} → Set ℓ → Set ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
