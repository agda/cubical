{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary where

open import Cubical.Core.Everything

open import Cubical.Data.Empty

private
  variable
    ℓ  : Level
    
-- Negation
infix 3 ¬_

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

isProp¬ : (A : Set ℓ) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

-- Decidable types (inspired by standard library)
data Dec (P : Set ℓ) : Set ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Stable : Set ℓ → Set ℓ
Stable A = ¬ ¬ A → A

Discrete : Set ℓ → Set ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
