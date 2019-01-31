{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Empty.Empty where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()

isProp⊥ : isProp ⊥
isProp⊥ x = ⊥-elim x

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥

isProp¬ : ∀ {l} → (A : Set l) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

