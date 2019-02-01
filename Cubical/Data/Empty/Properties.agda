{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Empty.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Empty.Base

isProp⊥ : isProp ⊥
isProp⊥ x = ⊥-elim x

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥

isProp¬ : ∀ {l} → (A : Set l) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i
