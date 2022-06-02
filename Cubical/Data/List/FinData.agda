{-# OPTIONS --safe #-}
module Cubical.Data.List.FinData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.Empty as ⊥

variable
  ℓ : Level
  A B : Type ℓ

-- copy-paste from agda-stdlib
lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

lookup-map : ∀ (f : A → B) (xs : List A)
  → (p0 : Fin (length (map f xs)))
  → (p1 : Fin (length xs))
  → (p : PathP (λ i → Fin (length-map f xs i)) p0 p1)
  → lookup (map f xs) p0 ≡ f (lookup xs p1)
lookup-map f (x ∷ xs) zero zero p = refl
lookup-map f (x ∷ xs) zero (suc p1) p = ⊥.rec (znotsP p)
lookup-map f (x ∷ xs) (suc p0) zero p = ⊥.rec (snotzP p)
lookup-map f (x ∷ xs) (suc p0) (suc p1) p = lookup-map f xs p0 p1 (injSucFinP p)
