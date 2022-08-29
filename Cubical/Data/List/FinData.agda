{-# OPTIONS --safe #-}
module Cubical.Data.List.FinData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat

variable
  ℓ : Level
  A B : Type ℓ

-- copy-paste from agda-stdlib
lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero ^a = []
tabulate (suc n) ^a = ^a zero ∷ tabulate n (^a ∘ suc)

length-tabulate : ∀ n → (^a : Fin n → A) → length (tabulate n ^a) ≡ n
length-tabulate zero ^a = refl
length-tabulate (suc n) ^a = cong suc (length-tabulate n (^a ∘ suc))

tabulate-lookup : ∀ (xs : List A) → tabulate (length xs) (lookup xs) ≡ xs
tabulate-lookup [] = refl
tabulate-lookup (x ∷ xs) = cong (x ∷_) (tabulate-lookup xs)

lookup-tabulate : ∀ n → (^a : Fin n → A)
  → PathP (λ i → (Fin (length-tabulate n ^a i) → A)) (lookup (tabulate n ^a)) ^a
lookup-tabulate (suc n) ^a i zero = ^a zero
lookup-tabulate (suc n) ^a i (suc p) = lookup-tabulate n (^a ∘ suc) i p

lookup-map : ∀ (f : A → B) (xs : List A)
  → (p0 : Fin (length (map f xs)))
  → (p1 : Fin (length xs))
  → (p : PathP (λ i → Fin (length-map f xs i)) p0 p1)
  → lookup (map f xs) p0 ≡ f (lookup xs p1)
lookup-map f (x ∷ xs) zero zero p = refl
lookup-map f (x ∷ xs) zero (suc p1) p = ⊥.rec (znotsP p)
lookup-map f (x ∷ xs) (suc p0) zero p = ⊥.rec (snotzP p)
lookup-map f (x ∷ xs) (suc p0) (suc p1) p = lookup-map f xs p0 p1 (injSucFinP p)
