{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Stream.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream

mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)

even : ∀ {A} → Stream A → Stream A
head (even a) = head a
tail (even a) = even (tail (tail a))

odd : ∀ {A} → Stream A → Stream A
head (odd a) = head (tail a)
tail (odd a) = odd (tail (tail a))

merge : ∀ {A} → Stream A → Stream A → Stream A
head (merge a _) = head a
head (tail (merge _ b)) = head b
tail (tail (merge a b)) = merge (tail a) (tail b)

-- Bisimulation
record _≈_ {A : Set} (x y : Stream A) : Set where
  coinductive
  field
    ≈head : head x ≡ head y
    ≈tail : tail x ≈ tail y

lookup : {A : Set} → Stream A → ℕ → A
lookup xs zero = head xs
lookup xs (suc n) = lookup (tail xs) n

tabulate : {A : Set} → (ℕ → A) → Stream A
head (tabulate f) = f zero
tail (tabulate f) = tabulate (λ n → f (suc n))
