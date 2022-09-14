{-# OPTIONS --safe #-}
module Cubical.HITs.FiniteMultiset.Recursive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Nat using (ℕ; isSetℕ; _+_; +-comm)
open import Cubical.HITs.UnorderedPair

private variable
  ℓ : Level
  A : Type ℓ

+-commPair : UnorderedPair (A × ℕ) → ℕ
+-commPair = rec isSetℕ (λ (_ , x) (_ , y) → x + y) λ (_ , x) (_ , y) → +-comm x y

data FMSet (A : Type ℓ) : ℕ → Type ℓ where
  [_] : A → FMSet A 1
  _++_ : (xs : UnorderedPair (A × ℕ)) → FMSet A (+-commPair xs)
