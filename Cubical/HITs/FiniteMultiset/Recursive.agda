{-# OPTIONS --safe #-}
module Cubical.HITs.FiniteMultiset.Recursive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (_×_) renaming (_,_ to _,,_)
open import Cubical.Data.Nat using (ℕ; isSetℕ; _+_; +-comm)
open import Cubical.HITs.UnorderedPair

private variable
  ℓ : Level
  A : Type ℓ

pattern ,_ x = _,,_ _ x

+-commPair : UnorderedPair (A × ℕ) → ℕ
+-commPair = rec isSetℕ (λ (, x) (, y) → x + y) λ (, x) (, y) → +-comm x y

data FMSet (A : Type ℓ) : ℕ → Type ℓ where
  [_] : A → FMSet A 1
  _++_ : (xs : UnorderedPair (A × ℕ)) → FMSet A (+-commPair xs)
