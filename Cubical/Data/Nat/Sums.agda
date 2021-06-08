{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Sums where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    l m n : ℕ

∑ₖ₌₁^ : (n : ℕ) → Vec ℕ n → ℕ
∑ₖ₌₁^ n = foldr (_+_) zero

-- some helpful laws:
∑Scalar : ∀ {n : ℕ} (x : ℕ) (xs : Vec ℕ n) → x · ∑ₖ₌₁^ n xs ≡ ∑ₖ₌₁^ n (map (x ·_) xs)
∑Scalar {n = zero} x [] = ·-comm x zero
∑Scalar {n = suc n} x (y ∷ xs) = sym (·-distribˡ x y _) ∙ cong ((x · y) +_) (∑Scalar x xs)

∑Assoc : ∀ {n : ℕ} (xs ys : Vec ℕ n) → ∑ₖ₌₁^ n (zipWith (_+_) xs ys) ≡ ∑ₖ₌₁^ (n + n) (xs ++ ys)
∑Assoc xs ys = foldrZipWith≡foldr++.thm _ _ +-assoc +-comm xs ys

-- vector that stores (n choose k) · x ^ (n ∸ k) · y ^ k for k = 0,...,n
-- BinomialVec : (n : ℕ) (x y : ℕ) → Vec ℕ (suc n)
-- BinomialVec zero x y = zero ∷ []
-- BinomialVec (suc n) x y = {!!}

-- most general:
-- bigOp : {M : RawMonoid} {n : ℕ} → (xs : (Σ[ k ∈ ℕ ] k < n) → M) → M
-- use this Fin instead of FinData!!!
