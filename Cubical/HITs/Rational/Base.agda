{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Rational.Base where

open import Cubical.Relation.Nullary
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.Ints.QuoInt renaming (_*ℤ_ to _*_)
open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)

open import Cubical.Data.Nat hiding (_*_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Data.Nat.Coprime

-- ℚ as the set of coprime pairs in ℤ × ℕ₊₁

module Sigma where

  ℚ : Type₀
  ℚ = Σ[ (a , b) ∈ ℤ × ℕ₊₁ ] areCoprime (abs a , ℕ₊₁→ℕ b)

  [_/_] : ℤ → ℕ₊₁ → ℚ
  [ pos a / b ] = let (p , q) = toCoprime (a , b) in ((pos p , q) , toCoprimeAreCoprime (a , b))
  [ neg a / b ] = let (p , q) = toCoprime (a , b) in ((neg p , q) , toCoprimeAreCoprime (a , b))
  [ posneg i / b ] = ((posneg i , 1) , toCoprimeAreCoprime (0 , b))

-- ℚ as a set quotient of ℤ × ℕ₊₁ (from the HoTT book)

module Quo where

  ℚ : Type₀
  ℚ = (ℤ × ℕ₊₁) // (λ (a , 1+ b) (c , 1+ d) → a * pos (suc b) ≡ c * pos (suc d))

  [_/_] : ℤ → ℕ₊₁ → ℚ
  [ a / b ] = [ a , b ]

-- ℚ as a higher inductive type

module HIT where

  data ℚ : Type₀ where
    con : (u : ℤ) (a : ℤ) → ¬ (a ≡ pos 0) → ℚ
    path : ∀ u a v b {p q} → (u * b) ≡ (v * a) → con u a p ≡ con v b q
    trunc : isSet ℚ

  [_/_] : ℤ → ℕ₊₁ → ℚ
  [ a / 1+ b ] = con a (pos (suc b)) (snotz ∘ cong abs)
