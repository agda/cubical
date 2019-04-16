{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Relation.Nullary

NonZero : ℕ → Type₀
NonZero 0 = ⊥
NonZero _ = ⊤

private
  variable
    ℓ : Level
    k : ℕ

-- The Modulo type is similar to the Fin type, but instead of being
-- inhabited by canonical values, the inhabitants are all naturals,
-- and paths are added between numbers that have the same residue.
--
-- This representation makes it easier to do certain arithmetic
-- without changing the modulus. For instance, we can just add any
-- natural to a Modulo k to get another, whereas with Fin k, we must
-- calculate the canonical representative.
--
-- The reason the path constructor is guarded is to avoid adding
-- non-trivial path structure to the k=0 case. If it were not guarded,
-- each `Modulo 0` would become like the circle, and guarding the
-- constructor is somewhat easier to work with than truncation.
--
-- Note also that unlike `Fin 0`, `Modulo 0` is equivalent to the naturals.
data Modulo (k : ℕ) : Type₀ where
  embed : (n : ℕ) → Modulo k
  pre-step : NonZero k → (n : ℕ) → embed n ≡ embed (k + n)

-- When we are working with k = suc k₀, the `step` alias is much
-- we can use this alias.
pattern step n i = pre-step _ n i

-- Helper to avoid having to case on `k` in certain places.
ztep : ∀{k} n → Path (Modulo k) (embed n) (embed (k + n))
ztep {0}     n = refl
ztep {suc k} n = step n

-- The standard eliminator for `Modulo`.
elim
  : (P : ∀ k → Modulo k → Type ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P (suc k) (step n i)) (e (suc k) n) (e (suc k) (suc k + n)))
  → (m : Modulo k) → P k m
elim P e st (embed n) = e _ n
elim {k = suc k} P e st (step n i) = st k n i
