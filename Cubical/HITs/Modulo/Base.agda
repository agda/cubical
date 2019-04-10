{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Modulo.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Relation.Nullary

NonZero : ℕ → Set
NonZero 0 = ⊥
NonZero _ = ⊤

private
  variable
    ℓ : Level
    k : ℕ

data Modulo (k : ℕ) : Set where
  embed : (n : ℕ) → Modulo k
  pre-step : NonZero k → (n : ℕ) → embed n ≡ embed (k + n)

pattern step n i = pre-step _ n i

ztep : ∀{k} n → Path (Modulo k) (embed n) (embed (k + n))
ztep {0}     n = refl
ztep {suc k} n = step n

elim
  : (P : ∀ k → Modulo k → Set ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P (suc k) (step n i)) (e (suc k) n) (e (suc k) (suc k + n)))
  → (m : Modulo k) → P k m
elim P e st (embed n) = e _ n
elim {k = suc k} P e st (step n i) = st k n i
