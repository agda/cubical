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

Zero : ℕ → Set
Zero 0 = ⊤
Zero _ = ⊥

private
  variable
    ℓ : Level
    k : ℕ

assertZero : Zero k → 0 ≡ k
assertZero {zero} _ = refl
assertZero {suc _} ()

data Modulo (k : ℕ) : Set where
  embed : (n : ℕ) → Modulo k
  step : (n : ℕ) → embed n ≡ embed (k + n)
  squash
    : ∀(z : Zero k) n
    → PathP (λ i → embed n ≡ embed (assertZero z i + n)) refl (step n)

Square
  : (P : ∀ k → Modulo k → Set ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P k (step n i)) (e k n) (e k (k + n)))
  → ℕ → Set ℓ
Square P e st n
  = PathP (λ i → PathP (λ j → P 0 (squash _ n i j)) (e 0 n) (e 0 n)) refl (st 0 n)

elim
  : (P : ∀ k → Modulo k → Set ℓ)
  → (e : ∀ k n → P k (embed n))
  → (st : ∀ k n → PathP (λ i → P k (step n i)) (e k n) (e k (k + n)))
  → (sq : ∀ n → Square P e st n)
  → (m : Modulo k) → P k m
elim P e st sq (embed n) = e _ n
elim P e st sq (step n i) = st _ n i
elim {k = 0} P e st sq (squash z n i j) = sq n i j

