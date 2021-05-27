{-# OPTIONS --safe #-}
module Cubical.HITs.Nullification.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv

isNull : ∀ {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') → Type (ℓ-max ℓ ℓ')
isNull S A = isPathSplitEquiv (const {A = A} {B = S})

data Null {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  ∣_∣ : A → Null S A
  -- the image of every map (S → Null S A) is contractible in Null S A
  hub   : (f : S → Null S A) → Null S A
  spoke : (f : S → Null S A) (s : S) → hub f ≡ f s
  -- the image of every map (S → x ≡ y) for x y : A is contractible in x ≡ y
  ≡hub   : ∀ {x y} (p : S → x ≡ y) → x ≡ y
  ≡spoke : ∀ {x y} (p : S → x ≡ y) (s : S) → ≡hub p ≡ p s

isNull-Null : ∀ {ℓ ℓ'} {S : Type ℓ} {A : Type ℓ'} → isNull S (Null S A)
fst (sec isNull-Null) f     = hub   f
snd (sec isNull-Null) f i s = spoke f s i
fst (secCong isNull-Null x y) p i     = ≡hub   (funExt⁻ p) i
snd (secCong isNull-Null x y) p i j s = ≡spoke (funExt⁻ p) s i j
