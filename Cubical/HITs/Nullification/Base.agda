{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Nullification.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.PathSplitEquiv
open isPathSplitEquiv

isNull : ∀ {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') → Type (ℓ-max ℓ ℓ')
isNull S A = isPathSplitEquiv (const {A = A} {B = S}) -- isEquiv (const : A → (S → A))

data Null {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  ∣_∣ : A → Null S A
  -- const : Null S A → (S → Null S A) is a path-split equivalence
  ext   : (f : S → Null S A) → Null S A
  isExt : (f : S → Null S A) (s : S) → ext f ≡ f s
  ≡ext   : ∀ {x y} (p : S → x ≡ y) → x ≡ y
  ≡isExt : ∀ {x y} (p : S → x ≡ y) (s : S) → ≡ext p ≡ p s

isNull-Null : ∀ {ℓ ℓ'} {S : Type ℓ} {A : Type ℓ'} → isNull S (Null S A)
fst (sec isNull-Null) f     = ext   f
snd (sec isNull-Null) f i s = isExt f s i
fst (secCong isNull-Null x y) p i     = ≡ext   (appl p) i
snd (secCong isNull-Null x y) p i j s = ≡isExt (appl p) s i j
