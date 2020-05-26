{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Sierpinski where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

-- Sierpinski set as defined by Veltri [0].
data Sierp (ℓ : Level) : Type ℓ where
  𝟏S     : Sierp ℓ
  𝟎S     : Sierp ℓ
  _∧S_   : Sierp ℓ → Sierp ℓ → Sierp ℓ
  ⋁S_    : (ℕ → Sierp ℓ) → Sierp ℓ

  comm   : (x y   : Sierp ℓ) → x ∧S y        ≡ y ∧S x
  assoc  : (x y z : Sierp ℓ) → x ∧S (y ∧S z) ≡ (x ∧S y) ∧S z
  idem   : (x     : Sierp ℓ) → x ∧S x        ≡ x
  id     : (x     : Sierp ℓ) → x ∧S 𝟏S       ≡ x
  ann    : (x     : Sierp ℓ) → x ∧S 𝟎S       ≡ 𝟎S

  ⋁-id   : (s : ℕ → Sierp ℓ) (n : ℕ)     → s n ∧S (⋁S s) ≡ s n
  dist   : (s : ℕ → Sierp ℓ) (x : Sierp ℓ) → (⋁S s) ∧S x ≡ ⋁S (λ n → s n ∧S x)

  isSetSierp : isSet (Sierp ℓ)

-- References
-- [0]: http://cs.ioc.ee/ewscs/2017/studsess/veltri-slides.pdf
