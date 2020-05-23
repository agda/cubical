{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Sierpinski where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

-- Sierpinski set as defined by Veltri [0].
data Sierp : Type₀ where
  𝟏S     : Sierp
  𝟎S     : Sierp
  _∧S_   : Sierp → Sierp → Sierp
  ⋁S_    : (ℕ → Sierp) → Sierp

  comm   : (x y   : Sierp) → x ∧S y        ≡ y ∧S x
  assoc  : (x y z : Sierp) → x ∧S (y ∧S z) ≡ (x ∧S y) ∧S z
  idem   : (x     : Sierp) → x ∧S x        ≡ x
  id     : (x     : Sierp) → x ∧S 𝟏S       ≡ x
  ann    : (x     : Sierp) → x ∧S 𝟎S       ≡ 𝟎S

  ⋁-id   : (s : ℕ → Sierp) (n : ℕ)     → s n ∧S (⋁S s) ≡ s n
  dist   : (s : ℕ → Sierp) (x : Sierp) → (⋁S s) ∧S x ≡ ⋁S (λ n → s n ∧S x)

  isSetSierp : isSet Sierp

-- References
-- [0]:  http://cs.ioc.ee/ewscs/2017/studsess/veltri-slides.pdf
