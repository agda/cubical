{-

Proof of some groupoid laws for equality

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.GroupoidLaws2 where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

-- shortcut for the composition

_·_ : {ℓ : Level} → {A : Set ℓ} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
x≡y · y≡z = compPath x≡y y≡z

infixl 30 _·_
