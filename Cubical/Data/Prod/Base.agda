{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Prod.Base where

open import Cubical.Core.Everything

-- If × is defined using Σ then transp/hcomp will be compute
-- "negatively", that is, they won't reduce unless we project out the
-- first of second component. This is not always what we want so the
-- default implementation is done using a datatype which computes
-- positively.

data _×_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  _,_ : A → B → A × B

infixr 5 _×_

-- We still export the version using Σ
_×Σ_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ×Σ B = Σ A (λ _ → B)

infixr 5 _×Σ_
