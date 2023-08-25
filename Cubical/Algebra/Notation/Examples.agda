module Cubical.Algebra.Notation.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Notation.Additive
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.CommMonoid.Notation
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Notation

private variable
  ℓ : Level

module _ (A : AbGroup ℓ) where
  instance _ = A

  _ : (x y : fst A) → x + y ≡ x
  _ = {!!}

{-
module _ (M : CommMonoid ℓ) where
  instance _ = M

  _ : (x y : fst M) → x + y ≡ y + x
  _ = {!!}
-}
