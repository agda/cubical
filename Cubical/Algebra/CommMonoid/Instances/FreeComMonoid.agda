module Cubical.Algebra.CommMonoid.Instances.FreeComMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.FreeComMonoids

open import Cubical.Algebra.CommMonoid.Base

private variable
  ℓ : Level

FCMCommMonoid : {A : Type ℓ} → CommMonoid ℓ
FCMCommMonoid {A = A} = makeCommMonoid {M = FreeComMonoid A} ε _·_ trunc assoc identityᵣ comm
