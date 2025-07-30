{-

Mapping cones or the homotopy cofiber/cokernel

-}

module Cubical.HITs.MappingCones.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level

data Cone {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) : Type (ℓ-max ℓ ℓ') where
  inj   : Y → Cone f
  hub   : Cone f
  spoke : (x : X) → hub ≡ inj (f x)

-- the attachment of multiple mapping cones

data Cones {X : Type ℓ} {Y : Type ℓ'} (A : Type ℓ'') (f : A → X → Y) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  inj   : Y → Cones A f
  hub   : A → Cones A f
  spoke : (a : A) (x : X) → hub a ≡ inj (f a x)
