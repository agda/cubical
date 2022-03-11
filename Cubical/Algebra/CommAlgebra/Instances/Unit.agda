{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.CommAlgebra

private
  variable
    ℓ ℓ' : Level

open CommAlgebraStr

module _ (R : CommRing ℓ) where

  UnitCommAlgebra : CommAlgebra R ℓ'
  UnitCommAlgebra = commAlgebraFromCommRing
      UnitCommRing
      (λ _ _ → tt*) (λ _ _ _ → refl) (λ _ _ _ → refl)
      (λ _ _ _ → refl) (λ _ → refl) (λ _ _ _ → refl)
