{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
  terminalCAlg : CommAlgebra R ℓ
  terminalCAlg = Unit* , commAlgStr
    where open CommAlgebraStr

          commAlgStr : CommAlgebraStr R Unit*
          0a commAlgStr = tt*
          1a commAlgStr = tt*
          _+_ commAlgStr = λ _ _ → tt*
          _·_ commAlgStr = λ _ _ → tt*
          - commAlgStr = λ _ → tt*
          _⋆_ commAlgStr = λ _ _ → tt*
          isCommAlgebra commAlgStr = makeIsCommAlgebra isSetUnit*
                                       (λ _ _ _ → refl) (λ _ → refl)
                                       (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
                                       (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl)
                                       (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl)
                                       (λ _ → refl) λ _ _ _ → refl
