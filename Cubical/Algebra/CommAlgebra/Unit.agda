{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra

private
  variable
    ℓ ℓ' : Level

open CommAlgebraStr

module _ (R : CommRing ℓ) where

  UnitCommAlgebra : CommAlgebra R ℓ'
  fst UnitCommAlgebra = Unit*
  0a (snd UnitCommAlgebra) = tt*
  1a (snd UnitCommAlgebra) = tt*
  _+_ (snd UnitCommAlgebra) = λ _ _ → tt*
  _·_ (snd UnitCommAlgebra) = λ _ _ → tt*
  - snd UnitCommAlgebra = λ _ → tt*
  _⋆_ (snd UnitCommAlgebra) = λ _ _ → tt*
  isCommAlgebra (snd UnitCommAlgebra) = makeIsCommAlgebra isSetUnit*
       (λ _ _ _ → refl) (λ { tt* → refl }) (λ _ → refl) (λ _ _ → refl)
       (λ _ _ _ → refl) (λ { tt* → refl }) (λ _ _ _ → refl) (λ _ _ → refl)
       (λ _ _ _ → refl) (λ _ _ _ → refl)
       (λ _ _ _ → refl) (λ { tt* → refl }) (λ _ _ _ → refl)
