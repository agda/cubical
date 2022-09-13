{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

private variable
  ℓ : Level

module _ (R : CommRing ℓ) where
  open CommRingStr ⦃...⦄
  open PolyModTheory R
  private
    ListPoly = UnivariatePolyList R
    instance
      _ = snd ListPoly
      _ = snd R

  ListPolyCommAlgebra : CommAlgebra R ℓ
  ListPolyCommAlgebra =
    Iso.inv (CommAlgChar.CommAlgIso R)
            (ListPoly ,
             constantPolynomialHom R)
