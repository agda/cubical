{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.UnivariatePoly where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.Univariate.Base
open import Cubical.Algebra.Polynomials.Univariate.Properties

private
  variable
    ℓ : Level


UnivariatePoly : (CommRing ℓ) → CommRing ℓ
UnivariatePoly R = (PolyMod.Poly R) , str
    where
      open CommRingStr --(snd R)
      str : CommRingStr (PolyMod.Poly R)
      0r str = PolyModTheory.0P R
      1r str = PolyModTheory.1P R
      _+_ str = PolyModTheory._Poly+_ R
      _·_ str = PolyModTheory._Poly*_ R
      - str = PolyModTheory.Poly- R
      isCommRing str = makeIsCommRing (PolyMod.isSetPoly R)
                                      (PolyModTheory.Poly+Assoc R)
                                      (PolyModTheory.Poly+Rid R)
                                      (PolyModTheory.Poly+Inverses R)
                                      (PolyModTheory.Poly+Comm  R)
                                      (PolyModTheory.Poly*Associative R)
                                      (PolyModTheory.Poly*Rid R)
                                      (PolyModTheory.Poly*LDistrPoly+ R)
                                      (PolyModTheory.Poly*Commutative R)
