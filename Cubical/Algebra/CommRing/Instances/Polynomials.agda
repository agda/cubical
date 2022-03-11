{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.Polynomials where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials

private
  variable
    ℓ : Level


Poly : (CommRing ℓ) → CommRing ℓ
Poly R = (PolyMod.Poly R) , str
    where
      open CommRingStr --(snd R)
      str : CommRingStr (PolyMod.Poly R)
      0r str = PolyMod.0P R
      1r str = PolyMod.1P R
      _+_ str = PolyMod._Poly+_ R
      _·_ str = PolyMod._Poly*_ R
      - str = PolyMod.Poly- R
      isCommRing str = makeIsCommRing (PolyMod.isSetPoly R)
                                      (PolyMod.Poly+Assoc R)
                                      (PolyMod.Poly+Rid R)
                                      (PolyMod.Poly+Inverses R)
                                      (PolyMod.Poly+Comm  R)
                                      (PolyMod.Poly*Associative R)
                                      (PolyMod.Poly*Rid R)
                                      (PolyMod.Poly*LDistrPoly+ R)
                                      (PolyMod.Poly*Commutative R)
