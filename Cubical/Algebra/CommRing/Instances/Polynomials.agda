{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.Polynomials where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials

private
  variable
    ℓ : Level


ℙ : (R : CommRing ℓ) → CommRing ℓ
ℙ R = (PolyMod.Poly R) , str
    where
      open CommRingStr (snd R)
      str : CommRingStr (PolyMod.Poly R)
      CommRingStr.0r str = PolyMod.0P R
      CommRingStr.1r str = PolyMod.1P R
      CommRingStr._+_ str = PolyMod._Poly+_ R
      CommRingStr._·_ str = PolyMod._Poly*_ R
      CommRingStr.- str = PolyMod.Poly- R
      CommRingStr.isCommRing str = makeIsCommRing (PolyMod.PolyIsSet R)
                                                  (PolyMod.Poly+Assoc R)
                                                  (PolyMod.Poly+Rid R)
                                                  (PolyMod.Poly+Inverses R)
                                                  (PolyMod.Poly+Comm  R)
                                                  (PolyMod.Poly*Associative R)
                                                  (PolyMod.Poly*Rid R)
                                                  (PolyMod.Poly*LDistrPoly+ R)
                                                  (PolyMod.Poly*Commutative R)
