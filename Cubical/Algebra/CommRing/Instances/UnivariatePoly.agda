{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.UnivariatePoly where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.Univariate.Base
open import Cubical.Algebra.Polynomials.Univariate.Properties

private
  variable
    ℓ : Level

open CommRingStr

module _ (R : CommRing ℓ) where

  open PolyMod R
  open PolyModTheory R

  UnivariatePoly : CommRing ℓ
  fst UnivariatePoly = Poly R
  0r (snd UnivariatePoly) = 0P
  1r (snd UnivariatePoly) = 1P
  _+_ (snd UnivariatePoly) = _Poly+_
  _·_ (snd UnivariatePoly) = _Poly*_
  - snd UnivariatePoly = Poly-
  isCommRing (snd UnivariatePoly) = makeIsCommRing isSetPoly
                                    Poly+Assoc Poly+Rid Poly+Inverses Poly+Comm
                                    Poly*Associative Poly*Rid Poly*LDistrPoly+ Poly*Commutative


nUnivariatePoly : (A' : CommRing ℓ) → (n : ℕ) → CommRing ℓ
nUnivariatePoly A' zero = A'
nUnivariatePoly A' (suc n) = UnivariatePoly (nUnivariatePoly A' n)
