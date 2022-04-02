{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties

private variable
  ℓ ℓ' : Level


module _ (A' : CommRing ℓ) (n : ℕ) where

  private
    A = fst A'
    Ar = CommRing→Ring A'

  open CommRingStr
  open RingTheory Ar
  open Nth-Poly-structure A' n

  PolyCommRing : CommRing ℓ
  fst PolyCommRing = Poly A' n
  0r (snd PolyCommRing) = 0P
  1r (snd PolyCommRing) = 1P
  _+_ (snd PolyCommRing) = _Poly+_
  _·_ (snd PolyCommRing) = _Poly*_
  - snd PolyCommRing = Poly-inv
  isCommRing (snd PolyCommRing) = makeIsCommRing
                                  trunc
                                  Poly+-assoc
                                  Poly+-Rid
                                  Poly+-rinv
                                  Poly+-comm
                                  Poly*-assoc
                                  Poly*-Rid
                                  Poly*-Rdist
                                  Poly*-comm
