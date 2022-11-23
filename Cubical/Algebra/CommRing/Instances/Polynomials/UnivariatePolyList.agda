{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

private
  variable
    ℓ : Level

open CommRingStr

module _ (R : CommRing ℓ) where

  open PolyMod R
  open PolyModTheory R

  UnivariatePolyList : CommRing ℓ
  fst UnivariatePolyList = Poly R
  0r (snd UnivariatePolyList) = 0P
  1r (snd UnivariatePolyList) = 1P
  _+_ (snd UnivariatePolyList) = _Poly+_
  _·_ (snd UnivariatePolyList) = _Poly*_
  - snd UnivariatePolyList = Poly-
  isCommRing (snd UnivariatePolyList) = makeIsCommRing isSetPoly
                                    Poly+Assoc Poly+Rid Poly+Inverses Poly+Comm
                                    Poly*Associative Poly*Rid Poly*LDistrPoly+ Poly*Commutative


  constantPolynomialHom : CommRingHom R UnivariatePolyList
  constantPolynomialHom = [_] ,
                          makeIsRingHom
                            refl
                            (λ r s → refl)
                            λ r s → sym (MultHom[-] r s)


nUnivariatePolyList : (A' : CommRing ℓ) → (n : ℕ) → CommRing ℓ
nUnivariatePolyList A' zero = A'
nUnivariatePolyList A' (suc n) = UnivariatePolyList (nUnivariatePolyList A' n)
