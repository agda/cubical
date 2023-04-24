{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.UnivariateFun.Polyn-nPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.DirectSumFun
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyHIT
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyFun
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.Poly0-A
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[Am[X]]-Anm[X]
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.AB-An[X]Bn[X]
open import Cubical.Algebra.Polynomials.UnivariateHIT.Polyn-nPoly

open CommRingEquivs renaming (compCommRingEquiv to _∘-ecr_ ; invCommRingEquiv to inv-ecr)

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Definition

Equiv1 : (A' : CommRing ℓ) → CommRingEquiv (nUnivariatePolyHIT A' 1) (nUnivariatePolyFun A' 1)
Equiv1 A' = CommRingEquiv-DirectSumGradedRing _ _ _  _ _ _ _ _ _ _ _ _ _ _ _

Equiv-Polyn-nPolyFun : (A' : CommRing ℓ) → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (nUnivariatePolyFun A' n)
Equiv-Polyn-nPolyFun A' zero = CRE-Poly0-A A'
Equiv-Polyn-nPolyFun A' (suc n) =       inv-ecr _ _ (CRE-PolyN∘M-PolyN+M A' 1 n)
                               ∘-ecr (lift-equiv-poly _ _ 1 (Equiv-Polyn-nPolyFun A' n)
                               ∘-ecr (Equiv-Polyn-nPolyHIT (nUnivariatePolyFun A' n) 1
                                     ∘-ecr Equiv1 (nUnivariatePolyFun A' n)))
