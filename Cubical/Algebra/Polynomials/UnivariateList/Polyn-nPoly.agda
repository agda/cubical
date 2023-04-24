{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.UnivariateList.Polyn-nPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.Poly0-A
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[Am[X]]-Anm[X]
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.AB-An[X]Bn[X]
open import Cubical.Algebra.Polynomials.UnivariateList.Poly1-1Poly

open CommRingEquivs renaming (compCommRingEquiv to _∘-ecr_ ; invCommRingEquiv to inv-ecr)

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Definition

Equiv-Polyn-nPoly : (A' : CommRing ℓ) → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (nUnivariatePolyList A' n)
Equiv-Polyn-nPoly A' zero = CRE-Poly0-A A'
Equiv-Polyn-nPoly A' (suc n) =       inv-ecr _ _ (CRE-PolyN∘M-PolyN+M A' 1 n)
                               ∘-ecr (lift-equiv-poly _ _ 1 (Equiv-Polyn-nPoly A' n)
                               ∘-ecr CRE-Poly1-Poly: (nUnivariatePolyList A' n))
