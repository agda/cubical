{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv-Polyn-nPoly where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Univariate.Base
open import Cubical.Algebra.CommRing.Instances.UnivariatePoly

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open import Cubical.Algebra.Polynomials.Multivariate.Equiv.Poly0-A
open import Cubical.Algebra.Polynomials.Multivariate.Equiv.Poly1-Poly
open import Cubical.Algebra.Polynomials.Multivariate.Equiv.Comp-Poly
open import Cubical.Algebra.Polynomials.Multivariate.Equiv.Induced-Poly


open Nth-Poly-structure
open CommRingEquivs renaming (compCommRingEquiv to _∘-ecr_ ; invCommRingEquiv to inv-ecr)

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Definition

nPoly : (A' : CommRing ℓ) → (n : ℕ) → CommRing ℓ
nPoly A' zero = A'
nPoly A' (suc n) = UnivariatePoly (nPoly A' n)

Equiv-Polyn-nPoly : (A' : CommRing ℓ) → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (nPoly A' n)
Equiv-Polyn-nPoly A' zero = CRE-Poly0-A A'
Equiv-Polyn-nPoly A' (suc n) = inv-ecr _ _ (CRE-PolyN∘M-PolyN+M A' 1 n)
                               ∘-ecr (lift-equiv-poly _ _ (Equiv-Polyn-nPoly A' n) 1
                               ∘-ecr CRE-Poly1-Poly: (nPoly A' n))
