{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRing.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sum

open import Cubical.Algebra.Ring

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.CohomologyRing.CohomologyRing

open import Cubical.HITs.Sn
open import Cubical.ZCohomology.Groups.Sn

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- Lemma

H*Sn : Type ℓ-zero
H*Sn = H* (S (-1+ 12))


