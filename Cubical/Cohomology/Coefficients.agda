{-
  Covariant functoriality of cohomology in morphisms of coefficients
-}
{-# OPTIONS --safe #-}
module Cubical.Cohomology.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Int.Base hiding (_·_)
open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.SetTruncation hiding (map)

open import Cubical.Homotopy.Spectrum
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Loopspace

open import Cubical.Cohomology.Base

{-
  Functoriality of cohomology with respect to morphism of
  dependent spectra.
-}

private
  variable
    ℓ : Level
    X : Type ℓ
    A B : (x : X) → Spectrum ℓ

CohomCoeffMap : (f : (x : X) → A x →ₛ B x) (k : ℤ)
              → (CohomClasses X A k) →∙ (CohomClasses X B k)
CohomCoeffMap f k = (λ χ → λ x → fst (fst (f x) k) (χ x)) ,
                    λ i x → snd (fst (f x) k) i
