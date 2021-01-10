{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Utility where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra.Base using (algebrahom)
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Morphism
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Examples

private
  variable
    ℓ : Level

asFunction : {R : CommRing {ℓ}}
             → (f : CommAlgebra.Carrier (R [ Unit* ]))
             → fst R → fst R
asFunction {R = R} P x =
  let
    RasAlgebra = (CommAlgebraExamples.initial R)
    evaluationHom : CAlgHom (R [ Unit* ]) RasAlgebra
    evaluationHom = inducedHom RasAlgebra (λ _ → x)
  in AlgebraHom.map evaluationHom P

