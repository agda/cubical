{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (f₁,⋯,fₘ) → R[X₁,⋯,Xₙ] → A → 0

  (where f₁,⋯,fₘ ∈ R[X₁,⋯,Xₙ])
  Our definition is more explicit.
-}
module Cubical.Algebra.CommAlgebra.FP where

open import Cubical.Algebra.CommAlgebra.FP.Base public
open import Cubical.Algebra.CommAlgebra.FP.Properties public
