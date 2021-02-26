{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (a₁,⋯,aₘ) → R[X₁,⋯,Xₙ] → A → 0
-}
{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal

private
  variable
    ℓ : Level

module _ {R : CommRing {ℓ}} where
  freeAlgebra : (n : ℕ) → CommAlgebra R
  freeAlgebra n = R [ Lift (Fin n) ]

  makeFPAlgebra : {m : ℕ} (n : ℕ) (l : Vec (CommAlgebra.Carrier (freeAlgebra n)) m)
                  → CommAlgebra R
  makeFPAlgebra n l = freeAlgebra n / generatedIdeal (freeAlgebra n) l

  isFPAlgebra : (A : CommAlgebra R) → Type _
  isFPAlgebra A = ∥ (Σ[ n ∈ ℕ ]
                      Σ[ m ∈ ℕ ]
                      Σ[ l ∈ Vec (CommAlgebra.Carrier (freeAlgebra n)) m ]  makeFPAlgebra n l ≡ A)  ∥

  isFPAlgebraIsProp : {A : CommAlgebra R} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = propTruncIsProp
