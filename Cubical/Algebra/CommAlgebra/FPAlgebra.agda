{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (a₁,⋯,aₘ) → R[X₁,⋯,Xₙ] → A → 0
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} where
  freeAlgebra : (n : ℕ) → CommAlgebra R ℓ
  freeAlgebra n = R [ Fin n ]

  makeFPAlgebra : {m : ℕ} (n : ℕ) (l : FinVec (fst (freeAlgebra n)) m)
                  → CommAlgebra R ℓ
  makeFPAlgebra n l = freeAlgebra n / generatedIdeal (freeAlgebra n) l

  isFPAlgebra : (A : CommAlgebra R ℓ) → Type _
  isFPAlgebra A = ∃[ ((n , m) , l) ∈ Σ[ (n , m) ∈ ℕ × ℕ ] FinVec (fst (freeAlgebra n)) m ]
                   makeFPAlgebra n l ≡ A

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc
