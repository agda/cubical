{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (f₁,⋯,fₘ) → R[X₁,⋯,Xₙ] → A → 0

  (where f₁,⋯,fₘ ∈ R[X₁,⋯,Xₙ])
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
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
  record finitePresentation (A : CommAlgebra R ℓ) : Type ℓ where
    field
      n : ℕ
      m : ℕ
      relations : FinVec (fst (freeAlgebra n)) m
      equiv : CommAlgebraHom A (makeFPAlgebra n relations)
{-

finitePresentation : (A : CommAlgebra R ℓ) → Type _
  finitePresentation A = Σ[ ((n , m) , l) ∈ Σ[ (n , m) ∈ ℕ × ℕ ] FinVec (fst (freeAlgebra n)) m ]
                         CommAlgebraEquiv (makeFPAlgebra n l) A

  isFPAlgebra : (A : CommAlgebra R ℓ) → Type _
  isFPAlgebra A = ∥ finitePresentation A ∥

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc

module Instances {R : CommRing ℓ} where
  initialFP : finitePresentation (initialCAlg R)
  initialFP = {!!}
  initialFP = ((0 , 0) , emptyGen) , equivByInitiality R R[⊥]/⟨0⟩ isInitial
    where
      R[⊥] : CommAlgebra R ℓ
      R[⊥] = R [ Fin 0 ]

      emptyGen : FinVec (fst R[⊥]) 0
      emptyGen = λ ()

      R[⊥]/⟨0⟩ : CommAlgebra R ℓ
      R[⊥]/⟨0⟩ = R[⊥] / (generatedIdeal R[⊥] emptyGen)

      postulate
        isInitial : (A : CommAlgebra R ℓ) → isContr (CommAlgebraHom R[⊥]/⟨0⟩ A)
-}
