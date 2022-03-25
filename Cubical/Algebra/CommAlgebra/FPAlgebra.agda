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
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} where
  abstract
    freeAlgebraType : (n : ℕ) → Type ℓ
    freeAlgebraType n = fst (R [ Fin n ])
    freeAlgebraStr : (n : ℕ) → CommAlgebraStr R (freeAlgebraType n)
    freeAlgebraStr n = snd (R [ Fin n ])

  freeAlgebra : (n : ℕ) → CommAlgebra R ℓ
  freeAlgebra n = freeAlgebraType n , freeAlgebraStr n

  abstract
    makeFPAlgebra : {m : ℕ} (n : ℕ) (l : FinVec (fst (freeAlgebra n)) m)
                  → CommAlgebra R ℓ
    makeFPAlgebra n l = freeAlgebra n / generatedIdeal (freeAlgebra n) l

  record finitePresentation (A : CommAlgebra R ℓ) : Type ℓ where
    field
      n : ℕ
      m : ℕ
      relations : FinVec (fst (freeAlgebra n)) m
      equiv : CommAlgebraEquiv (makeFPAlgebra n relations) A

  isFPAlgebra : (A : CommAlgebra R ℓ) → Type _
  isFPAlgebra A = ∥ finitePresentation A ∥

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc

module Instances {R : CommRing ℓ} where
  private
    R[⊥] : CommAlgebra R ℓ
    R[⊥] = freeAlgebra 0

    emptyGen : FinVec (fst R[⊥]) 0
    emptyGen = λ ()

    R[⊥]/⟨0⟩ : CommAlgebra R ℓ
    R[⊥]/⟨0⟩ = R[⊥] / (generatedIdeal R[⊥] emptyGen)

  initialCAlgFP : finitePresentation (initialCAlg R)
  finitePresentation.n initialCAlgFP = 0
  finitePresentation.m initialCAlgFP = 0
  finitePresentation.relations initialCAlgFP = emptyGen
  finitePresentation.equiv initialCAlgFP =
    makeFPAlgebra 0 emptyGen                                ≃CAlg⟨ {!idCAlgEquiv _!} ⟩
    freeAlgebra 0 / generatedIdeal (freeAlgebra 0) emptyGen ≃CAlg⟨ {!!} ⟩
    initialCAlg R                                           ≃CAlg∎
