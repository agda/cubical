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
open import Cubical.Foundations.Powerset

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (inclOfFGIdeal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (inducedHom to freeInducedHom)
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Kernel


open import Cubical.Foundations.Structure

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} where
  Polynomials : (n : ℕ) → CommAlgebra R ℓ
  Polynomials n = R [ Fin n ]

  evPoly : {n : ℕ} (A : CommAlgebra R ℓ) → ⟨ Polynomials n ⟩ → FinVec ⟨ A ⟩ n → ⟨ A ⟩
  evPoly A P values = fst (freeInducedHom A values) P 

  module _ {m : ℕ} (n : ℕ) (relation : FinVec ⟨ Polynomials n ⟩ m) where
    open CommAlgebraStr using (0a)

    relationsIdeal = generatedIdeal (Polynomials n) relation

    FPAlgebra : CommAlgebra R ℓ
    FPAlgebra = Polynomials n / relationsIdeal

    module universalProperty
      {A : CommAlgebra R ℓ}
      (values : FinVec ⟨ A ⟩ n)
      (relationsHold : (i : Fin m) → evPoly A (relation i) values ≡ 0a (snd A))
      where

      open Construction using (var)

      inducedHom : CommAlgebraHom FPAlgebra A
      inducedHom =
        quotientInducedHom
          (Polynomials n)
          relationsIdeal
          A
          freeHom
          isInKernel
        where
          freeHom = freeInducedHom A values
          isInKernel :   fst (generatedIdeal (Polynomials n) relation)
                       ⊆ fst (kernel (Polynomials n) A freeHom)
          isInKernel = inclOfFGIdeal
                         (CommAlgebra→CommRing (Polynomials n))
                         relation
                         (kernel (Polynomials n) A freeHom)
                         relationsHold

      generator : (i : Fin n) → ⟨ FPAlgebra ⟩
      generator i =
        elementInQuotientCAlg
          R (Polynomials n) relationsIdeal (var i)

      unique : (f : CommAlgebraHom FPAlgebra A)
             → ((i : Fin n) → fst f (generator i)  ≡ values i)
             → f ≡ inducedHom
      unique = {!!}

{-

  record finitePresentation (A : CommAlgebra R ℓ) : Type ℓ where
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ m
      equiv : CommAlgebraEquiv (FPAlgebra.make n relations) A

  isFPAlgebra : (A : CommAlgebra R ℓ) → Type _
  isFPAlgebra A = ∥ finitePresentation A ∥

  isFPAlgebraIsProp : {A : CommAlgebra R ℓ} → isProp (isFPAlgebra A)
  isFPAlgebraIsProp = isPropPropTrunc

module Instances {R : CommRing ℓ} where
  private
    R[⊥] : CommAlgebra R ℓ
    R[⊥] = Polynomials 0

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
    Polynomials 0 / generatedIdeal (Polynomials 0) emptyGen ≃CAlg⟨ {!!} ⟩
    initialCAlg R                                           ≃CAlg∎
-}
