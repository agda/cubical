module Cubical.Algebra.CommAlgebra.FP.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Polynomials
open import Cubical.Algebra.CommAlgebra.Quotient
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Notation

private variable
    ℓ ℓ' ℓ'' : Level

module _ (R : CommRing ℓ) where
  Polynomials : (n : ℕ) → CommAlgebra R ℓ
  Polynomials n = R [ Fin n ]ₐ

  record FinitePresentation : Type ℓ where
    no-eta-equality
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ₐ m

    opaque
      fgIdeal : IdealsIn R (Polynomials n)
      fgIdeal = ⟨ relations ⟩[ Polynomials n ]

      asFGIdeal : fgIdeal ≡ ⟨ relations ⟩[ Polynomials n ]
      asFGIdeal = refl

    opaque
      fpAlg : CommAlgebra R ℓ
      fpAlg = Polynomials n / fgIdeal
      open InstancesForCAlg fpAlg

      π : CommAlgebraHom (Polynomials n) fpAlg
      π = quotientHom (Polynomials n) fgIdeal

      generator : (i : Fin n) → ⟨ fpAlg ⟩ₐ
      generator = ⟨ π ⟩ₐ→ ∘ var

      fgIdealZero : (x : ⟨ Polynomials n ⟩ₐ) → x ∈ fst fgIdeal → π $ca x ≡ 0r
      fgIdealZero x x∈I = isZeroFromIdeal {A = Polynomials n} {I = fgIdeal} x x∈I

      computeGenerator : (i : Fin n) → π $ca (var i) ≡ generator i
      computeGenerator i = refl

      fpAlgAsQuotient : CommAlgebraEquiv fpAlg (Polynomials n / fgIdeal)
      fpAlgAsQuotient = idCAlgEquiv fpAlg

  FPsOf : (A : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
  FPsOf A = Σ[ p ∈ FinitePresentation ] CommAlgebraEquiv (FinitePresentation.fpAlg p) A

  isFP : (A : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
  isFP A = ∥ FPsOf A ∥₁

  opaque
    isFPIsProp : {A : CommAlgebra R ℓ'} → isProp (isFP A)
    isFPIsProp = isPropPropTrunc

  FPCAlg : (ℓ' : Level) → Type _
  FPCAlg ℓ' = Σ[ A ∈ CommAlgebra R ℓ' ] isFP A

  isFPByEquiv : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → CommAlgebraEquiv A B → isFP A → isFP B
  isFPByEquiv A B A≅B ∥fpA∥ =
    PT.rec
      isPropPropTrunc
      (λ (fp , fp≅A) → ∣ fp , compCommAlgebraEquiv fp≅A A≅B ∣₁)
      ∥fpA∥
