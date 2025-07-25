{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Quotient.FGIdealSum where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure
open import Cubical.Functions.Surjection

open import Cubical.HITs.SetQuotients hiding (_/_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.FinData

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Quotient as CommRing
import Cubical.Algebra.CommRing.Quotient.IdealSum as CommRing
import Cubical.Algebra.CommRing.FGIdeal as CommRing
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Notation
open import Cubical.Algebra.CommAlgebra.Quotient
open import Cubical.Algebra.CommAlgebra.Quotient.IdealSum
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.Ideal.SurjectiveImage

open import Cubical.Tactics.CommRingSolver

private variable
  ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} {n m : ℕ} (A : CommAlgebra R ℓ') (gi : FinVec ⟨ A ⟩ₐ n) (gj : FinVec ⟨ A ⟩ₐ m) where
  private
     π = quotientHom A ⟨ gi ⟩[ A ]
     π₂ = quotientHom (A / ⟨ gi ⟩[ A ]) ⟨ ⟨ π ⟩ₐ→ ∘ gj ⟩[ A / ⟨ gi ⟩[ A ] ]

  open IdealSum (A .fst)

  fgIdealSumEquiv : CommAlgebraEquiv (A / ⟨ gi ++Fin gj ⟩[ A ]) ((A / ⟨ gi ⟩[ A ]) / ⟨ ⟨ π ⟩ₐ→ ∘ gj ⟩[ A / ⟨ gi ⟩[ A ] ])
  fgIdealSumEquiv =
    compCommAlgebraEquiv
      (ideal≡ToEquiv (CommRing.FGIdealAddLemma (fst A) gi gj))
      justWithIdealSum
    where
          justWithIdealSum : CommAlgebraEquiv (A / (⟨ gi ⟩[ A ] +i ⟨ gj ⟩[ A ]))
                                              ((A / ⟨ gi ⟩[ A ]) / ⟨ ⟨ π ⟩ₐ→ ∘ gj ⟩[ A / ⟨ gi ⟩[ A ] ])
          justWithIdealSum =
            compCommAlgebraEquiv
              (quotientIdealSumEquiv A ⟨ gi ⟩[ A ] ⟨ gj ⟩[ A ])
              (ideal≡ToEquiv (imageIdealIsImageFGIdeal A gj (A / generatedIdeal A gi) π (quotientHomSurjective A (generatedIdeal A gi))))
