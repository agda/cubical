{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Quotient.IdealSum where
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
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Notation
open import Cubical.Algebra.CommAlgebra.Quotient
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.Ideal.SurjectiveImage

open import Cubical.Tactics.CommRingSolver

private variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ') (I J : IdealsIn R A) where
  private
    π = quotientHom A I

  open IdealSum (A .fst)

  πJ : IdealsIn R (A / I)
  πJ = imageIdeal (CommAlgebraHom→CommRingHom π) (quotientHomSurjective A I) J

  quotientIdealSumEquiv : CommAlgebraEquiv (A / (I +i J)) ((A / I) / πJ)
  quotientIdealSumEquiv = compCommAlgebraEquiv quotientIdealSumEquiv' (ideal≡ToEquiv πJ'≡πJ)
    where
      πJ' : IdealsIn R (A / I)
      πJ' = CommRing.Construction.π₁J I J

      t : CommRingEquiv ((A / (I +i J)) .fst) (((A / I) / πJ') .fst)
      t = CommRing.quotientIdealSumEquiv I J

      commutes : t .fst .fst ∘ fst ((A / (I +i J)) .snd) ≡ fst (((A / I) / πJ') .snd)
      commutes = cong (λ f → f ∘ A .snd .fst) (CommRing.commutesWithQuotientHoms I J)

      quotientIdealSumEquiv' : CommAlgebraEquiv (A / (I +i J)) ((A / I) / πJ')
      quotientIdealSumEquiv' =
        CommAlgebraEquivFromCommRingEquiv t (CommRingHom≡ commutes)

      πJ'≡πJ : πJ' ≡ πJ
      πJ'≡πJ = Σ≡Prop (isPropIsCommIdeal _) refl

      πJRing : IdealsIn R (A / I)
      πJRing = imageIdeal (CommAlgebraHom→CommRingHom π) (CommRing.quotientHomSurjective (A .fst) I) J
