{-# OPTIONS --lossy-unification #-}
{-
  Universal property of finitely presented algebras
-}
module Cubical.Algebra.CommAlgebra.FP.Properties where

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

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.FP.Base
open import Cubical.Algebra.CommAlgebra.Notation
import Cubical.Algebra.CommAlgebra.Polynomials as Poly
import Cubical.Algebra.CommAlgebra.Quotient as Quot

private variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) (fp : FinitePresentation R) (A : CommAlgebra R ℓ) where
  open FinitePresentation fp
  open InstancesForCAlg A

  module _ (φ : FinVec ⟨ A ⟩ₐ n) (p : (i : Fin m) → Poly.inducedHom A φ $ca relations i ≡ 0r) where
    opaque
      unfolding fpAlg fgIdeal
      polyInduced : CommAlgebraHom (Polynomials R n) A
      polyInduced = Poly.inducedHom A φ

      ⟨relations⟩⊆kernel : fst ⟨ relations ⟩[ Polynomials R n ] ⊆ fst (kernel (Polynomials R n) A polyInduced)
      ⟨relations⟩⊆kernel = inclOfFGIdeal (Polynomials R n) relations (kernel (Polynomials R n) A polyInduced) p

      inducedHom : CommAlgebraHom fpAlg A
      inducedHom =
        Quot.inducedHom
          (Polynomials R n)
          fgIdeal
          A
          polyInduced
          (subst (λ J → fst J ⊆ fst (kernel (Polynomials R n) A polyInduced)) (sym asFGIdeal) ⟨relations⟩⊆kernel)


      inducedHomUnique :
                     (f : CommAlgebraHom fpAlg A)
                   → ((i : Fin n) → f $ca (generator i) ≡ φ i)
                   → inducedHom ≡ f
      inducedHomUnique f q =
        sym ((Quot.inducedHomUnique
                 (Polynomials R n) fgIdeal A (f ∘ca π)
                 (subst (λ g → fst ⟨ relations ⟩[ Polynomials R n ]
                               ⊆ fst (kernel (Polynomials R n) A g))
                        uniqueOnPoly
                        ⟨relations⟩⊆kernel)
                 f refl)
             ∙ (subst (λ h → Quot.inducedHom (Polynomials R n) fgIdeal A (fst h) (snd h) ≡ inducedHom)
                      (Σ≡Prop {B = λ g → fst ⟨ relations ⟩[ Polynomials R n ] ⊆ fst (kernel (Polynomials R n) A g)}
                              (λ _ → ⊆-isProp _ _) uniqueOnPoly)
                      refl))
        where
          uniqueOnPoly : polyInduced ≡ f ∘ca π
          uniqueOnPoly = Poly.inducedHomUnique A φ (f ∘ca π) (funExt λ k → cong ⟨ f ⟩ₐ→ (computeGenerator k) ∙ q k)
