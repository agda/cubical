{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Quotient.Properties where
open import Cubical.Foundations.Prelude as Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Univalence
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Quotient.Base

open import Cubical.Tactics.CommRingSolver

private variable
  ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} {A : CommAlgebra R ℓ'} {I : IdealsIn R A} where

  ideal≡ToEquiv : {J : IdealsIn R A} → I ≡ J → CommAlgebraEquiv (A / I) (A / J)
  ideal≡ToEquiv {J = J} I≡J = pathToAlgEquiv $ cong (λ K → A / K) I≡J
    where
      pathToAlgEquiv : (A / I) ≡ (A / J) → CommAlgebraEquiv (A / I) (A / J)
      pathToAlgEquiv = fst $ invEquiv $ CommAlgebraPath (A / I) (A / J)

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ') (I : IdealsIn R A) (B : CommAlgebra R ℓ') (J : IdealsIn R B) where
  idealAlg≡ToEquiv : (A , I) ≡ (B , J) → CommAlgebraEquiv (A / I) (B / J)
  idealAlg≡ToEquiv p = fst (invEquiv $ CommAlgebraPath (A / I) (B / J)) A/I≡B/J
    where A/I≡B/J = cong (λ (C , K) → C / K) p

  commAlgIdealEquivToQuotientEquiv :
    (e : CommAlgebraEquiv A B) → ((x : ⟨ A ⟩ₐ) → fst I x ≡ fst J ((⟨ e ⟩ₐ≃ x)))
    → CommAlgebraEquiv (A / I) (B / J)
  commAlgIdealEquivToQuotientEquiv e p =
    idealAlg≡ToEquiv
        (Prelude.J
          (λ B A≡B → (I : IdealsIn R A) (J : IdealsIn R B) (p : (x : ⟨ A ⟩ₐ) → fst I x ≡ fst J (transport (cong ⟨_⟩ₐ A≡B) x) )
                   → (A , I) ≡ (B , J))
          (λ I J p → cong (λ K → (A , K)) (Σ≡Prop (isPropIsCommIdeal _) (funExt (λ x → p x ∙ cong (fst J) (transportRefl x)))))
          (uaCommAlgebra e) I J λ x → p x ∙ cong (fst J) (sym (uaβ (fst e) x)))
