{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebraAbstract where

-- many unused imports...
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients hiding (_/_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.QuotientRing as CommRing
import Cubical.Algebra.Ring.QuotientRing as Ring
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.Instances.Unit
import Cubical.Algebra.CommAlgebra.QuotientAlgebra as Impl
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom; isPropIsAlgebraHom)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal using (isIdeal)
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Algebra.Algebra.Properties
open AlgebraHoms using (compAlgebraHom)


module _ {ℓ : Level} {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  abstract
    _/_ : CommAlgebra R ℓ
    _/_ = Impl._/_ A I

    quotientHom : CommAlgebraHom A (_/_)
    quotientHom = Impl.quotientHom A I

module _ {ℓ : Level} {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  abstract
    CommForget/ : RingEquiv (CommAlgebra→Ring (A / I)) ((CommAlgebra→Ring A) Ring./ (CommIdeal→Ideal I))
    CommForget/ = Impl.CommForget/ A I

    inducedHom : (B : CommAlgebra R ℓ) (ϕ : CommAlgebraHom A B)
                 → (fst I) ⊆ (fst (kernel A B ϕ))
                 → CommAlgebraHom (A / I) B
    inducedHom = Impl.inducedHom A I


    injectivePrecomp : (B : CommAlgebra R ℓ) (f g : CommAlgebraHom (A / I) B)
                       → f ∘a (quotientHom A I) ≡ g ∘a (quotientHom A I)
                       → f ≡ g
    injectivePrecomp = Impl.injectivePrecomp A I

module _ {ℓ : Level} {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  abstract
{-
    -- level problems
    oneIdealQuotient : CommAlgebraEquiv (A / (1Ideal A)) (UnitCommAlgebra R)
    oneIdealQuotient = Impl.oneIdealQuotient A
-}

    zeroIdealQuotient : CommAlgebraEquiv A (A / (0Ideal A))
    zeroIdealQuotient = Impl.zeroIdealQuotient A

{-
-- level problems
abstract

  [_]/ : {ℓ : Level} {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
         → (a : fst A) → fst (A / I)
  [_]/ = Impl.[_]/
-}

module _ {ℓ = ℓ} {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where

  abstract
    kernel≡I : kernel A (A / I) (quotientHom A I) ≡ I
    kernel≡I = Impl.kernel≡I A I

abstract
  isZeroFromIdeal : {ℓ : Level} {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
                  → (x : ⟨ A ⟩) → x ∈ (fst I) → fst (quotientHom A I) x ≡ CommAlgebraStr.0a (snd (A / I))
  isZeroFromIdeal {ℓ} {R} {A} {I} = Impl.isZeroFromIdeal {ℓ} {R} {A} {I}
