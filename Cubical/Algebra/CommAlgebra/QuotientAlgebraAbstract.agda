{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebraAbstract where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Algebra.CommRing using (CommRing)
import Cubical.Algebra.CommRing.QuotientRing as CommRing
import Cubical.Algebra.Ring.QuotientRing as Ring
open import Cubical.Algebra.CommRing.Ideal using (CommIdeal→Ideal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal using (IdealsIn; 1Ideal; 0Ideal)
open import Cubical.Algebra.CommAlgebra.Kernel using (kernel)
open import Cubical.Algebra.CommAlgebra.Instances.Unit using (UnitCommAlgebra)
open import Cubical.Algebra.Ring using (RingEquiv)
open import Cubical.Algebra.Algebra.Properties using (module AlgebraHoms)
open AlgebraHoms using (compAlgebraHom)

import Cubical.Algebra.CommAlgebra.QuotientAlgebra as Impl


-- Note that anonymous modules have a shared abstract scope.

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

    inducedHom∘quotientHom : (B : CommAlgebra R ℓ) (ϕ : CommAlgebraHom A B)
                 → (I⊆kerϕ : fst I ⊆ fst (kernel A B ϕ))
                 → inducedHom B ϕ I⊆kerϕ ∘a quotientHom A I ≡ ϕ
    inducedHom∘quotientHom = Impl.inducedHom∘quotientHom A I

    injectivePrecomp : (B : CommAlgebra R ℓ) (f g : CommAlgebraHom (A / I) B)
                       → f ∘a (quotientHom A I) ≡ g ∘a (quotientHom A I)
                       → f ≡ g
    injectivePrecomp = Impl.injectivePrecomp A I

module _ {ℓ : Level} {R : CommRing ℓ} (A : CommAlgebra R ℓ) where

  abstract
    oneIdealQuotient : CommAlgebraEquiv (A / (1Ideal A)) (UnitCommAlgebra R {ℓ' = ℓ})
    oneIdealQuotient = Impl.oneIdealQuotient A

    zeroIdealQuotient : CommAlgebraEquiv A (A / (0Ideal A))
    zeroIdealQuotient = Impl.zeroIdealQuotient A

abstract
  [_]/ : {ℓ : Level} {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
         → (a : fst A) → fst (A / I)
  [_]/ {A = A} {I = I} = Impl.[_]/ {A = A} {I = I}

module _ {ℓ = ℓ} {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  abstract
    kernel≡I : kernel A (A / I) (quotientHom A I) ≡ I
    kernel≡I = Impl.kernel≡I A I

abstract
  isZeroFromIdeal : {ℓ : Level} {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
                  → (x : ⟨ A ⟩) → x ∈ (fst I) → fst (quotientHom A I) x ≡ CommAlgebraStr.0a (snd (A / I))
  isZeroFromIdeal {ℓ} {R} {A} {I} = Impl.isZeroFromIdeal {ℓ} {R} {A} {I}
