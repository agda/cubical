module Cubical.Algebra.CommAlgebraAlt.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.CommAlgebraAlt.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

CommAlgebraPath : (R : CommRing ℓ) → (A B : CommAlgebra R ℓ') → (CommAlgebraEquiv A B) ≃ (A ≡ B)
CommAlgebraPath R A B = isoToEquiv (iso to {!!} {!!} {!!})
  where
    to : CommAlgebraEquiv A B → A ≡ B
    to e = Σ≡Prop {!!} (CommRingPath (A .fst) (B .fst) .fst (e .fst))

{-
CommAlgebraPath : (R : CommRing ℓ) → (A B : CommAlgebra R ℓ') → (CommAlgebraEquiv A B) ≃ (A ≡ B)
CommAlgebraPath R = ∫ (𝒮ᴰ-CommAlgebra R) .UARel.ua

uaCommAlgebra : {R : CommRing ℓ} {A B : CommAlgebra R ℓ'} → CommAlgebraEquiv A B → A ≡ B
uaCommAlgebra {R = R} {A = A} {B = B} = equivFun (CommAlgebraPath R A B)

isGroupoidCommAlgebra : {R : CommRing ℓ} → isGroupoid (CommAlgebra R ℓ')
isGroupoidCommAlgebra A B = isOfHLevelRespectEquiv 2 (CommAlgebraPath _ _ _) (isSetAlgebraEquiv _ _)
-}
