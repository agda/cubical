module Cubical.Algebra.CommRing.Polynomials.Typevariate.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.SetTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} where
  open CommRingStr ⦃...⦄
  private instance
    _ = snd R

  polynomialsOn⊥ : CommRingEquiv (R [ ⊥ ]) R
  polynomialsOn⊥ =
    isoToEquiv
      (iso (to .fst) (from .fst)
           (λ x → cong (λ f → f .fst x) to∘from)
           (λ x → cong (λ f → f .fst x) from∘to)) ,
    isHom
    where to : CommRingHom (R [ ⊥ ]) R
          to = inducedHom R (idCommRingHom R) ⊥.rec

          from : CommRingHom R (R [ ⊥ ])
          from = constPolynomial R ⊥

          to∘from : to ∘cr from ≡ idCommRingHom R
          to∘from = CommRingHom≡ refl

          from∘to : from ∘cr to ≡ idCommRingHom (R [ ⊥ ])
          from∘to = idByIdOnVars (from ∘cr to) refl (funExt ⊥.elim)

          abstract
            isHom : IsCommRingHom ((R [ ⊥ ]) .snd) (to .fst) (R .snd)
            isHom = to .snd
