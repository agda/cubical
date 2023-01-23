{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.UnivariateList.Karatsuba where

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty.Base renaming (rec to ⊥rec )
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.Polynomials.UnivariateList.UniversalProperty

open import Cubical.Algebra.CommAlgebra.UnivariatePolyList

private
  variable
    ℓ ℓ' : Level


module _ (R' : CommRing ℓ) where

  open PolyMod R'
  open PolyModTheory R'
  open CommRingStr ⦃...⦄
  open Exponentiation (UnivariatePolyList R')

  private
    R = fst R'
    instance
      _ = snd R'
      _ = snd (UnivariatePolyList R')

    X : Poly R'
    X = 0r ∷ 1r ∷ []

    R[X] = Poly R'
  -- p(X) ↦ p(X²)
  evalAtX² : R[X] → R[X]
  evalAtX² = RecPoly.f []
                       (λ a p → a ∷ 0r ∷ p)
                       (cong (0r ∷_) drop0 ∙ drop0)

  inducedEvalAtX² : AlgebraHom (CommAlgebra→Algebra (ListPolyCommAlgebra R'))
                               (CommAlgebra→Algebra (ListPolyCommAlgebra R'))
  inducedEvalAtX² = inducedHom _ _ (X ^ 2)

  -- this gives us homomorphism properties
  evalAtX²≡ : fst inducedEvalAtX² ≡ evalAtX²
  evalAtX²≡ = funExt (ElimProp _ refl step (isSetPoly _ _))
    where
    X² = X ^ 2
    useSolver1 : ∀ r → r · 1r + 0r ≡ r
    useSolver1 = solve R'
    useSolver2 : ∀ p q → (p ^ 2) · q ≡ p · (p · q)
    useSolver2 = solve (UnivariatePolyList R')
    step : ∀ (r : R) (p : R[X])
         → inducedMap _ _ X² p ≡ evalAtX² p
         → fst inducedEvalAtX² (r ∷ p) ≡ evalAtX² (r ∷ p)
    step r p hyp =
        [ r · 1r + 0r ] + (X² · inducedMap _ _ X² p)

      ≡⟨ cong₂ (λ x y → [ x ] + y) (useSolver1 _) (useSolver2 X (inducedMap _ _ X² p)) ⟩

        [ r ] + X · (X · inducedMap _ _ X² p)

      ≡⟨ cong (λ x → [ r ] + X · x) (X*Poly (inducedMap _ _ X² p)) ⟩

        [ r ] + X · (0r ∷ inducedMap _ _ X² p)

      ≡⟨ cong (λ x → [ r ] + x) (X*Poly (0r ∷ inducedMap _ _ X² p)) ⟩

        (r + 0r) ∷ 0r ∷ inducedMap _ _ X² p

      ≡⟨ cong (λ x → x ∷ 0r ∷ inducedMap _ _ X² p) (+IdR r) ⟩

        r ∷ 0r ∷ inducedMap _ _ X² p

      ≡⟨ cong (λ x → r ∷ 0r ∷ x) hyp ⟩

        r ∷ 0r ∷ evalAtX² p ∎


  -- split into coefficients of even and odd degree
  evenDegCoeff : R[X] → R[X]
  evenDegCoeff [] = []
  evenDegCoeff [ a ] = []
  evenDegCoeff (a ∷ b ∷ p) = b ∷ evenDegCoeff p
  evenDegCoeff (a ∷ drop0 i) = drop0 i
  evenDegCoeff (drop0 i) = []

  syntax evenDegCoeff p = p ₑ

  oddDegCoeff : R[X] → R[X]
  oddDegCoeff [] = []
  oddDegCoeff [ a ] = [ a ]
  oddDegCoeff (a ∷ b ∷ p) = a ∷ oddDegCoeff p
  oddDegCoeff (a ∷ drop0 i) = [ a ]
  oddDegCoeff (drop0 i) = drop0 i

  syntax oddDegCoeff p = p ₒ

  -- custom eliminator
  module _ (B : R[X] → Type ℓ')
           (BProp : ∀ p → isProp (B p))
           ([]* : B [])
           (sing* : ∀ a → B [ a ])
           (cons* : ∀ a b p → B p → B (a ∷ b ∷ p)) where

   B' : R[X] → Type (ℓ-max ℓ ℓ')
   B' p = B p × (∀ a → B (a ∷ p))
   foo : ∀ p → B' p
   foo = ElimProp _ ([]* , sing*)
                    (λ b p B'p → (B'p .snd b) , λ a → cons* a b p (B'p .fst))
                    (isProp× (BProp _) (isPropΠ (λ _ → BProp _)))
   ElimPropDoubleCons : ∀ p → B p
   ElimPropDoubleCons p = foo p .fst

  -- observation:
  splitPoly : ∀ (p : R[X]) → evalAtX² (p ₑ) + X · evalAtX² (p ₒ) ≡ p
  splitPoly = ElimProp _ (cong (0r ∷_) drop0 ∙ drop0) nested (isSetPoly _ _)
    where
    nested : ∀ r p
           → evalAtX² (p ₑ) + X · evalAtX² (p ₒ) ≡ p
           → evalAtX² ((r ∷ p) ₑ) + X · evalAtX² ((r ∷ p) ₒ) ≡ r ∷ p
    nested r = ElimProp _ (λ _ → basePath) {!!} (isProp→ (isSetPoly _ _))
      where
      basePath : (0r · r + 0r) ∷ (0r · 0r + (1r · r + 0r)) ∷ [ 1r · 0r ]
               ≡ [ r ]
      basePath = {!!}

  -- splitPoly : ∀ (p : R[X]) → evalAtX² (p ₑ) + X · evalAtX² (p ₒ) ≡ p
  -- splitPoly [] = cong (0r ∷_) drop0 ∙ drop0
  -- splitPoly [ a ] = {!!}
  -- splitPoly (a ∷ b ∷ p) = {!!}
  -- splitPoly (a ∷ drop0 i) = {!!}
  -- splitPoly (drop0 i) = isSetPoly _ _ {!!} {!!} i
