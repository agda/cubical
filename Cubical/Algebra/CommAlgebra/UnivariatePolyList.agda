{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

private variable
  ℓ : Level

module _ (R : CommRing ℓ) where
  open CommRingStr ⦃...⦄
  open PolyModTheory R
  private
    ListPoly = UnivariatePolyList R
    instance
      _ = snd ListPoly
      _ = snd R

  ListPolyCommAlgebra : CommAlgebra R ℓ
  ListPolyCommAlgebra =
    commAlgebraFromCommRing
      ListPoly
      (λ r x → [ r ] · x)
      (λ r s x → ([ r · s ] · x)      ≡[ i ]⟨ sym (MultHom[-] r s) i · x ⟩
                 ([ r ] · [ s ]) · x  ≡⟨ sym (·Assoc [ r ] [ s ] x) ⟩
                  [ r ] · ([ s ] · x) ∎)
      (λ r x y → ·DistR+ [ r ] x y)
      (λ r s x → ·DistL+ [ r ] [ s ] x)
      (λ x → ·IdL x)
      λ r x y → sym (·Assoc [ r ] x y)
