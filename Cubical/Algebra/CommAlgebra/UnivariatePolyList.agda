{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

open import Cubical.Tactics.CommRingSolver.Reflection

private variable
  ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  open RingStr ⦃...⦄    -- Not CommRingStr, so it can be used in together with AlgebraStr
  open PolyModTheory R
  private
    ListPoly = UnivariatePolyList R
    instance
      _ = snd (CommRing→Ring ListPoly)
      _ = snd (CommRing→Ring R)

  ListPolyCommAlgebra : CommAlgebra R ℓ
  ListPolyCommAlgebra =
    commAlgebraFromCommRing
      ListPoly
      (λ r x → [ r ] · x)
      (λ r s x → ([ r · s ] · x)      ≡[ i ]⟨ sym (PolyConst*Hom r s) i · x ⟩
                 ([ r ] · [ s ]) · x  ≡⟨ sym (·Assoc [ r ] [ s ] x) ⟩
                  [ r ] · ([ s ] · x) ∎)
      (λ r x y → ·DistR+ [ r ] x y)
      (λ r s x → ·DistL+ [ r ] [ s ] x)
      (λ x → ·IdL x)
      λ r x y → sym (·Assoc [ r ] x y)

  {- Universal Property -}
  module _ (A : Algebra (CommRing→Ring R) ℓ') where
    open AlgebraStr ⦃...⦄ using (_⋆_; 0a; 1a)
    private instance
      _ = snd A
      _ = snd (Algebra→Ring A)

    module _ (x : ⟨ A ⟩) where
      inducedMap : ⟨ ListPolyCommAlgebra ⟩ → ⟨ A ⟩
      inducedMap [] = 0a
      inducedMap (a ∷ p) = a ⋆ 1a + (x · inducedMap p)
      inducedMap (drop0 i) = eq i
        where
          open AlgebraTheory using (0-actsNullifying)
          open RingTheory using (0RightAnnihilates)

          eq = 0r ⋆ 1a + (x · 0a) ≡[ i ]⟨  0-actsNullifying (CommRing→Ring R) A 1a i + (x · 0a) ⟩
               0a + (x · 0a)      ≡⟨ +IdL (x · 0a) ⟩
               x · 0a             ≡⟨ 0RightAnnihilates (Algebra→Ring A) x ⟩
               0a ∎

      open IsAlgebraHom
      inducedHom : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A
      fst inducedHom = inducedMap
      (snd inducedHom).pres0 = refl
      (snd inducedHom).pres1 = {!!} -- inducedMap (1r ∷ []) = 1r ⋆ (x · 0a)
      (snd inducedHom).pres+ = {!!}
      (snd inducedHom).pres· = {!!}
      (snd inducedHom).pres- = {!!}
      (snd inducedHom).pres⋆ = {!!}
