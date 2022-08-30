{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.MonoidSolver.Reflection

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
    open AlgebraStr ⦃...⦄ using (_⋆_; 0a; 1a; ⋆IdL; ⋆DistL+)
    private instance
      _ = snd A
      _ = snd (Algebra→Ring A)

    module _ (x : ⟨ A ⟩) where
      open AlgebraTheory using (0-actsNullifying)
      open RingTheory using (0RightAnnihilates)
      open AbGroupTheory using (comm-4)
      open PolyMod using (elimProp2; isSetPoly)

      inducedMap : ⟨ ListPolyCommAlgebra ⟩ → ⟨ A ⟩
      inducedMap [] = 0a
      inducedMap (a ∷ p) = a ⋆ 1a + (x · inducedMap p)
      inducedMap (drop0 i) = eq i
        where
          eq = 0r ⋆ 1a + (x · 0a) ≡[ i ]⟨  0-actsNullifying (CommRing→Ring R) A 1a i + (x · 0a) ⟩
               0a + (x · 0a)      ≡⟨ +IdL (x · 0a) ⟩
               x · 0a             ≡⟨ 0RightAnnihilates (Algebra→Ring A) x ⟩
               0a ∎

      open IsAlgebraHom
      inducedHom : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A
      fst inducedHom = inducedMap
      (snd inducedHom).pres0 = refl
      (snd inducedHom).pres1 =
        inducedMap [ 1r ]   ≡⟨⟩
        1r ⋆ 1a + (x · 0a)  ≡[ i ]⟨ ⋆IdL 1a i + 0RightAnnihilates (Algebra→Ring A) x i ⟩
        1a + 0a             ≡⟨ +IdR 1a ⟩
        1a ∎
      (snd inducedHom).pres+ =
        elimProp2 R
          (λ x y → inducedMap (x + y) ≡ inducedMap x + inducedMap y)
          (0a ≡⟨ sym (+IdR _) ⟩ 0a + 0a ∎)
          (λ r p _ →
            inducedMap ((r ∷ p) + []) ≡⟨⟩
            inducedMap (r ∷ p)        ≡⟨ sym (+IdR _) ⟩
            (inducedMap (r ∷ p) + 0a) ∎)
          (λ s q _ →
            inducedMap ([] + (s ∷ q)) ≡⟨⟩
            inducedMap (s ∷ q)        ≡⟨ sym (+IdL _) ⟩
            0a + inducedMap (s ∷ q)   ∎)
          (λ r s p q IH →
            inducedMap ((r ∷ p) + (s ∷ q))                            ≡⟨⟩
            inducedMap (r + s ∷ p + q)                                ≡⟨⟩
            (r + s) ⋆ 1a + x · inducedMap (p + q)                     ≡[ i ]⟨ (r + s) ⋆ 1a + x · IH i ⟩
            (r + s) ⋆ 1a + (x · (inducedMap p + inducedMap q))        ≡[ i ]⟨ step1 r s p q i ⟩
            (r ⋆ 1a + s ⋆ 1a) + (x · inducedMap p + x · inducedMap q) ≡⟨ comm-4 (Algebra→AbGroup A) _ _ _ _ ⟩
            (r ⋆ 1a + x · inducedMap p) + (s ⋆ 1a + x · inducedMap q) ≡⟨⟩
            inducedMap (r ∷ p) + inducedMap (s ∷ q) ∎)
          (is-set _ _)
          where step1 : (r s : ⟨ R ⟩) (p q : _) → _ ≡ _
                step1 r s p q i = ⋆DistL+ r s 1a i + ·DistR+ x (inducedMap p) (inducedMap q) i
                M = (AbGroup→CommMonoid (Algebra→AbGroup A))
                {- TODO: Use CommMonoidSolver, once it can recognize '+'
                step2 : (a b c d : ⟨ A ⟩) →
                        (a + b) + (c + d) ≡ (a + c) + (b + d)
                step2 = solveCommMonoid M -}
      (snd inducedHom).pres· =
        elimProp2 R
          (λ x y → inducedMap (x · y) ≡ inducedMap x · inducedMap y)
          {!!} {!!} {!!} {!!}
          (is-set _ _)
      (snd inducedHom).pres- = {!!}
      (snd inducedHom).pres⋆ = {!!}
