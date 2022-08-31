{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

open import Cubical.Tactics.CommRingSolver.Reflection

private variable
  ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  open RingStr ⦃...⦄    -- Not CommRingStr, so it can be used together with AlgebraStr
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
    open AlgebraStr ⦃...⦄ using (_⋆_; 0a; 1a; ⋆IdL; ⋆DistL+; ⋆DistR+; ⋆AssocL; ⋆AssocR; ⋆Assoc)
    private instance
      _ = snd A
      _ = snd (Algebra→Ring A)
      _ = snd (CommAlgebra→Algebra ListPolyCommAlgebra)

    module _ (x : ⟨ A ⟩) where
      open AlgebraTheory using (0-actsNullifying; 0a-absorbs)
      open RingTheory using (0RightAnnihilates; 0LeftAnnihilates)
      open AbGroupTheory using (comm-4)
      open PolyMod using (ElimProp; elimProp2; isSetPoly)

      private
        X : ⟨ ListPolyCommAlgebra ⟩
        X = 0r ∷ 1r ∷ []

      inducedMap : ⟨ ListPolyCommAlgebra ⟩ → ⟨ A ⟩
      inducedMap [] = 0a
      inducedMap (a ∷ p) = a ⋆ 1a + (x · inducedMap p)
      inducedMap (drop0 i) = eq i
        where
          eq = 0r ⋆ 1a + (x · 0a) ≡[ i ]⟨  0-actsNullifying (CommRing→Ring R) A 1a i + (x · 0a) ⟩
               0a + (x · 0a)      ≡⟨ +IdL (x · 0a) ⟩
               x · 0a             ≡⟨ 0RightAnnihilates (Algebra→Ring A) x ⟩
               0a ∎

      private
        inducedMap1 : inducedMap (1r ∷ []) ≡ 1a
        inducedMap1 =
          inducedMap [ 1r ]   ≡⟨⟩
          1r ⋆ 1a + (x · 0a)  ≡[ i ]⟨ ⋆IdL 1a i + 0RightAnnihilates (Algebra→Ring A) x i ⟩
          1a + 0a             ≡⟨ +IdR 1a ⟩
          1a ∎

        inducedMapGenerator : inducedMap X ≡ x
        inducedMapGenerator =
          0r ⋆ 1a + (x · inducedMap (1r ∷ [])) ≡[ i ]⟨  0-actsNullifying
                                               (CommRing→Ring R) A 1a i + (x · inducedMap (1r ∷ [])) ⟩
          0a + (x · inducedMap (1r ∷ []))     ≡⟨ +IdL _ ⟩
          x · inducedMap (1r ∷ [])            ≡[ i ]⟨ x · inducedMap1 i ⟩
          x · 1a                              ≡⟨ ·IdR _ ⟩
          x ∎

        inducedMapPolyConst⋆ : (r : ⟨ R ⟩) (p : _) → inducedMap (r PolyConst* p) ≡ r ⋆ inducedMap p
        inducedMapPolyConst⋆ r =
          ElimProp R
            (λ p → inducedMap (r PolyConst* p) ≡ r ⋆ inducedMap p)
            (inducedMap (r PolyConst* []) ≡⟨⟩
             inducedMap []       ≡⟨⟩
             0a                  ≡⟨ sym (0a-absorbs (CommRing→Ring R) A r) ⟩
             r ⋆ 0a ∎)
            (λ s p IH →
              inducedMap (r PolyConst* (s ∷ p))              ≡⟨⟩
              inducedMap ((r · s) ∷ (r PolyConst* p))        ≡⟨⟩
              (r · s) ⋆ 1a + x · inducedMap (r PolyConst* p) ≡[ i ]⟨ ⋆Assoc r s 1a i + x · IH i ⟩
              r ⋆ (s ⋆ 1a) + x · (r ⋆ inducedMap p)          ≡⟨ step s p ⟩
              r ⋆ (s ⋆ 1a) + r ⋆ (x · inducedMap p)          ≡⟨ sym (⋆DistR+ r (s ⋆ 1a) (x · inducedMap p)) ⟩
              r ⋆ (s ⋆ 1a + x · inducedMap p)                ≡⟨⟩
              r ⋆ inducedMap (s ∷ p) ∎)
            (is-set _ _)
            where
              step : (s : ⟨ R ⟩) (p : _) → _ ≡ _
              step s p i = r ⋆ (s ⋆ 1a) + sym (⋆AssocR r x (inducedMap p)) i

        inducedMap⋆ : (r : ⟨ R ⟩) (p : _) → inducedMap (r ⋆ p) ≡ r ⋆ inducedMap p
        inducedMap⋆ r p =
          inducedMap (r ⋆ p)          ≡⟨ cong inducedMap (sym (PolyConst*≡Poly* r p)) ⟩
          inducedMap (r PolyConst* p) ≡⟨ inducedMapPolyConst⋆ r p ⟩
          r ⋆ inducedMap p ∎

        inducedMap+ : (p q : _) → inducedMap (p + q) ≡ inducedMap p + inducedMap q
        inducedMap+ =
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

        inducedMap· : (p q : _) → inducedMap (p · q) ≡ inducedMap p · inducedMap q
        inducedMap· p q =
          ElimProp R
            (λ p → inducedMap (p · q) ≡ inducedMap p · inducedMap q)
            (inducedMap ([] · q)      ≡⟨⟩
             inducedMap []            ≡⟨⟩
             0a                       ≡⟨ sym (0LeftAnnihilates (Algebra→Ring A) _) ⟩
             0a · inducedMap q ∎)
            (λ r p IH →
              inducedMap ((r ∷ p) · q)                                    ≡⟨⟩
              inducedMap ((r PolyConst* q) + (0r ∷ (p · q)))              ≡⟨ step1 r p ⟩
              inducedMap (r PolyConst* q) + inducedMap (0r ∷ (p · q))     ≡⟨ step2 r p ⟩
              inducedMap (r ⋆ q) + inducedMap (0r ∷ (p · q))              ≡⟨ step3 r p ⟩
              r ⋆ inducedMap q + inducedMap (0r ∷ (p · q))                ≡⟨ step4 r p ⟩
              r ⋆ inducedMap q + (0a + x · inducedMap (p · q))            ≡⟨ step5 r p ⟩
              r ⋆ inducedMap q + x · inducedMap (p · q)                   ≡⟨ step6 r p IH ⟩
              r ⋆ inducedMap q + x · (inducedMap p · inducedMap q)        ≡⟨ step7 r p ⟩
              r ⋆ (1a · inducedMap q) + (x · inducedMap p) · inducedMap q ≡⟨ step8 r p ⟩
              (r ⋆ 1a) · inducedMap q + (x · inducedMap p) · inducedMap q ≡⟨ sym (·DistL+ _ _ _) ⟩
              (r ⋆ 1a + x · inducedMap p) · inducedMap q                  ≡⟨⟩
              inducedMap (r ∷ p) · inducedMap q ∎)
            (is-set _ _) p
            where step1 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step1 r p = inducedMap+ (r PolyConst* q) (0r ∷ (p Poly* q))

                  step2 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step2 r p i = inducedMap (PolyConst*≡Poly* r q i) + inducedMap (0r ∷ (p Poly* q))

                  step3 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step3 r p i = inducedMap⋆ r q i + inducedMap (0r ∷ (p Poly* q))

                  step4 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step4 r p i = r ⋆ inducedMap q + (0-actsNullifying (CommRing→Ring R) A 1a i + x · inducedMap (p · q))

                  step5 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step5 r p i = r ⋆ inducedMap q + +IdL (x · inducedMap (p · q)) i

                  step6 : (r : ⟨ R ⟩) (p : _) → _ → _ ≡ _
                  step6 r p IH i = r ⋆ inducedMap q + x · IH i

                  step7 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step7 r p i = r ⋆ (sym (·IdL (inducedMap q)) i) + ·Assoc x (inducedMap p) (inducedMap q) i

                  step8 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
                  step8 r p i = sym (⋆AssocL r 1a (inducedMap q)) i + (x · inducedMap p) · inducedMap q

      inducedHom : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A
      fst inducedHom = inducedMap
      snd inducedHom = makeIsAlgebraHom inducedMap1 inducedMap+ inducedMap· inducedMap⋆

      {- Uniqueness -}
      inducedHomUnique : (f : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A)
                         → fst f X ≡ x
                         → f ≡ inducedHom
      inducedHomUnique f fX≡x =
        Σ≡Prop
          (λ _ → isPropIsAlgebraHom _ _ _ _)
          λ i p → pwEq p i
        where
        open IsAlgebraHom (snd f)
        pwEq : (p : ⟨ ListPolyCommAlgebra ⟩) → fst f p ≡ fst inducedHom p
        pwEq =
          ElimProp R
            (λ p → fst f p ≡ fst inducedHom p)
            pres0
            (λ r p IH →
              fst f (r ∷ p)                    ≡[ i ]⟨ fst f ((sym (+IdR r) i) ∷ sym (Poly+Lid p) i) ⟩
              fst f ([ r ] + (0r ∷ p))         ≡[ i ]⟨ fst f ([ useSolver r i ] + sym (X*Poly p) i) ⟩
              fst f (r ⋆ 1a + X · p)           ≡⟨ pres+ (r ⋆ 1a) (X · p) ⟩
              fst f (r ⋆ 1a) + fst f (X · p)   ≡[ i ]⟨ pres⋆ r 1a i + pres· X p i ⟩
              r ⋆ fst f 1a + fst f X · fst f p ≡[ i ]⟨ r ⋆ pres1 i + fX≡x i · fst f p ⟩
              r ⋆ 1a + x · fst f p             ≡[ i ]⟨ r ⋆ 1a + (x · IH i) ⟩
              r ⋆ 1a + x · inducedMap p        ≡⟨⟩
              inducedMap (r ∷ p) ∎)
            (is-set _ _)
          where
            useSolver : (r : ⟨ R ⟩) → r ≡ (r · 1r) + 0r
            useSolver = solve R
