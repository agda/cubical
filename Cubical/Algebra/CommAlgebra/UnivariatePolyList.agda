{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.UnivariatePolyList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

open import Cubical.Tactics.CommRingSolver

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
    Iso.inv (CommAlgChar.CommAlgIso R)
            (ListPoly ,
             constantPolynomialHom R)

  private
    X : ⟨ ListPolyCommAlgebra ⟩
    X = 0r ∷ 1r ∷ []

  {- export the generator 'X' -}
  generator = X

  {- Universal Property -}
  module _ (A : Algebra (CommRing→Ring R) ℓ') where
    open AlgebraStr ⦃...⦄ using (_⋆_; 0a; 1a; ⋆IdL; ⋆DistL+; ⋆DistR+; ⋆AssocL; ⋆AssocR; ⋆Assoc)
    private instance
      _ = snd A
      _ = snd (Algebra→Ring A)
      _ = snd (CommAlgebra→Algebra ListPolyCommAlgebra)

    module _ (x : ⟨ A ⟩) where
      open AlgebraTheory using (⋆AnnihilL; ⋆AnnihilR)
      open RingTheory using (0RightAnnihilates; 0LeftAnnihilates)
      open AbGroupTheory using (comm-4)
      open PolyMod using (ElimProp; elimProp2; isSetPoly)

      inducedMap : ⟨ ListPolyCommAlgebra ⟩ → ⟨ A ⟩
      inducedMap [] = 0a
      inducedMap (a ∷ p) = a ⋆ 1a + (x · inducedMap p)
      inducedMap (drop0 i) = eq i
        where
          eq = 0r ⋆ 1a + (x · 0a) ≡[ i ]⟨  ⋆AnnihilL (CommRing→Ring R) A 1a i + (x · 0a) ⟩
               0a + (x · 0a)      ≡⟨ +IdL (x · 0a) ⟩
               x · 0a             ≡⟨ 0RightAnnihilates (Algebra→Ring A) x ⟩
               0a ∎

      private
        ϕ = inducedMap
        inducedMap1 : ϕ (1r ∷ []) ≡ 1a
        inducedMap1 =
          ϕ [ 1r ]            ≡⟨⟩
          1r ⋆ 1a + (x · 0a)  ≡[ i ]⟨ ⋆IdL 1a i + 0RightAnnihilates (Algebra→Ring A) x i ⟩
          1a + 0a             ≡⟨ +IdR 1a ⟩
          1a ∎

        inducedMapPolyConst⋆ : (r : ⟨ R ⟩) (p : _) → ϕ (r PolyConst* p) ≡ r ⋆ ϕ p
        inducedMapPolyConst⋆ r =
          ElimProp R
            (λ p → ϕ (r PolyConst* p) ≡ r ⋆ ϕ p)
            (ϕ (r PolyConst* []) ≡⟨⟩
             ϕ []       ≡⟨⟩
             0a                  ≡⟨ sym (⋆AnnihilR (CommRing→Ring R) A r) ⟩
             r ⋆ 0a ∎)
            (λ s p IH →
              ϕ (r PolyConst* (s ∷ p))              ≡⟨⟩
              ϕ ((r · s) ∷ (r PolyConst* p))        ≡⟨⟩
              (r · s) ⋆ 1a + x · ϕ (r PolyConst* p) ≡[ i ]⟨ ⋆Assoc r s 1a i + x · IH i ⟩
              r ⋆ (s ⋆ 1a) + x · (r ⋆ ϕ p)          ≡⟨ step s p ⟩
              r ⋆ (s ⋆ 1a) + r ⋆ (x · ϕ p)          ≡⟨ sym (⋆DistR+ r (s ⋆ 1a) (x · ϕ p)) ⟩
              r ⋆ (s ⋆ 1a + x · ϕ p)                ≡⟨⟩
              r ⋆ ϕ (s ∷ p) ∎)
            (is-set _ _)
            where
              step : (s : ⟨ R ⟩) (p : _) → _ ≡ _
              step s p i = r ⋆ (s ⋆ 1a) + sym (⋆AssocR r x (ϕ p)) i

        inducedMap⋆ : (r : ⟨ R ⟩) (p : _) → ϕ (r ⋆ p) ≡ r ⋆ ϕ p
        inducedMap⋆ r p =
          ϕ (r ⋆ p)                   ≡⟨ cong ϕ (sym (PolyConst*≡Poly* r p)) ⟩
          ϕ (r PolyConst* p)          ≡⟨ inducedMapPolyConst⋆ r p ⟩
          r ⋆ ϕ p ∎

        inducedMap+ : (p q : _) → ϕ (p + q) ≡ ϕ p + ϕ q
        inducedMap+ =
          elimProp2 R
            (λ x y → ϕ (x + y) ≡ ϕ x + ϕ y)
            (0a ≡⟨ sym (+IdR _) ⟩ 0a + 0a ∎)
            (λ r p _ →
              ϕ ((r ∷ p) + []) ≡⟨⟩
              ϕ (r ∷ p)        ≡⟨ sym (+IdR _) ⟩
              (ϕ (r ∷ p) + 0a) ∎)
            (λ s q _ →
              ϕ ([] + (s ∷ q)) ≡⟨⟩
              ϕ (s ∷ q)        ≡⟨ sym (+IdL _) ⟩
              0a + ϕ (s ∷ q)   ∎)
            (λ r s p q IH →
              ϕ ((r ∷ p) + (s ∷ q))                   ≡⟨⟩
              ϕ (r + s ∷ p + q)                       ≡⟨⟩
              (r + s) ⋆ 1a + x · ϕ (p + q)            ≡[ i ]⟨ (r + s) ⋆ 1a + x · IH i ⟩
              (r + s) ⋆ 1a + (x · (ϕ p + ϕ q))        ≡[ i ]⟨ step1 r s p q i ⟩
              (r ⋆ 1a + s ⋆ 1a) + (x · ϕ p + x · ϕ q) ≡⟨ comm-4 (Algebra→AbGroup A) _ _ _ _ ⟩
              (r ⋆ 1a + x · ϕ p) + (s ⋆ 1a + x · ϕ q) ≡⟨⟩
              ϕ (r ∷ p) + ϕ (s ∷ q) ∎)
            (is-set _ _)
            where step1 : (r s : ⟨ R ⟩) (p q : _) → _ ≡ _
                  step1 r s p q i = ⋆DistL+ r s 1a i + ·DistR+ x (ϕ p) (ϕ q) i
                  M = (AbGroup→CommMonoid (Algebra→AbGroup A))

        inducedMap· : (p q : _) → ϕ (p · q) ≡ ϕ p · ϕ q
        inducedMap· p q =
          ElimProp R
            (λ p → ϕ (p · q) ≡ ϕ p · ϕ q)
            (ϕ ([] · q)      ≡⟨⟩
             ϕ []            ≡⟨⟩
             0a                       ≡⟨ sym (0LeftAnnihilates (Algebra→Ring A) _) ⟩
             0a · ϕ q ∎)
            (λ r p IH →
              ϕ ((r ∷ p) · q)                           ≡⟨⟩
              ϕ ((r PolyConst* q) + (0r ∷ (p · q)))     ≡⟨ step1 r p ⟩
              ϕ (r PolyConst* q) + ϕ (0r ∷ (p · q))     ≡⟨ step2 r p ⟩
              ϕ (r ⋆ q) + ϕ (0r ∷ (p · q))              ≡⟨ step3 r p ⟩
              r ⋆ ϕ q + ϕ (0r ∷ (p · q))                ≡⟨ step4 r p ⟩
              r ⋆ ϕ q + (0a + x · ϕ (p · q))            ≡⟨ step5 r p ⟩
              r ⋆ ϕ q + x · ϕ (p · q)                   ≡⟨ step6 r p IH ⟩
              r ⋆ ϕ q + x · (ϕ p · ϕ q)                 ≡⟨ step7 r p ⟩
              r ⋆ (1a · ϕ q) + (x · ϕ p) · ϕ q          ≡⟨ step8 r p ⟩
              (r ⋆ 1a) · ϕ q + (x · ϕ p) · ϕ q          ≡⟨ sym (·DistL+ _ _ _) ⟩
              (r ⋆ 1a + x · ϕ p) · ϕ q                  ≡⟨⟩
              ϕ (r ∷ p) · ϕ q ∎)
            (is-set _ _) p
          where
            step1 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step1 r p = inducedMap+ (r PolyConst* q) (0r ∷ (p Poly* q))

            step2 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step2 r p i = ϕ (PolyConst*≡Poly* r q i) + ϕ (0r ∷ (p Poly* q))

            step3 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step3 r p i = inducedMap⋆ r q i + ϕ (0r ∷ (p Poly* q))

            step4 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step4 r p i = r ⋆ ϕ q + (⋆AnnihilL (CommRing→Ring R) A 1a i + x · ϕ (p · q))

            step5 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step5 r p i = r ⋆ ϕ q + +IdL (x · ϕ (p · q)) i

            step6 : (r : ⟨ R ⟩) (p : _) → _ → _ ≡ _
            step6 r p IH i = r ⋆ ϕ q + x · IH i

            step7 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step7 r p i = r ⋆ (sym (·IdL (ϕ q)) i) + ·Assoc x (ϕ p) (ϕ q) i

            step8 : (r : ⟨ R ⟩) (p : _) → _ ≡ _
            step8 r p i = sym (⋆AssocL r 1a (ϕ q)) i + (x · ϕ p) · ϕ q

      inducedHom : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A
      fst inducedHom = inducedMap
      snd inducedHom = makeIsAlgebraHom inducedMap1 inducedMap+ inducedMap· inducedMap⋆

      inducedMapGenerator : ϕ X ≡ x
      inducedMapGenerator =
        0r ⋆ 1a + (x · ϕ (1r ∷ [])) ≡[ i ]⟨  ⋆AnnihilL
                                     (CommRing→Ring R) A 1a i + (x · ϕ (1r ∷ [])) ⟩
        0a + (x · ϕ (1r ∷ []))      ≡⟨ +IdL _ ⟩
        x · ϕ (1r ∷ [])             ≡[ i ]⟨ x · inducedMap1 i ⟩
        x · 1a                      ≡⟨ ·IdR _ ⟩
        x ∎

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
            useSolver r = solve! R


    {- Reforumlation in terms of the R-AlgebraHom from R[X] to A -}
    indcuedHomEquivalence : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A ≃ ⟨ A ⟩
    fst indcuedHomEquivalence f = fst f X
    fst (fst (equiv-proof (snd indcuedHomEquivalence) x)) = inducedHom x
    snd (fst (equiv-proof (snd indcuedHomEquivalence) x)) = inducedMapGenerator x
    snd (equiv-proof (snd indcuedHomEquivalence) x) (g , gX≡x) =
      Σ≡Prop (λ _ → is-set _ _) (sym (inducedHomUnique x g gX≡x))

    equalByUMP : (f g : AlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra) A)
                 → fst f X ≡ fst g X
                 → (x : ⟨ ListPolyCommAlgebra ⟩) → fst f x ≡ fst g x
    equalByUMP f g fX≡gX x =
      fst f x                      ≡[ i ]⟨ fst (inducedHomUnique (fst f X) f refl i) x  ⟩
      fst (inducedHom (fst f X)) x ≡[ i ]⟨ fst (inducedHom (fX≡gX i)) x ⟩
      fst (inducedHom (fst g X)) x ≡[ i ]⟨ fst (inducedHomUnique (fst g X) g refl (~ i)) x ⟩
      fst g x ∎

  {- A corollary, which is useful for constructing isomorphisms to
     algebras with the same universal property -}
  isIdByUMP : (f : CommAlgebraHom ListPolyCommAlgebra ListPolyCommAlgebra)
              → fst f X ≡ X
              → (x : ⟨ ListPolyCommAlgebra ⟩) → fst f x ≡ x
  isIdByUMP f =
    equalByUMP (CommAlgebra→Algebra ListPolyCommAlgebra)
               f
               (idAlgebraHom (CommAlgebra→Algebra ListPolyCommAlgebra))
    where open AlgebraHoms using (idAlgebraHom)
