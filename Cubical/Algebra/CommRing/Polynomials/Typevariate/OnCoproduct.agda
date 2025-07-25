{-
 The goal of this module is to show that for two types I,J, there is an
 isomorphism of algebras

    R[I][J] ≃ R[ I ⊎ J ]

  where '⊎' is the disjoint sum.
-}
module Cubical.Algebra.CommRing.Polynomials.Typevariate.OnCoproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty

private
  variable
    ℓ ℓ' : Level

module CalculatePolynomialsOnCoproduct (R : CommRing ℓ) (I J : Type ℓ) where
  private
    I→I+J : CommRingHom (R [ I ]) (R [ I ⊎ J ])
    I→I+J = inducedHom (R [ I ⊎ J ]) (constPolynomial R (I ⊎ J)) (var ∘ inl)

    to : CommRingHom ((R [ I ]) [ J ]) (R [ I ⊎ J ])
    to = inducedHom (R [ I ⊎ J ]) I→I+J (var ∘ inr)

    constPolynomialIJ : CommRingHom R ((R [ I ]) [ J ])
    constPolynomialIJ = constPolynomial _ _ ∘cr constPolynomial _ _

    evalVarTo : to .fst ∘ var ≡ var ∘ inr
    evalVarTo = evalInduce (R [ I ⊎ J ]) I→I+J (var ∘ inr)

    commConstTo : to ∘cr constPolynomialIJ ≡ constPolynomial _ _
    commConstTo = CommRingHom≡ refl

    mapVars : I ⊎ J → ⟨ (R [ I ]) [ J ] ⟩
    mapVars (inl i) = constPolynomial _ _ $cr var i
    mapVars (inr j) = var j

    to∘MapVars : to .fst ∘ mapVars ≡ var
    to∘MapVars =
      funExt λ {(inl i) → to .fst (constPolynomial _ _ $cr var i)
                              ≡⟨ cong (λ z → z i)
                                      (evalInduce (R [ I ⊎ J ])
                                                  (constPolynomial R (I ⊎ J)) (var ∘ inl)) ⟩
                          var (inl i) ∎;
                (inr j) → (to .fst (var j) ≡⟨ cong (λ z → z j) evalVarTo ⟩ var (inr j) ∎)}

    from : CommRingHom (R [ I ⊎ J ]) ((R [ I ]) [ J ])
    from = inducedHom
               ((R [ I ]) [ J ])
               (constPolynomial (R [ I ]) J ∘cr constPolynomial R I)
               mapVars

    evalVarFrom : from .fst ∘ var ≡ mapVars
    evalVarFrom = evalInduce ((R [ I ]) [ J ]) (constPolynomial (R [ I ]) J ∘cr constPolynomial R I) mapVars

    toFrom : to ∘cr from ≡ (idCommRingHom (R [ I ⊎ J ]))
    toFrom =
      idByIdOnVars
        (to ∘cr from)
        (to .fst ∘ from .fst ∘ constPolynomial R (I ⊎ J) .fst  ≡⟨⟩
         constPolynomial R (I ⊎ J) .fst ∎)
        (to .fst ∘ from .fst ∘ var       ≡⟨ cong (to .fst ∘_) evalVarFrom ⟩
         to .fst ∘ mapVars               ≡⟨ to∘MapVars ⟩
         var ∎)

    {- from and to are R[I]-algebra homomorphisms:
       this is true definitionally for to.
    -}
    fromAlgebraHom : from ∘cr I→I+J ≡ constPolynomial (R [ I ]) J
    fromAlgebraHom =
      hom≡ByValuesOnVars
        ((R [ I ]) [ J ]) (constPolynomial (R [ I ]) J ∘cr constPolynomial R I)
        (from ∘cr I→I+J) (constPolynomial (R [ I ]) J)
        refl refl
        (funExt
        (λ i →  (from ∘cr I→I+J) .fst (var i)
                  ≡⟨ cong (from .fst)
                          (evalOnVars (R [ I ⊎ J ])
                                      (constPolynomial R (I ⊎ J))
                                      (var ∘ inl) i) ⟩
                from .fst (var (inl i))
                  ≡⟨ evalOnVars ((R [ I ]) [ J ])
                     (constPolynomial (R [ I ]) J ∘cr constPolynomial R I)
                     mapVars (inl i) ⟩
                 constPolynomial (R [ I ]) J $cr var i ∎))

    fromTo : from ∘cr to ≡ (idCommRingHom $ (R [ I ]) [ J ])
    fromTo =
      idByIdOnVars
        (from ∘cr to)
        (from .fst ∘ to .fst ∘ constPolynomial (R [ I ]) J .fst ≡⟨⟩
         from .fst ∘ I→I+J .fst ≡⟨ cong fst fromAlgebraHom ⟩
         constPolynomial (R [ I ]) J .fst ∎)
        (from .fst ∘ to .fst ∘ var ≡⟨ cong (from .fst ∘_) (funExt $ evalOnVars (R [ I ⊎ J ]) I→I+J (var ∘ inr) )  ⟩
         from .fst ∘ var ∘ inr     ≡⟨ (funExt $ λ j → evalOnVars _ _ _ (inr j)) ⟩
         var ∎)
