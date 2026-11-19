module Cubical.Relation.Premetric.Instances.Scaled where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open PremetricStr
open PremetricTheory

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module Scaled (M : PremetricSpace ℓM ℓM') (L : ℚ₊) where
  private
    module M = PremetricStr (snd M)

  open IsPremetric

  infix 5 _≈[·_]_

  _≈[·_]_ : ⟨ M ⟩ → ℚ₊ → ⟨ M ⟩ → Type ℓM'
  x ≈[· ε ] y = x M.≈[ L ·₊ ε ] y

  isPremetricScaled : IsPremetric _≈[·_]_
  isPremetricScaled .is-set        = M.is-set
  isPremetricScaled .isProp≈       = λ _ _ _ → M.isProp≈ _ _ _
  isPremetricScaled .isRefl≈       = λ _ _   → M.isRefl≈ _ _
  isPremetricScaled .isSym≈        = λ _ _ _ → M.isSym≈ _ _ _
  isPremetricScaled .isSeparated≈  = λ _ _ ≈L· →
    M.isSeparated≈ _ _ λ ε → subst≈ M _ _ (·₊/₊ ε L) (≈L· (ε ₊/₊ L))
  isPremetricScaled .isTriangular≈ = λ _ _ _ _ _ →
    (subst≈ M _ _ (sym (ℚ.·DistL+ ⟨ L ⟩₊ _ _)) ∘_) ∘ M.isTriangular≈ _ _ _ _ _
  isPremetricScaled .isRounded≈    = λ _ _ ε x≈[Lε]y → do
    (δ , δ<Lε , x≈[δ]y) ← M.isRounded≈ _ _ (L ·₊ ε) x≈[Lε]y
    return (δ ₊/₊ L , <·₊→₊/₊< δ L ε δ<Lε , subst≈ M _ _ (sym (·₊/₊ δ L)) x≈[δ]y)

  ·PremetricSpace : PremetricSpace ℓM ℓM'
  fst ·PremetricSpace = ⟨ M ⟩
  _≈[_]_      (snd ·PremetricSpace) = _≈[·_]_
  isPremetric (snd ·PremetricSpace) = isPremetricScaled

  ·isCauchy→isCauchy/ : ∀ x → isCauchy ·PremetricSpace x → isCauchy M (x ∘ (_₊/₊ L))
  ·isCauchy→isCauchy/ x xc ε δ = subst≈ M _ _
    (cong (⟨ L ⟩₊ ℚ.·_) (sym (ℚ.·DistR+ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊)) ∙ ·₊/₊ (ε +₊ δ) L)
    (xc (ε ₊/₊ L) (δ ₊/₊ L))

  isComplete· : isComplete M → isComplete ·PremetricSpace
  fst (isComplete· Mcomp x xc) = fst (Mcomp _ (·isCauchy→isCauchy/ x xc))
  snd (isComplete· Mcomp x xc) = λ ε θ →
    subst2 (M._≈[_] fst (Mcomp _ (·isCauchy→isCauchy/ x xc)))
      (cong x (ℚ₊≡ (sym (ℚ.·Assoc ⟨ L ⟩₊ _ _) ∙ ·₊/₊ ε L)))
      (ℚ₊≡ (sym (ℚ.·DistL+ ⟨ L ⟩₊ _ _)))
      (snd (Mcomp _ (·isCauchy→isCauchy/ x xc)) (L ·₊ ε) (L ·₊ θ))

-- Shorter notation
_·₊PrSp_ : ℚ₊ → PremetricSpace ℓM ℓM' → PremetricSpace ℓM ℓM'
L ·₊PrSp M = Scaled.·PremetricSpace M L

module _ (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') (L : ℚ₊) where

  open Iso
  open IsNonExpansive
  open IsLipschitzWith

  L[,]≅NE[,·] : Iso (Σ[ f ∈ _ ] IsLipschitzWith (snd M) f (snd N) L) NE[ M , L ·₊PrSp N ]
  fst (fun L[,]≅NE[,·] f)         = fst f
  pres≈ (snd (fun L[,]≅NE[,·] f)) = pres≈ (snd f)
  fst (inv L[,]≅NE[,·] f)         = fst f
  pres≈ (snd (inv L[,]≅NE[,·] f)) = pres≈ (snd f)
  sec L[,]≅NE[,·] f               = NE≡ refl
  ret L[,]≅NE[,·] f               = Σ≡Prop (λ h → isPropIsLipschitzWith _ h _ L) refl

  L[,]≃NE[,·] : (Σ[ f ∈ _ ] IsLipschitzWith (snd M) f (snd N) L) ≃ NE[ M , L ·₊PrSp N ]
  L[,]≃NE[,·] = isoToEquiv L[,]≅NE[,·]
