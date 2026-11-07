module Cubical.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.Instances.Rationals

open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open OrderedFieldStr       (snd ℚOrderedField)
open OrderedFieldTheory    ℚOrderedField
open OrderedFieldReasoning ℚOrderedField
open PremetricStr
open PremetricTheory

private
  variable
    ℓK ℓK' ℓM ℓM' ℓN ℓN' : Level

-- Product spaces using the "sup metric", i.e. the ∞-norm of the premetrics.
-- This coincides with the categorical product in PrSpacesⁿ⸴ᴸ⸴ᶜ⸴ᵘᶜ
module ProductSpaceL∞ (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') where
  private
    module M = PremetricStr (snd M)
    module N = PremetricStr (snd N)

  open IsPremetric

  infix 5 _≈×[_]_

  _≈×[_]_ : (⟨ M ⟩ × ⟨ N ⟩) → ℚ₊ → (⟨ M ⟩ × ⟨ N ⟩) → Type (ℓ-max ℓM' ℓN')
  (x₁ , x₂) ≈×[ ε ] (y₁ , y₂) = x₁ M.≈[ ε ] y₁ × x₂ N.≈[ ε ] y₂

  isPremetric× : IsPremetric _≈×[_]_
  isPremetric× .is-set                      = isSet× M.is-set N.is-set
  isPremetric× .isProp≈ x y ε               = isProp× (M.isProp≈ _ _ ε) (N.isProp≈ _ _ ε)
  isPremetric× .isRefl≈ x ε .fst            = M.isRefl≈ _ ε
  isPremetric× .isRefl≈ x ε .snd            = N.isRefl≈ _ ε
  isPremetric× .isSym≈  x y ε x≈y .fst      = M.isSym≈ _ _ ε (fst x≈y)
  isPremetric× .isSym≈  x y ε x≈y .snd      = N.isSym≈ _ _ ε (snd x≈y)
  isPremetric× .isSeparated≈ x y x≈y i .fst = M.isSeparated≈ _ _ (fst ∘ x≈y) i
  isPremetric× .isSeparated≈ x y x≈y i .snd = N.isSeparated≈ _ _ (snd ∘ x≈y) i
  isPremetric× .isTriangular≈ x y z ε δ x≈y y≈z .fst =
    M.isTriangular≈ _ _ _ ε δ (fst x≈y) (fst y≈z)
  isPremetric× .isTriangular≈ x y z ε δ x≈y y≈z .snd =
    N.isTriangular≈ _ _ _ ε δ (snd x≈y) (snd y≈z)
  isPremetric× .isRounded≈ x y ε x≈y = do
    (δM , δM<ε , x₁≈[δM]y₁) ← M.isRounded≈ _ _ ε (fst x≈y)
    (δN , δN<ε , x₂≈[δN]y₂) ← N.isRounded≈ _ _ ε (snd x≈y)
    return
      ( max₊ δM δN
      , max₊LUB< δM δN ε δM<ε δN<ε
      , isMonotone≈≤ M (L≤⊔ {b = ⟨ δN ⟩₊}) x₁≈[δM]y₁
      , isMonotone≈≤ N (R≤⊔ {a = ⟨ δM ⟩₊}) x₂≈[δN]y₂)

  ×PremetricSpace : PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
  fst ×PremetricSpace = ⟨ M ⟩ × ⟨ N ⟩
  _≈[_]_      (snd ×PremetricSpace) = _≈×[_]_
  isPremetric (snd ×PremetricSpace) = isPremetric×

-- Shorter notation
_×PrSp_ : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN'
        → PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
M ×PrSp N = ProductSpaceL∞.×PremetricSpace M N

module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓM ℓM'} where

  open IsIsometry
  open IsNonExpansive
  open IsLipschitzWith
  open IsContinuousAt
  open IsUContinuous

  π₁ⁿ : NE[ M ×PrSp N , M ]
  fst π₁ⁿ = fst
  pres≈ (snd π₁ⁿ) = λ _ _ _ → fst

  π₂ⁿ : NE[ M ×PrSp N , N ]
  fst π₂ⁿ = snd
  pres≈ (snd π₂ⁿ) = λ _ _ _ → snd

  π₁ᴸ : L[ M ×PrSp N , M ]
  π₁ᴸ = NE→L π₁ⁿ

  π₂ᴸ : L[ M ×PrSp N , N ]
  π₂ᴸ = NE→L π₂ⁿ

  π₁ᵘᶜ : UC[ M ×PrSp N , M ]
  π₁ᵘᶜ = NE→UC π₁ⁿ

  π₂ᵘᶜ : UC[ M ×PrSp N , N ]
  π₂ᵘᶜ = NE→UC π₂ⁿ

  π₁ᶜ : C[ M ×PrSp N , M ]
  π₁ᶜ = NE→C π₁ⁿ

  π₂ᶜ : C[ M ×PrSp N , N ]
  π₂ᶜ = NE→C π₂ⁿ

  module _ {K : PremetricSpace ℓK ℓK'} where

    ⟨_,_⟩ᴵ : Isometry[ K , M ] → Isometry[ K , N ] → Isometry[ K , M ×PrSp N ]
    fst (fst ⟨ f , g ⟩ᴵ x) = fst f x
    snd (fst ⟨ f , g ⟩ᴵ x) = fst g x
    pres≈ (snd ⟨ f , g ⟩ᴵ) x ε y =
      propBiimpl→Equiv (isProp≈ (snd K) x y ε) (isProp≈ (snd (M ×PrSp N)) _ _ ε)
        (λ x≈y → equivFun (pres≈ (snd f) x ε y) x≈y , equivFun (pres≈ (snd g) x ε y) x≈y)
        λ (fx≈fy , _) → invEq (pres≈ (snd f) x ε y) fx≈fy
        -- alternative proof for the line above:
        -- λ (_ , gx≈gy) → invEq (pres≈ (snd g) x ε y) gx≈gy

    ⟨_,_⟩ⁿ : NE[ K , M ] → NE[ K , N ] → NE[ K , M ×PrSp N ]
    fst (fst ⟨ f , g ⟩ⁿ x) = fst f x
    snd (fst ⟨ f , g ⟩ⁿ x) = fst g x
    fst (pres≈ (snd ⟨ f , g ⟩ⁿ) x y ε x≈y) = pres≈ (snd f) x y ε x≈y
    snd (pres≈ (snd ⟨ f , g ⟩ⁿ) x y ε x≈y) = pres≈ (snd g) x y ε x≈y

    ⟨_,_⟩ᴸ : L[ K , M ] → L[ K , N ] → L[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᴸ = λ x → fst f x , fst g x
    snd ⟨ f , g ⟩ᴸ = do
      (L , L-lip) ← snd f
      (R , R-lip) ← snd g
      return λ where
        .fst → max₊ L R
        .snd .pres≈ x y ε x≈y .fst → isMonotone≈≤ M
          (L≤⊔ {⟨ L ⟩₊} ≤·[ ⟨ ε ⟩₊ , <-≤-weaken _ _ (snd ε) ]) (L-lip .pres≈ x y ε x≈y)
        .snd .pres≈ x y ε x≈y .snd → isMonotone≈≤ N
          (R≤⊔ {⟨ L ⟩₊} ≤·[ ⟨ ε ⟩₊ , <-≤-weaken _ _ (snd ε) ]) (R-lip .pres≈ x y ε x≈y)

    ⟨_,_⟩ᶜ : C[ K , M ] → C[ K , N ] → C[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᶜ = λ x → fst f x , fst g x
    pres≈ (snd ⟨ f , g ⟩ᶜ x) ε = do
      (δM , x≈[δM]→fx≈[ε]f) ← pres≈ (snd f x) ε
      (δN , x≈[δN]→gx≈[ε]g) ← pres≈ (snd g x) ε
      return
        ( min₊ δM δN
        , λ y x≈y →
          ( x≈[δM]→fx≈[ε]f y (isMonotone≈≤ K (min₊≤L δM δN) x≈y)
          , x≈[δN]→gx≈[ε]g y (isMonotone≈≤ K (min₊≤R δM δN) x≈y)))

    ⟨_,_⟩ᵘᶜ : UC[ K , M ] → UC[ K , N ] → UC[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᵘᶜ = λ x → fst f x , fst g x
    pres≈ (snd ⟨ f , g ⟩ᵘᶜ) ε = do
      (δM , ≈δM→f≈[ε]f) ← pres≈ (snd f) ε
      (δN , ≈δN→g≈[ε]g) ← pres≈ (snd g) ε
      return
        ( min₊ δM δN
        , λ x y x≈y →
          ( ≈δM→f≈[ε]f x y (isMonotone≈≤ K (min₊≤L δM δN) x≈y)
          , ≈δN→g≈[ε]g x y (isMonotone≈≤ K (min₊≤R δM δN) x≈y)))
