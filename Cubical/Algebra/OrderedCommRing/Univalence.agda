module Cubical.Algebra.OrderedCommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

private
  variable
    ℓ ℓ' ℓ<≤ ℓ<≤' : Level

open Iso

𝒮ᴰ-OrderedCommRing : DUARel (𝒮-Univ ℓ) (OrderedCommRingStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-OrderedCommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsOrderedCommRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ un ∣ pres- ]
      data[ _<_ ∣ binRel ∣ pres< ]
      data[ _≤_ ∣ binRel ∣ pres≤ ]
      prop[ isOrderedCommRing ∣ (λ _ _ → isPropIsOrderedCommRing _ _ _ _ _ _ _) ])
  where
    open OrderedCommRingStr
    open IsOrderedCommRingEquiv

    -- faster with some sharing
    null = autoDUARel (𝒮-Univ _) (λ A → A)
    un = autoDUARel (𝒮-Univ _) (λ A → A → A)
    bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)
    binRel = autoDUARel (𝒮-Univ _) (λ A → A → A → Type _)

OrderedCommRingPath : (R S : OrderedCommRing ℓ ℓ') → OrderedCommRingEquiv R S ≃ (R ≡ S)
OrderedCommRingPath = ∫ 𝒮ᴰ-OrderedCommRing .UARel.ua

uaOrderedCommRing : {A B : OrderedCommRing ℓ ℓ'} → OrderedCommRingEquiv A B → A ≡ B
uaOrderedCommRing {A = A} {B = B} = equivFun (OrderedCommRingPath A B)

OrderedCommRingIso : OrderedCommRing ℓ ℓ<≤ → OrderedCommRing ℓ' ℓ<≤' → Type _
OrderedCommRingIso R S =
  Σ[ e ∈ Iso (R .fst) (S .fst) ] IsOrderedCommRingMono (R .snd) (e .fun) (S .snd)

OrderedCommRingEquivIsoOrderedCommRingIso : (R : OrderedCommRing ℓ  ℓ<≤)
                                          → (S : OrderedCommRing ℓ' ℓ<≤')
                                          → Iso (OrderedCommRingEquiv R S)
                                                (OrderedCommRingIso R S)
OrderedCommRingEquivIsoOrderedCommRingIso R S = OCREquivIsoOCRIso
  where
    open Iso
    OCREquivIsoOCRIso : Iso (OrderedCommRingEquiv R S) (OrderedCommRingIso R S)
    fst (fun OCREquivIsoOCRIso e) = equivToIso (fst e)
    snd (fun OCREquivIsoOCRIso e) = snd (OrderedCommRingEquiv→OrderedCommRingMono e)
    fst (inv OCREquivIsoOCRIso e) = isoToEquiv (fst e)
    snd (inv OCREquivIsoOCRIso e) = makeIsOrderedCommRingEquivFromIsMono (isoToEquiv (fst e)) (snd e)
    sec OCREquivIsoOCRIso e =
      Σ≡Prop (λ f → isPropIsOrderedCommRingMono _ (fun f) _) (
      Iso≡Set (OrderedCommRingStr.is-set (snd R)) (OrderedCommRingStr.is-set (snd S))
        _ _ (λ x → refl) (λ x → refl))
    ret OCREquivIsoOCRIso e =
      Σ≡Prop (λ f → isPropIsOrderedCommRingEquiv _ f _) (equivEq refl)

isGroupoidOrderedCommRing : isGroupoid (OrderedCommRing ℓ ℓ')
isGroupoidOrderedCommRing _ _ =
  isOfHLevelRespectEquiv 2 (OrderedCommRingPath _ _) (isSetOrderedCommRingEquiv _ _)
