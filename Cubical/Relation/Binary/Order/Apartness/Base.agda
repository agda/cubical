{-
  An apartness relation is a relation that distinguishes
  elements which are different from each other
-}
module Cubical.Relation.Binary.Order.Apartness.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsApartness {A : Type ℓ} (_#_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isapartness

  field
    is-set : isSet A
    is-prop-valued : isPropValued _#_
    is-irrefl : isIrrefl _#_
    is-cotrans : isCotrans _#_
    is-sym : isSym _#_

unquoteDecl IsApartnessIsoΣ = declareRecordIsoΣ IsApartnessIsoΣ (quote IsApartness)


record ApartnessStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor apartnessstr

  field
    _#_     : A → A → Type ℓ'
    isApartness : IsApartness _#_

  infixl 7 _#_

  open IsApartness isApartness public

Apartness : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Apartness ℓ ℓ' = TypeWithStr ℓ (ApartnessStr ℓ')

apartness : (A : Type ℓ) → (_#_ : Rel A A ℓ') → IsApartness _#_ → Apartness ℓ ℓ'
apartness A _#_ apart = A , (apartnessstr _#_ apart)

record IsApartnessEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : ApartnessStr ℓ₀' A) (e : A ≃ B) (N : ApartnessStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isapartnessequiv
  -- Shorter qualified names
  private
    module M = ApartnessStr M
    module N = ApartnessStr N

  field
    pres# : (x y : A) → x M.# y ≃ equivFun e x N.# equivFun e y


ApartnessEquiv : (M : Apartness ℓ₀ ℓ₀') (N : Apartness ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
ApartnessEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsApartnessEquiv (M .snd) e (N .snd)

isPropIsApartness : {A : Type ℓ} (_#_ : A → A → Type ℓ') → isProp (IsApartness _#_)
isPropIsApartness _#_ = isOfHLevelRetractFromIso 1 IsApartnessIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued# → isProp×2
                        (isPropΠ λ _ → isProp¬ _)
                        (isPropΠ4 λ _ _ _ _ → squash₁)
                        (isPropΠ3 λ _ _ _ → isPropValued# _ _))

𝒮ᴰ-Apartness : DUARel (𝒮-Univ ℓ) (ApartnessStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Apartness =
  𝒮ᴰ-Record (𝒮-Univ _) IsApartnessEquiv
    (fields:
      data[ _#_ ∣ autoDUARel _ _ ∣ pres# ]
      prop[ isApartness ∣ (λ _ _ → isPropIsApartness _) ])
    where
    open ApartnessStr
    open IsApartness
    open IsApartnessEquiv

ApartnessPath : (M N : Apartness ℓ ℓ') → ApartnessEquiv M N ≃ (M ≡ N)
ApartnessPath = ∫ 𝒮ᴰ-Apartness .UARel.ua

-- an easier way of establishing an equivalence of apartness relations
module _ {P : Apartness ℓ₀ ℓ₀'} {S : Apartness ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = ApartnessStr (P .snd)
    module S = ApartnessStr (S .snd)

  module _ (isMon : ∀ x y → x P.# y → equivFun e x S.# equivFun e y)
           (isMonInv : ∀ x y → x S.# y → invEq e x P.# invEq e y) where
    open IsApartnessEquiv
    open IsApartness

    makeIsApartnessEquiv : IsApartnessEquiv (P .snd) e (S .snd)
    pres# makeIsApartnessEquiv x y = propBiimpl→Equiv (P.isApartness .is-prop-valued _ _)
                                                      (S.isApartness .is-prop-valued _ _)
                                                      (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.# equivFun e y → x P.# y
      isMonInv' x y ex#ey = transport (λ i → retEq e x i P.# retEq e y i) (isMonInv _ _ ex#ey)
