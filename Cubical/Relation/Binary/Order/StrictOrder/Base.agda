{-
  Strict orders are linear orders that aren't connected,
  or a quasiorder with comparison
-}
module Cubical.Relation.Binary.Order.StrictOrder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary.Properties

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsStrictOrder {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isstrictorder

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_
    is-irrefl : isIrrefl _<_
    is-trans : isTrans _<_
    is-asym : isAsym _<_
    is-weakly-linear : isWeaklyLinear _<_

unquoteDecl IsStrictOrderIsoΣ = declareRecordIsoΣ IsStrictOrderIsoΣ (quote IsStrictOrder)


record StrictOrderStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor strictorderstr

  field
    _<_     : A → A → Type ℓ'
    isStrictOrder : IsStrictOrder _<_

  infixl 7 _<_

  open IsStrictOrder isStrictOrder public

StrictOrder : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
StrictOrder ℓ ℓ' = TypeWithStr ℓ (StrictOrderStr ℓ')

strictorder : (A : Type ℓ) → (_<_ : Rel A A ℓ') → IsStrictOrder _<_ → StrictOrder ℓ ℓ'
strictorder A _<_ strict = A , (strictorderstr _<_ strict)

record IsStrictOrderEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : StrictOrderStr ℓ₀' A) (e : A ≃ B) (N : StrictOrderStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isstrictorderequiv
  -- Shorter qualified names
  private
    module M = StrictOrderStr M
    module N = StrictOrderStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y


StrictOrderEquiv : (M : StrictOrder ℓ₀ ℓ₀') (M : StrictOrder ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
StrictOrderEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsStrictOrderEquiv (M .snd) e (N .snd)

isPropIsStrictOrder : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsStrictOrder _<_)
isPropIsStrictOrder _<_ = isOfHLevelRetractFromIso 1 IsStrictOrderIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued< → isProp×3 (isPropΠ (λ x → isProp¬ (x < x)))
                                 (isPropΠ5 (λ _ _ _ _ _ → isPropValued< _ _))
                                 (isPropΠ3 (λ x y _ → isProp¬ (y < x)))
                                 (isPropΠ4 λ _ _ _ _ → squash₁))

𝒮ᴰ-StrictOrder : DUARel (𝒮-Univ ℓ) (StrictOrderStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-StrictOrder =
  𝒮ᴰ-Record (𝒮-Univ _) IsStrictOrderEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isStrictOrder ∣ (λ _ _ → isPropIsStrictOrder _) ])
    where
    open StrictOrderStr
    open IsStrictOrder
    open IsStrictOrderEquiv

StrictOrderPath : (M N : StrictOrder ℓ ℓ') → StrictOrderEquiv M N ≃ (M ≡ N)
StrictOrderPath = ∫ 𝒮ᴰ-StrictOrder .UARel.ua

-- an easier way of establishing an equivalence of strict orders
module _ {P : StrictOrder ℓ₀ ℓ₀'} {S : StrictOrder ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = StrictOrderStr (P .snd)
    module S = StrictOrderStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsStrictOrderEquiv
    open IsStrictOrder

    makeIsStrictOrderEquiv : IsStrictOrderEquiv (P .snd) e (S .snd)
    pres< makeIsStrictOrderEquiv x y = propBiimpl→Equiv (P.isStrictOrder .is-prop-valued _ _)
                                                  (S.isStrictOrder .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex<ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex<ey)
