{-
  Quosets, or quasiordered sets, are posets where the relation is strict,
  i.e. irreflexive rather than reflexive
-}
module Cubical.Relation.Binary.Order.Quoset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

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

record IsQuoset {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isquoset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_
    is-irrefl : isIrrefl _<_
    is-trans : isTrans _<_
    is-asym : isAsym _<_

unquoteDecl IsQuosetIsoΣ = declareRecordIsoΣ IsQuosetIsoΣ (quote IsQuoset)


record QuosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor quosetstr

  field
    _<_     : A → A → Type ℓ'
    isQuoset : IsQuoset _<_

  infixl 7 _<_

  open IsQuoset isQuoset public

Quoset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Quoset ℓ ℓ' = TypeWithStr ℓ (QuosetStr ℓ')

quoset : (A : Type ℓ) → (_<_ : Rel A A ℓ') → IsQuoset _<_ → Quoset ℓ ℓ'
quoset A _<_ quo = A , (quosetstr _<_ quo)

record IsQuosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : QuosetStr ℓ₀' A) (e : A ≃ B) (N : QuosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isquosetequiv
  -- Shorter qualified names
  private
    module M = QuosetStr M
    module N = QuosetStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y


QuosetEquiv : (M : Quoset ℓ₀ ℓ₀') (M : Quoset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
QuosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsQuosetEquiv (M .snd) e (N .snd)

isPropIsQuoset : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsQuoset _<_)
isPropIsQuoset _<_ = isOfHLevelRetractFromIso 1 IsQuosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued< → isProp×2 (isPropΠ (λ x → isProp¬ (x < x)))
                                 (isPropΠ5 (λ _ _ _ _ _ → isPropValued< _ _))
                                 (isPropΠ3 λ x y _ → isProp¬ (y < x)))

𝒮ᴰ-Quoset : DUARel (𝒮-Univ ℓ) (QuosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Quoset =
  𝒮ᴰ-Record (𝒮-Univ _) IsQuosetEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isQuoset ∣ (λ _ _ → isPropIsQuoset _) ])
    where
    open QuosetStr
    open IsQuoset
    open IsQuosetEquiv

QuosetPath : (M N : Quoset ℓ ℓ') → QuosetEquiv M N ≃ (M ≡ N)
QuosetPath = ∫ 𝒮ᴰ-Quoset .UARel.ua

-- an easier way of establishing an equivalence of strict posets
module _ {P : Quoset ℓ₀ ℓ₀'} {S : Quoset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = QuosetStr (P .snd)
    module S = QuosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsQuosetEquiv
    open IsQuoset

    makeIsQuosetEquiv : IsQuosetEquiv (P .snd) e (S .snd)
    pres< makeIsQuosetEquiv x y = propBiimpl→Equiv (P.isQuoset .is-prop-valued _ _)
                                                  (S.isQuoset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex<ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex<ey)
