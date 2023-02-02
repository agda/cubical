{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality

open import Cubical.Induction.WellFounded

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsWoset {A : Type ℓ} (_≺_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iswoset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≺_
    is-well-founded : WellFounded _≺_
    is-weakly-extensional : isWeaklyExtensional _≺_
    is-trans : isTrans _≺_

unquoteDecl IsWosetIsoΣ = declareRecordIsoΣ IsWosetIsoΣ (quote IsWoset)


record WosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor wosetstr

  field
    _≺_     : A → A → Type ℓ'
    isWoset : IsWoset _≺_

  infixl 7 _≺_

  open IsWoset isWoset public

Woset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Woset ℓ ℓ' = TypeWithStr ℓ (WosetStr ℓ')

woset : (A : Type ℓ) (_≺_ : A → A → Type ℓ') (h : IsWoset _≺_) → Woset ℓ ℓ'
woset A _≺_ h = A , wosetstr _≺_ h

record IsWosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : WosetStr ℓ₀' A) (e : A ≃ B) (N : WosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   iswosetequiv
  -- Shorter qualified names
  private
    module M = WosetStr M
    module N = WosetStr N

  field
    pres≺ : (x y : A) → x M.≺ y ≃ equivFun e x N.≺ equivFun e y


WosetEquiv : (M : Woset ℓ₀ ℓ₀') (M : Woset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
WosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsWosetEquiv (M .snd) e (N .snd)

isPropIsWoset : {A : Type ℓ} (_≺_ : A → A → Type ℓ') → isProp (IsWoset _≺_)
isPropIsWoset _≺_ = isOfHLevelRetractFromIso 1 IsWosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≺ → isProp×2
                         isPropWellFounded
                         (isPropIsWeaklyExtensional _≺_)
                         (isPropΠ5 λ x _ z _ _ → isPropValued≺ x z))

𝒮ᴰ-Woset : DUARel (𝒮-Univ ℓ) (WosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Woset =
  𝒮ᴰ-Record (𝒮-Univ _) IsWosetEquiv
    (fields:
      data[ _≺_ ∣ autoDUARel _ _ ∣ pres≺ ]
      prop[ isWoset ∣ (λ _ _ → isPropIsWoset _) ])
    where
    open WosetStr
    open IsWoset
    open IsWosetEquiv

WosetPath : (M N : Woset ℓ ℓ') → WosetEquiv M N ≃ (M ≡ N)
WosetPath = ∫ 𝒮ᴰ-Woset .UARel.ua

-- an easier way of establishing an equivalence of wosets
module _ {P : Woset ℓ₀ ℓ₀'} {S : Woset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = WosetStr (P .snd)
    module S = WosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.≺ y → equivFun e x S.≺ equivFun e y)
           (isMonInv : ∀ x y → x S.≺ y → invEq e x P.≺ invEq e y) where
    open IsWosetEquiv
    open IsWoset

    makeIsWosetEquiv : IsWosetEquiv (P .snd) e (S .snd)
    pres≺ makeIsWosetEquiv x y = propBiimpl→Equiv (P.isWoset .is-prop-valued _ _)
                                                  (S.isWoset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≺ equivFun e y → x P.≺ y
      isMonInv' x y ex≺ey = transport (λ i → retEq e x i P.≺ retEq e y i) (isMonInv _ _ ex≺ey)
