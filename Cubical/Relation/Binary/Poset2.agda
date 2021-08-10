{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Poset2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
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

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsPoset {A : Type ℓ} (_≤_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isposet

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≤_
    is-refl : isRefl _≤_
    is-trans : isTrans _≤_
    is-antisym : isAntisym _≤_

unquoteDecl IsPosetIsoΣ = declareRecordIsoΣ IsPosetIsoΣ (quote IsPoset)


record PosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor posetstr

  field
    _≤_         : A → A → Type ℓ'
    isPoset : IsPoset _≤_

  infixl 7 _≤_

  open IsPoset isPoset public

Poset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Poset ℓ ℓ' = TypeWithStr ℓ (PosetStr ℓ')

poset : (A : Type ℓ) (_≤_ : A → A → Type ℓ') (h : IsPoset _≤_) → Poset ℓ ℓ'
poset A _≤_ h = A , posetstr _≤_ h

record IsPosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PosetStr ℓ₀' A) (e : A ≃ B) (N : PosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where

  -- Shorter qualified names
  private
    module M = PosetStr M
    module N = PosetStr N

  field
    isMon : (x y : A) → x M.≤ y → equivFun e x N.≤ equivFun e y

open PosetStr
open IsPoset
open IsPosetEquiv

PosetEquiv : (M : Poset ℓ₀ ℓ₀') (M : Poset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
PosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsPosetEquiv (M .snd) e (N .snd)

isPropIsPoset : {A : Type ℓ} (_≤_ : A → A → Type ℓ') → isProp (IsPoset _≤_)
isPropIsPoset _≤_ = isOfHLevelRetractFromIso 1 IsPosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≤ → isProp×2
                         (isPropΠ (λ _ → isPropValued≤ _ _))
                           (isPropΠ5 λ _ _ _ _ _ → isPropValued≤ _ _)
                             (isPropΠ4 λ _ _ _ _ → isSetA _ _))

-- help Evan!!!
-- 𝒮ᴰ-Poset : DUARel (𝒮-Univ (ℓ-max (ℓ-max ℓ ℓ') ℓ')) (PosetStr ℓ') (ℓ-max ℓ ℓ')
-- 𝒮ᴰ-Poset =
--   𝒮ᴰ-Record (𝒮-Univ _) IsPosetEquiv
--     (fields:
--       data[ _≤_ ∣ autoDUARel _ _ ∣ isMon ]
--       prop[ isPoset ∣ (λ _ _ → isPropIsPoset _) ])

-- PosetPath : (M N : Poset ℓ) → PosetEquiv M N ≃ (M ≡ N)
-- PosetPath = ∫ 𝒮ᴰ-Poset .UARel.ua
