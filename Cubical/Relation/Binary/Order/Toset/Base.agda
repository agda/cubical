{-
  Tosets are totally-ordered sets,
  i.e. strongly connected posets,
  a poset where every element can be compared
-}
module Cubical.Relation.Binary.Order.Toset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsToset {A : Type ℓ} (_≤_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor istoset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≤_
    is-refl : isRefl _≤_
    is-trans : isTrans _≤_
    is-antisym : isAntisym _≤_
    is-total : isTotal _≤_

unquoteDecl IsTosetIsoΣ = declareRecordIsoΣ IsTosetIsoΣ (quote IsToset)


record TosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor tosetstr

  field
    _≤_     : A → A → Type ℓ'
    isToset : IsToset _≤_

  infixl 7 _≤_

  open IsToset isToset public

Toset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Toset ℓ ℓ' = TypeWithStr ℓ (TosetStr ℓ')

toset : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → IsToset _≤_ → Toset ℓ ℓ'
toset A _≤_ tos = A , (tosetstr _≤_ tos)

record IsTosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : TosetStr ℓ₀' A) (e : A ≃ B) (N : TosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   istosetequiv
  -- Shorter qualified names
  private
    module M = TosetStr M
    module N = TosetStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y


TosetEquiv : (M : Toset ℓ₀ ℓ₀') (N : Toset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
TosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsTosetEquiv (M .snd) e (N .snd)

isPropIsToset : {A : Type ℓ} (_≤_ : A → A → Type ℓ') → isProp (IsToset _≤_)
isPropIsToset _≤_ = isOfHLevelRetractFromIso 1 IsTosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≤ → isProp×3
                         (isPropΠ (λ _ → isPropValued≤ _ _))
                           (isPropΠ5 λ _ _ _ _ _ → isPropValued≤ _ _)
                             (isPropΠ4 λ _ _ _ _ → isSetA _ _)
                               (isPropΠ2 λ _ _ → squash₁))

𝒮ᴰ-Toset : DUARel (𝒮-Univ ℓ) (TosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Toset =
  𝒮ᴰ-Record (𝒮-Univ _) IsTosetEquiv
    (fields:
      data[ _≤_ ∣ autoDUARel _ _ ∣ pres≤ ]
      prop[ isToset ∣ (λ _ _ → isPropIsToset _) ])
    where
    open TosetStr
    open IsToset
    open IsTosetEquiv

TosetPath : (M N : Toset ℓ ℓ') → TosetEquiv M N ≃ (M ≡ N)
TosetPath = ∫ 𝒮ᴰ-Toset .UARel.ua

-- an easier way of establishing an equivalence of tosets
module _ {P : Toset ℓ₀ ℓ₀'} {S : Toset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = TosetStr (P .snd)
    module S = TosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.≤ y → equivFun e x S.≤ equivFun e y)
           (isMonInv : ∀ x y → x S.≤ y → invEq e x P.≤ invEq e y) where
    open IsTosetEquiv
    open IsToset

    makeIsTosetEquiv : IsTosetEquiv (P .snd) e (S .snd)
    pres≤ makeIsTosetEquiv x y = propBiimpl→Equiv (P.isToset .is-prop-valued _ _)
                                                  (S.isToset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≤ equivFun e y → x P.≤ y
      isMonInv' x y ex≤ey = transport (λ i → retEq e x i P.≤ retEq e y i) (isMonInv _ _ ex≤ey)


module TosetReasoning (P' : Toset ℓ ℓ') where
 private P = fst P'
 open TosetStr (snd P')
 open IsToset

 _≤⟨_⟩_ : (x : P) {y z : P} → x ≤ y → y ≤ z → x ≤ z
 x ≤⟨ p ⟩ q = isToset .is-trans x _ _ p q

 _◾ : (x : P) → x ≤ x
 x ◾ = isToset .is-refl x

 infixr 0 _≤⟨_⟩_
 infix  1 _◾
