{-
  Prosets are preordered sets; a set with a reflexive, transitive relation
-}
module Cubical.Relation.Binary.Order.Proset.Base where

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

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsProset {A : Type ℓ} (_≲_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isproset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≲_
    is-refl : isRefl _≲_
    is-trans : isTrans _≲_

unquoteDecl IsProsetIsoΣ = declareRecordIsoΣ IsProsetIsoΣ (quote IsProset)


record ProsetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor prosetstr

  field
    _≲_     : A → A → Type ℓ'
    isProset : IsProset _≲_

  infixl 7 _≲_

  open IsProset isProset public

Proset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Proset ℓ ℓ' = TypeWithStr ℓ (ProsetStr ℓ')

proset : (A : Type ℓ) → (_≲_ : Rel A A ℓ') → IsProset _≲_ → Proset ℓ ℓ'
proset A _≲_ pros = A , (prosetstr _≲_ pros)

record IsProsetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : ProsetStr ℓ₀' A) (e : A ≃ B) (N : ProsetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isprosetequiv
  -- Shorter qualified names
  private
    module M = ProsetStr M
    module N = ProsetStr N

  field
    pres≲ : (x y : A) → x M.≲ y ≃ equivFun e x N.≲ equivFun e y


ProsetEquiv : (M : Proset ℓ₀ ℓ₀') (N : Proset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
ProsetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsProsetEquiv (M .snd) e (N .snd)

isPropIsProset : {A : Type ℓ} (_≲_ : A → A → Type ℓ') → isProp (IsProset _≲_)
isPropIsProset _≲_ = isOfHLevelRetractFromIso 1 IsProsetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≲ → isProp×
                        (isPropΠ (λ _ → isPropValued≲ _ _))
                        (isPropΠ4 λ _ _ _ _ → isPropΠ λ _ → isPropValued≲ _ _))

𝒮ᴰ-Proset : DUARel (𝒮-Univ ℓ) (ProsetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Proset =
  𝒮ᴰ-Record (𝒮-Univ _) IsProsetEquiv
    (fields:
      data[ _≲_ ∣ autoDUARel _ _ ∣ pres≲ ]
      prop[ isProset ∣ (λ _ _ → isPropIsProset _) ])
    where
    open ProsetStr
    open IsProset
    open IsProsetEquiv

ProsetPath : (M N : Proset ℓ ℓ') → ProsetEquiv M N ≃ (M ≡ N)
ProsetPath = ∫ 𝒮ᴰ-Proset .UARel.ua

-- an easier way of establishing an equivalence of prosets
module _ {P : Proset ℓ₀ ℓ₀'} {S : Proset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = ProsetStr (P .snd)
    module S = ProsetStr (S .snd)

  module _ (isMon : ∀ x y → x P.≲ y → equivFun e x S.≲ equivFun e y)
           (isMonInv : ∀ x y → x S.≲ y → invEq e x P.≲ invEq e y) where
    open IsProsetEquiv
    open IsProset

    makeIsProsetEquiv : IsProsetEquiv (P .snd) e (S .snd)
    pres≲ makeIsProsetEquiv x y = propBiimpl→Equiv (P.isProset .is-prop-valued _ _)
                                                  (S.isProset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≲ equivFun e y → x P.≲ y
      isMonInv' x y ex≲ey = transport (λ i → retEq e x i P.≲ retEq e y i) (isMonInv _ _ ex≲ey)


module ProsetReasoning (P' : Proset ℓ ℓ') where
 private P = fst P'
 open ProsetStr (snd P')
 open IsProset

 _≲⟨_⟩_ : (x : P) {y z : P} → x ≲ y → y ≲ z → x ≲ z
 x ≲⟨ p ⟩ q = isProset .is-trans x _ _ p q

 _◾ : (x : P) → x ≲ x
 x ◾ = isProset .is-refl x

 infixr 0 _≲⟨_⟩_
 infix  1 _◾
