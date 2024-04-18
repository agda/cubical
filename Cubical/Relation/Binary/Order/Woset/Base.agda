{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset.Base where

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
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

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

  pres≺⁻ : (x y : B) → x N.≺ y ≃ invEq e x M.≺ invEq e y
  pres≺⁻ x y = invEquiv
                 (pres≺ (invEq e x) (invEq e y) ∙ₑ
                  substEquiv (N._≺ equivFun e (invEq e y)) (secEq e x) ∙ₑ
                  substEquiv (x N.≺_) (secEq e y))


WosetEquiv : (M : Woset ℓ₀ ℓ₀') (M : Woset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
WosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsWosetEquiv (M .snd) e (N .snd)

invWosetEquiv : {M : Woset ℓ₀ ℓ₀'} {N : Woset ℓ₁ ℓ₁'} → WosetEquiv M N → WosetEquiv N M
invWosetEquiv (M≃N , iswq) = invEquiv M≃N , iswosetequiv (IsWosetEquiv.pres≺⁻ iswq)

compWosetEquiv : {M : Woset ℓ₀ ℓ₀'} {N : Woset ℓ₁ ℓ₁'} {O : Woset ℓ₂ ℓ₂'}
               → WosetEquiv M N → WosetEquiv N O → WosetEquiv M O
compWosetEquiv (M≃N , wqMN) (N≃O , wqNO) = (compEquiv M≃N N≃O)
               , (iswosetequiv (λ x y
               → compEquiv (IsWosetEquiv.pres≺ wqMN x y)
                           (IsWosetEquiv.pres≺ wqNO (equivFun M≃N x) (equivFun M≃N y))))

reflWosetEquiv : {M : Woset ℓ₀ ℓ₀'} → WosetEquiv M M
reflWosetEquiv {M = M} = (idEquiv ⟨ M ⟩) , (iswosetequiv (λ _ _ → idEquiv _))

isPropIsWoset : {A : Type ℓ} (_≺_ : A → A → Type ℓ') → isProp (IsWoset _≺_)
isPropIsWoset _≺_ = isOfHLevelRetractFromIso 1 IsWosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≺ → isProp×2
                         isPropWellFounded
                         (isPropIsWeaklyExtensional _≺_)
                         (isPropΠ5 λ x _ z _ _ → isPropValued≺ x z))

private
  unquoteDecl IsWosetEquivIsoΣ = declareRecordIsoΣ IsWosetEquivIsoΣ (quote IsWosetEquiv)

isPropIsWosetEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                   → (M : WosetStr ℓ₀' A) (e : A ≃ B) (N : WosetStr ℓ₁' B)
                   → isProp (IsWosetEquiv M e N)
isPropIsWosetEquiv M e N = isOfHLevelRetractFromIso 1 IsWosetEquivIsoΣ
  (isPropΠ2 λ x y → isOfHLevel≃ 1
    (IsWoset.is-prop-valued (WosetStr.isWoset M) x y)
    (IsWoset.is-prop-valued (WosetStr.isWoset N) (e .fst x) (e .fst y)))

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

isSetWoset : isSet (Woset ℓ ℓ')
isSetWoset M N = isOfHLevelRespectEquiv 1 (WosetPath M N)
  λ ((f , eqf) , wqf) ((g , eqg) , wqg)
    → Σ≡Prop (λ e → isPropIsWosetEquiv (str M) e (str N))
      (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt (WFI.induction wellM λ a ind
          → isWeaklyExtensional→≺Equiv→≡ _≺ₙ_ weakN (f a) (g a) λ c
            → propBiimpl→Equiv (propN c (f a)) (propN c (g a))
  (λ c≺ₙfa → subst (_≺ₙ g a) (secEq (g , eqg) c)
               (equivFun (IsWosetEquiv.pres≺ wqg (invEq (g , eqg) c) a)
                (subst (_≺ₘ a)
                 (sym
                  (cong (invEq (g , eqg))
                   (sym (secEq (f , eqf) c)
                   ∙ ind (invEq (f , eqf) c)
                    (subst (invEq (f , eqf) c ≺ₘ_) (retEq (f , eqf) a)
                     (equivFun (IsWosetEquiv.pres≺⁻ wqf c (f a)) c≺ₙfa)))
                   ∙ retEq (g , eqg) (invEq (f , eqf) c)))
                 (subst (invEq (f , eqf) c ≺ₘ_)
                   (retEq (f , eqf) a)
                     (equivFun
                       (IsWosetEquiv.pres≺⁻ wqf c (f a)) c≺ₙfa)))))
   λ c≺ₙga → subst (_≺ₙ f a) (secEq (f , eqf) c)
               (equivFun (IsWosetEquiv.pres≺ wqf (invEq (f , eqf) c) a)
                 (subst (_≺ₘ a)
                   (sym
                     (retEq (f , eqf) (invEq (g , eqg) c))
                     ∙ cong (invEq (f , eqf))
                      (ind (invEq (g , eqg) c)
                       (subst (invEq (g , eqg) c ≺ₘ_) (retEq (g , eqg) a)
                        (equivFun (IsWosetEquiv.pres≺⁻ wqg c (g a)) c≺ₙga))
                       ∙ secEq (g , eqg) c))
                   (subst (invEq (g , eqg) c ≺ₘ_)
                     (retEq (g , eqg) a)
                       (equivFun
                         (IsWosetEquiv.pres≺⁻ wqg c (g a)) c≺ₙga)))))))
  where _≺ₘ_ = WosetStr._≺_ (str M)
        _≺ₙ_ = WosetStr._≺_ (str N)

        wosM = WosetStr.isWoset (str M)
        wosN = WosetStr.isWoset (str N)

        wellM = IsWoset.is-well-founded (wosM)

        weakN = IsWoset.is-weakly-extensional (wosN)

        propN = IsWoset.is-prop-valued (wosN)

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
