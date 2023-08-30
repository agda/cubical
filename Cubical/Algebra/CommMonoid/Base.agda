{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level



record IsCommMonoid {M : Type ℓ}
                    (ε : M) (_·_ : M → M → M) : Type ℓ where
  constructor iscommmonoid

  field
    isMonoid : IsMonoid ε _·_
    ·Comm     : (x y : M) → x · y ≡ y · x

  open IsMonoid isMonoid public

unquoteDecl IsCommMonoidIsoΣ = declareRecordIsoΣ IsCommMonoidIsoΣ (quote IsCommMonoid)

record CommMonoidStr (M : Type ℓ) : Type ℓ where
  constructor commmonoidstr

  field
    ε            : M
    _·_          : M → M → M
    isCommMonoid : IsCommMonoid ε _·_

  infixl 7 _·_

  open IsCommMonoid isCommMonoid public

CommMonoid : ∀ ℓ → Type (ℓ-suc ℓ)
CommMonoid ℓ = TypeWithStr ℓ CommMonoidStr

makeIsCommMonoid : {M : Type ℓ} {ε : M} {_·_ : M → M → M}
                 (is-setM : isSet M)
                 (·Assoc   : (x y z : M) → x · (y · z) ≡ (x · y) · z)
                 (·IdR     : (x : M) → x · ε ≡ x)
                 (·Comm    : (x y : M) → x · y ≡ y · x)
               → IsCommMonoid ε _·_
IsCommMonoid.isMonoid (makeIsCommMonoid is-setM ·Assoc ·IdR ·Comm) =
  makeIsMonoid is-setM ·Assoc ·IdR (λ x → ·Comm _ _ ∙ ·IdR x)
IsCommMonoid.·Comm (makeIsCommMonoid is-setM ·Assoc ·IdR ·Comm) = ·Comm

makeCommMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
               (is-setM : isSet M)
               (·Assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
               (·IdR : (x : M) → x · ε ≡ x)
               (·Comm    : (x y : M) → x · y ≡ y · x)
             → CommMonoid ℓ
fst (makeCommMonoid ε _·_ is-setM ·Assoc ·IdR ·Comm) = _
CommMonoidStr.ε (snd (makeCommMonoid ε _·_ is-setM ·Assoc ·IdR ·Comm)) = ε
CommMonoidStr._·_ (snd (makeCommMonoid ε _·_ is-setM ·Assoc ·IdR ·Comm)) = _·_
CommMonoidStr.isCommMonoid (snd (makeCommMonoid ε _·_ is-setM ·Assoc ·IdR ·Comm)) =
  makeIsCommMonoid is-setM ·Assoc ·IdR ·Comm

CommMonoidStr→MonoidStr : {A : Type ℓ} → CommMonoidStr A → MonoidStr A
CommMonoidStr→MonoidStr (commmonoidstr _ _ H) = monoidstr _ _ (IsCommMonoid.isMonoid H)

CommMonoid→Monoid : CommMonoid ℓ → Monoid ℓ
CommMonoid→Monoid (_ , commmonoidstr  _ _ M) = _ , monoidstr _ _ (IsCommMonoid.isMonoid M)

CommMonoidHom : (L : CommMonoid ℓ) (M : CommMonoid ℓ') → Type (ℓ-max ℓ ℓ')
CommMonoidHom L M = MonoidHom (CommMonoid→Monoid L) (CommMonoid→Monoid M)

IsCommMonoidEquiv : {A : Type ℓ} {B : Type ℓ'}
  (M : CommMonoidStr A) (e : A ≃ B) (N : CommMonoidStr B) → Type (ℓ-max ℓ ℓ')
IsCommMonoidEquiv M e N = IsMonoidHom (CommMonoidStr→MonoidStr M) (e .fst) (CommMonoidStr→MonoidStr N)

CommMonoidEquiv : (M : CommMonoid ℓ) (N : CommMonoid ℓ') → Type (ℓ-max ℓ ℓ')
CommMonoidEquiv M N = Σ[ e ∈ (M .fst ≃ N .fst) ] IsCommMonoidEquiv (M .snd) e (N .snd)

isPropIsCommMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
             → isProp (IsCommMonoid ε _·_)
isPropIsCommMonoid ε _·_  =
  isOfHLevelRetractFromIso 1 IsCommMonoidIsoΣ
    (isPropΣ (isPropIsMonoid ε _·_)
             λ mon → isPropΠ2 (λ _ _ → mon .is-set _ _))
  where
  open IsMonoid

𝒮ᴰ-CommMonoid : DUARel (𝒮-Univ ℓ) CommMonoidStr ℓ
𝒮ᴰ-CommMonoid =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommMonoidEquiv
    (fields:
      data[ ε ∣ autoDUARel _ _ ∣ presε ]
      data[ _·_ ∣ autoDUARel _ _ ∣ pres· ]
      prop[ isCommMonoid ∣ (λ _ _ → isPropIsCommMonoid _ _) ])
  where
  open CommMonoidStr
  open IsMonoidHom

CommMonoidPath : (M N : CommMonoid ℓ) → CommMonoidEquiv M N ≃ (M ≡ N)
CommMonoidPath = ∫ 𝒮ᴰ-CommMonoid .UARel.ua
