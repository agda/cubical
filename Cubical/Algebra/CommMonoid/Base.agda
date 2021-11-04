{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Base

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsCommMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor iscommmonoid

  field
   isMonoid : IsMonoid ε _·_
   comm :  (x y : A) → x · y ≡ y · x

  open IsMonoid isMonoid public

unquoteDecl IsCommMonoidIsoΣ = declareRecordIsoΣ IsCommMonoidIsoΣ (quote IsCommMonoid)

record CommMonoidStr (A : Type ℓ) : Type ℓ where
  constructor commmonoidstr

  field
    ε        : A
    _·_      : A → A → A
    isCommMonoid : IsCommMonoid ε _·_

  infixl 7 _·_

  open IsCommMonoid isCommMonoid public

CommMonoid : ∀ ℓ → Type (ℓ-suc ℓ)
CommMonoid ℓ = TypeWithStr ℓ CommMonoidStr

commmonoid : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsCommMonoid ε _·_) → CommMonoid ℓ
commmonoid A ε _·_ h = A , commmonoidstr ε _·_ h

-- Easier to use constructors
makeIsCommMonoid : {M : Type ℓ} {ε : M} {_·_ : M → M → M}
               (is-setM : isSet M)
               (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : M) → x · ε ≡ x)
               (lid : (x : M) → ε · x ≡ x)
               (comm : (x y : M) → x · y ≡ y · x)
             → IsCommMonoid ε _·_
IsCommMonoid.isMonoid (makeIsCommMonoid is-setM assoc rid lid comm) =
                                        makeIsMonoid is-setM assoc rid lid
IsCommMonoid.comm (makeIsCommMonoid is-setM assoc rid lid comm) = comm

makeCommMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
             (is-setM : isSet M)
             (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : M) → x · ε ≡ x)
             (lid : (x : M) → ε · x ≡ x)
             (comm : (x y : M) → x · y ≡ y · x)
           → CommMonoid ℓ
makeCommMonoid ε _·_ is-setM assoc rid lid comm =
  commmonoid _ ε _·_ (makeIsCommMonoid is-setM assoc rid lid comm)



CommMonoidStr→MonoidStr : {A : Type ℓ} → CommMonoidStr A → MonoidStr A
CommMonoidStr→MonoidStr (commmonoidstr _ _ H) = monoidstr _ _ (IsCommMonoid.isMonoid H)

CommMonoid→Monoid : CommMonoid ℓ → Monoid ℓ
CommMonoid→Monoid (_ , commmonoidstr _ _ H) = _ , monoidstr _ _ (IsCommMonoid.isMonoid H)


CommMonoidHom : (L : CommMonoid ℓ) (M : CommMonoid ℓ') → Type (ℓ-max ℓ ℓ')
CommMonoidHom L M = MonoidHom (CommMonoid→Monoid L) (CommMonoid→Monoid M)

IsCommMonoidEquiv : {A : Type ℓ} {B : Type ℓ'}
  (M : CommMonoidStr A) (e : A ≃ B) (N : CommMonoidStr B) → Type (ℓ-max ℓ ℓ')
IsCommMonoidEquiv M e N = IsMonoidHom (CommMonoidStr→MonoidStr M) (e .fst) (CommMonoidStr→MonoidStr N)

CommMonoidEquiv : (M : CommMonoid ℓ) (N : CommMonoid ℓ') → Type (ℓ-max ℓ ℓ')
CommMonoidEquiv M N = Σ[ e ∈ (M .fst ≃ N .fst) ] IsCommMonoidEquiv (M .snd) e (N .snd)

isPropIsCommMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
             → isProp (IsCommMonoid ε _·_)
isPropIsCommMonoid ε _·_ (iscommmonoid MM MC) (iscommmonoid SM SC) =
  λ i → iscommmonoid (isPropIsMonoid _ _ MM SM i) (isPropComm MC SC i)
  where
  isSetM : isSet _
  isSetM = MM .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x · y ≡ y · x)
  isPropComm = isPropΠ2 λ _ _ → isSetM _ _

𝒮ᴰ-CommMonoid : DUARel (𝒮-Univ ℓ) CommMonoidStr ℓ
𝒮ᴰ-CommMonoid =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommMonoidEquiv
    (fields:
      data[ ε ∣ autoDUARel _ _ ∣ presε ]
      data[ _·_ ∣ autoDUARel _ _ ∣ isHom ]
      prop[ isCommMonoid ∣ (λ _ _ → isPropIsCommMonoid _ _) ])
  where
  open CommMonoidStr
  open IsMonoidHom

CommMonoidPath : (M N : CommMonoid ℓ) → CommMonoidEquiv M N ≃ (M ≡ N)
CommMonoidPath = ∫ 𝒮ᴰ-CommMonoid .UARel.ua
