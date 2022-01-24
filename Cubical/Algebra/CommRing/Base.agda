{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base

open Iso

private
  variable
    ℓ ℓ' : Level

record IsCommRing {R : Type ℓ}
                  (ringStr : RingStr R) : Type ℓ where

  constructor iscommring

  open RawRingStr (RingStr.rawRingStr ringStr) public
  open IsRing (RingStr.isRing ringStr) public
  
  field
    ·Comm : (x y : R) → x · y ≡ y · x

record CommRingStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor commringstr

  field
    ringStr : RingStr A
    isCommRing : IsCommRing ringStr

  open IsCommRing isCommRing public

CommRing : ∀ ℓ → Type (ℓ-suc ℓ)
CommRing ℓ = TypeWithStr ℓ CommRingStr


makeIsCommRing : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
                 (is-setR : isSet R)
                 (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
                 (+-rid : (x : R) → x + 0r ≡ x)
                 (+-rinv : (x : R) → x + (- x) ≡ 0r)
                 (+-comm : (x y : R) → x + y ≡ y + x)
                 (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
                 (·-rid : (x : R) → x · 1r ≡ x)
                 (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
                 (·-comm : (x y : R) → x · y ≡ y · x)
               → IsCommRing (ringstr _ (makeIsRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid
                         (λ x → ·-comm _ _ ∙ ·-rid x) ·-rdist-+
                         (λ x y z → ·-comm _ _ ∙∙ ·-rdist-+ z x y ∙∙ λ i → (·-comm z x i) + (·-comm z y i))))
makeIsCommRing {_+_ = _+_} is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
  iscommring  ·-comm

makeCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
               (is-setR : isSet R)
               (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
               (+-rid : (x : R) → x + 0r ≡ x)
               (+-rinv : (x : R) → x + (- x) ≡ 0r)
               (+-comm : (x y : R) → x + y ≡ y + x)
               (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
               (·-rid : (x : R) → x · 1r ≡ x)
               (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
               (·-comm : (x y : R) → x · y ≡ y · x)
             → CommRing ℓ
makeCommRing 0r 1r _+_ _·_ -_ is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
  _ , commringstr _ (makeIsCommRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm)

CommRingStr→RingStr : {A : Type ℓ} → CommRingStr A → RingStr A
CommRingStr→RingStr (commringstr r H) = r

CommRing→Ring : CommRing ℓ → Ring ℓ
CommRing→Ring (_ , commringstr r H) = _ , r

CommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ') 
CommRingHom R S = RingHom (CommRing→Ring R) (CommRing→Ring S)

record IsCommRingHom {A : Type ℓ} {B : Type ℓ'}
  (R : CommRingStr A) (f : A → B) (S : CommRingStr B) : Type (ℓ-max ℓ ℓ') where
  constructor iscommringhom
  field
    isRingHom : IsRingHom (CommRingStr→RingStr R) f (CommRingStr→RingStr S)

IsCommRingEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : CommRingStr A) (e : A ≃ B) (S : CommRingStr B) → Type (ℓ-max ℓ ℓ')
IsCommRingEquiv R e S = IsCommRingHom R (e .fst) S

CommRingEquiv : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsCommRingEquiv (R .snd) e (S .snd)

isPropIsCommRing : {R : Type ℓ} (ringStr : RingStr R)
             → isProp (IsCommRing ringStr)
isPropIsCommRing ringStr (iscommring RC) (iscommring SC) =
  λ i → iscommring (isPropComm RC SC i)
  where
    open RingStr ringStr
    isPropComm : isProp ((x y : _) → x · y ≡ y · x)
    isPropComm = isPropΠ2 λ _ _ → isSetRing (_  , ringStr) _ _

𝒮ᴰ-CommRing : DUARel (𝒮-Univ ℓ) CommRingStr ℓ
𝒮ᴰ-CommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommRingEquiv
    (fields:
      data[ ringStr ∣ 𝒮ᴰ-Ring ∣ isRingHom ]
      prop[ isCommRing ∣ (λ _ _ → isPropIsCommRing _) ])
 where
  open CommRingStr
  open IsCommRingHom

CommRingPath : (R S : CommRing ℓ) → CommRingEquiv R S ≃ (R ≡ S)
CommRingPath = ∫ 𝒮ᴰ-CommRing .UARel.ua

isSetCommRing : ((R , str) : CommRing ℓ) → isSet R
isSetCommRing (R , str) = str .CommRingStr.is-set
