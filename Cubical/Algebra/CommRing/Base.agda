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
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor iscommring

  field
    isRing : IsRing 0r 1r _+_ _·_ -_
    ·Comm : (x y : R) → x · y ≡ y · x

  open IsRing isRing public

record CommRingStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor commringstr

  field
    0r         : A
    1r         : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    isCommRing : IsCommRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

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
               → IsCommRing 0r 1r _+_ _·_ -_
makeIsCommRing {_+_ = _+_} is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
  iscommring (makeIsRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid
                         (λ x → ·-comm _ _ ∙ ·-rid x) ·-rdist-+
                         (λ x y z → ·-comm _ _ ∙∙ ·-rdist-+ z x y ∙∙ λ i → (·-comm z x i) + (·-comm z y i))) ·-comm

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
  _ , commringstr _ _ _ _ _ (makeIsCommRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm)

CommRingStr→RingStr : {A : Type ℓ} → CommRingStr A → RingStr A
CommRingStr→RingStr (commringstr _ _ _ _ _ H) = ringstr _ _ _ _ _ (IsCommRing.isRing H)

CommRing→Ring : CommRing ℓ → Ring ℓ
CommRing→Ring (_ , commringstr _ _ _ _ _ H) = _ , ringstr _ _ _ _ _ (IsCommRing.isRing H)

CommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingHom R S = RingHom (CommRing→Ring R) (CommRing→Ring S)

IsCommRingEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : CommRingStr A) (e : A ≃ B) (S : CommRingStr B) → Type (ℓ-max ℓ ℓ')
IsCommRingEquiv R e S = IsRingHom (CommRingStr→RingStr R) (e .fst) (CommRingStr→RingStr S)

CommRingEquiv : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsCommRingEquiv (R .snd) e (S .snd)

isPropIsCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsCommRing 0r 1r _+_ _·_ -_)
isPropIsCommRing 0r 1r _+_ _·_ -_ (iscommring RR RC) (iscommring SR SC) =
  λ i → iscommring (isPropIsRing _ _ _ _ _ RR SR i)
                   (isPropComm RC SC i)
  where
  isSetR : isSet _
  isSetR = RR .IsRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x · y ≡ y · x)
  isPropComm = isPropΠ2 λ _ _ → isSetR _ _

𝒮ᴰ-CommRing : DUARel (𝒮-Univ ℓ) CommRingStr ℓ
𝒮ᴰ-CommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isCommRing ∣ (λ _ _ → isPropIsCommRing _ _ _ _ _) ])
 where
  open CommRingStr
  open IsRingHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

CommRingPath : (R S : CommRing ℓ) → CommRingEquiv R S ≃ (R ≡ S)
CommRingPath = ∫ 𝒮ᴰ-CommRing .UARel.ua

isSetCommRing : ((R , str) : CommRing ℓ) → isSet R
isSetCommRing (R , str) = str .CommRingStr.is-set
