{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Macro
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid    hiding (⟨_⟩)
open import Cubical.Structures.AbGroup   hiding (⟨_⟩)
open import Cubical.Structures.Ring      hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsCommRing {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor iscommring

  field
    isRing : IsRing 0r 1r _+_ _·_ -_
    ·-comm : (x y : R) → x · y ≡ y · x

  open IsRing isRing public

record CommRing : Type (ℓ-suc ℓ) where

  constructor commring

  field
    Carrier    : Type ℓ
    0r         : Carrier
    1r         : Carrier
    _+_        : Carrier → Carrier → Carrier
    _·_        : Carrier → Carrier → Carrier
    -_         : Carrier → Carrier
    isCommRing : IsCommRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsCommRing isCommRing public

-- Extractor for the carrier type
⟨_⟩ : CommRing → Type ℓ
⟨_⟩ = CommRing.Carrier

-- TODO: add makeCommRing

CommRing→Ring : CommRing {ℓ} → Ring
CommRing→Ring (commring _ _ _ _ _ _ H) = ring _ _ _ _ _ _ (IsCommRing.isRing H)

CommRingIso : (R S : CommRing) → Type ℓ
CommRingIso R S = RingIso (CommRing→Ring R) (CommRing→Ring S)

module CommRingΣ-theory {ℓ} where

  open RingΣ-theory

  comm-ring-axioms : (R : Type ℓ) (s : raw-ring-structure R) → Type ℓ
  comm-ring-axioms R (_+_ , 1r , _·_) = ring-axioms R (_+_ , 1r , _·_)
                                      × ((x y : R) → x · y ≡ y · x)

  comm-ring-structure : Type ℓ → Type ℓ
  comm-ring-structure = add-to-structure raw-ring-structure comm-ring-axioms

  CommRingΣ : Type (ℓ-suc ℓ)
  CommRingΣ = TypeWithStr ℓ comm-ring-structure

  comm-ring-iso : StrIso comm-ring-structure ℓ
  comm-ring-iso =
    add-to-iso (join-iso (binaryFunIso pointed-iso)
                         (join-iso pointed-iso (binaryFunIso pointed-iso))) comm-ring-axioms

  isProp-comm-ring-axioms : (R : Type ℓ) (s : raw-ring-structure R)
                          → isProp (comm-ring-axioms R s)
  isProp-comm-ring-axioms R (_·_ , 0r , _+_) =
    isPropΣ (isProp-ring-axioms R (_·_ , 0r , _+_))
            λ { (_ , x , _)→ isPropΠ2 λ _ _ →
                  x .IsMonoid.isSemigroup .IsSemigroup.is-set _ _}

  CommRing→CommRingΣ : CommRing → CommRingΣ
  CommRing→CommRingΣ (commring _ _ _ _ _ _ (iscommring G C)) =
    _ , _ , Ring→RingΣ (ring _ _ _ _ _ _ G) .snd .snd , C

  CommRingΣ→CommRing : CommRingΣ → CommRing
  CommRingΣ→CommRing (_ , _ , G , C) =
    commring _ _ _ _ _ _ (iscommring (RingΣ→Ring (_ , _ , G) .Ring.isRing) C)

  CommRingIsoCommRingΣ : Iso CommRing CommRingΣ
  CommRingIsoCommRingΣ =
    iso CommRing→CommRingΣ CommRingΣ→CommRing (λ _ → refl) (λ _ → refl)

  comm-ring-is-SNS : SNS comm-ring-structure comm-ring-iso
  comm-ring-is-SNS = add-axioms-SNS _ isProp-comm-ring-axioms raw-ring-is-SNS

  CommRingΣPath : (R S : CommRingΣ) → (R ≃[ comm-ring-iso ] S) ≃ (R ≡ S)
  CommRingΣPath = SIP comm-ring-is-SNS

  CommRingIsoΣ : (R S : CommRing) → Type ℓ
  CommRingIsoΣ R S = CommRing→CommRingΣ R ≃[ comm-ring-iso ] CommRing→CommRingΣ S

  CommRingPath : (R S : CommRing) → (CommRingIso R S) ≃ (R ≡ S)
  CommRingPath R S =
    CommRingIso R S   ≃⟨ isoToEquiv RingIsoΣPath ⟩
    CommRingIsoΣ R S  ≃⟨ CommRingΣPath _ _ ⟩
    CommRing→CommRingΣ R ≡ CommRing→CommRingΣ S
      ≃⟨ isoToEquiv (invIso (congIso CommRingIsoCommRingΣ)) ⟩
    R ≡ S ■

-- Extract the characterization of equality of groups
CommRingPath : (R S : CommRing {ℓ}) → (CommRingIso R S) ≃ (R ≡ S)
CommRingPath = CommRingΣ-theory.CommRingPath

isPropIsCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsCommRing 0r 1r _+_ _·_ -_)
isPropIsCommRing 0r 1r _+_ _·_ -_ (iscommring RR RC) (iscommring SR SC) =
  λ i → iscommring (isPropIsRing _ _ _ _ _ RR SR i)
                   (isPropComm RC SC i)
  where
  isSetR : isSet _
  isSetR = RR .IsRing.·-isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x · y ≡ y · x)
  isPropComm = isPropΠ2 λ _ _ → isSetR _ _

