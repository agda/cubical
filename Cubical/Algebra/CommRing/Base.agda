{-# OPTIONS --cubical --no-import-sorts --safe #-}
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

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup    hiding (⟨_⟩)
open import Cubical.Algebra.Monoid       hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup   hiding (⟨_⟩)
open import Cubical.Algebra.Ring      hiding (⟨_⟩)

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
             → CommRing
makeCommRing 0r 1r _+_ _·_ -_ is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm =
  commring _ _ _ _ _ _ (makeIsCommRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm)

CommRing→Ring : CommRing {ℓ} → Ring
CommRing→Ring (commring _ _ _ _ _ _ H) = ring _ _ _ _ _ _ (IsCommRing.isRing H)

CommRingEquiv : (R S : CommRing) → Type ℓ
CommRingEquiv R S = RingEquiv (CommRing→Ring R) (CommRing→Ring S)

module CommRingΣTheory {ℓ} where

  open RingΣTheory

  CommRingAxioms : (R : Type ℓ) (s : RawRingStructure R) → Type ℓ
  CommRingAxioms R (_+_ , 1r , _·_) = RingAxioms R (_+_ , 1r , _·_)
                                      × ((x y : R) → x · y ≡ y · x)
  CommRingStructure : Type ℓ → Type ℓ
  CommRingStructure = AxiomsStructure RawRingStructure CommRingAxioms

  CommRingΣ : Type (ℓ-suc ℓ)
  CommRingΣ = TypeWithStr ℓ CommRingStructure

  CommRingEquivStr : StrEquiv CommRingStructure ℓ
  CommRingEquivStr = AxiomsEquivStr RawRingEquivStr CommRingAxioms

  isPropCommRingAxioms : (R : Type ℓ) (s : RawRingStructure R)
                       → isProp (CommRingAxioms R s)
  isPropCommRingAxioms R (_·_ , 0r , _+_) =
    isPropΣ (isPropRingAxioms R (_·_ , 0r , _+_))
            λ { (_ , x , _) → isPropΠ2 λ _ _ →
                  x .IsMonoid.isSemigroup .IsSemigroup.is-set _ _}

  CommRing→CommRingΣ : CommRing → CommRingΣ
  CommRing→CommRingΣ (commring _ _ _ _ _ _ (iscommring G C)) =
    _ , _ , Ring→RingΣ (ring _ _ _ _ _ _ G) .snd .snd , C

  CommRingΣ→CommRing : CommRingΣ → CommRing
  CommRingΣ→CommRing (_ , _ , G , C) =
    commring _ _ _ _ _ _ (iscommring (RingΣ→Ring (_ , _ , G) .Ring.isRing) C)

  CommRingIsoCommRingΣ : Iso CommRing CommRingΣ
  CommRingIsoCommRingΣ =
    iso CommRing→CommRingΣ CommRingΣ→CommRing (λ _ → refl) helper

    where
    open import Cubical.Algebra.Group.Base hiding (⟨_⟩)
    open CommRing
    open IsRing
    open IsCommRing
    open RingΣTheory
    ring-helper : retract (Ring→RingΣ {ℓ}) RingΣ→Ring
    ring-helper = Iso.leftInv RingIsoRingΣ

    helper : _
    Carrier (helper a i) = ⟨ a ⟩
    0r (helper a i) = 0r a
    1r (helper a i) = 1r a
    _+_ (helper a i) = CommRing._+_ a
    _·_ (helper a i) = _·_ a
    - helper a i = - a
    isRing (isCommRing (helper a i)) =
      Ring.isRing (ring-helper (ring _ _ _ _ _ _ (isRing (isCommRing a))) i)
    ·-comm (isCommRing (helper a i)) = ·-comm (isCommRing a)

  commRingUnivalentStr : UnivalentStr CommRingStructure CommRingEquivStr
  commRingUnivalentStr = axiomsUnivalentStr _ isPropCommRingAxioms rawRingUnivalentStr

  CommRingΣPath : (R S : CommRingΣ) → (R ≃[ CommRingEquivStr ] S) ≃ (R ≡ S)
  CommRingΣPath = SIP commRingUnivalentStr

  CommRingEquivΣ : (R S : CommRing) → Type ℓ
  CommRingEquivΣ R S = CommRing→CommRingΣ R ≃[ CommRingEquivStr ] CommRing→CommRingΣ S

  CommRingPath : (R S : CommRing) → (CommRingEquiv R S) ≃ (R ≡ S)
  CommRingPath R S =
    CommRingEquiv R S   ≃⟨ isoToEquiv RingIsoΣPath ⟩
    CommRingEquivΣ R S  ≃⟨ CommRingΣPath _ _ ⟩
    CommRing→CommRingΣ R ≡ CommRing→CommRingΣ S
      ≃⟨ isoToEquiv (invIso (congIso CommRingIsoCommRingΣ)) ⟩
    R ≡ S ■

CommRingPath : (R S : CommRing {ℓ}) → (CommRingEquiv R S) ≃ (R ≡ S)
CommRingPath = CommRingΣTheory.CommRingPath

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
