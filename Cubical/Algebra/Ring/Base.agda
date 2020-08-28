{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Ring.Base where

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
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup    hiding (⟨_⟩)
open import Cubical.Algebra.Monoid       hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup   hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsRing {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isring

  field
    +-isAbGroup : IsAbGroup 0r _+_ -_
    ·-isMonoid  : IsMonoid 1r _·_
    dist        : (x y z : R) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z))
    -- This is in the Agda stdlib, but it's redundant
    -- zero             : (x : R) → (x · 0r ≡ 0r) × (0r · x ≡ 0r)

  open IsAbGroup +-isAbGroup public
    renaming
      ( assoc       to +-assoc
      ; identity    to +-identity
      ; lid         to +-lid
      ; rid         to +-rid
      ; inverse     to +-inv
      ; invl        to +-linv
      ; invr        to +-rinv
      ; comm        to +-comm
      ; isSemigroup to +-isSemigroup
      ; isMonoid    to +-isMonoid
      ; isGroup     to +-isGroup )

  open IsMonoid ·-isMonoid public
    renaming
      ( assoc       to ·-assoc
      ; identity    to ·-identity
      ; lid         to ·-lid
      ; rid         to ·-rid
      ; isSemigroup to ·-isSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

  ·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·-rdist-+ x y z = dist x y z .fst

  ·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·-ldist-+ x y z = dist x y z .snd

record Ring : Type (ℓ-suc ℓ) where

  constructor ring

  field
    Carrier : Type ℓ
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isRing  : IsRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsRing isRing public

-- Extractor for the carrier type
⟨_⟩ : Ring → Type ℓ
⟨_⟩ = Ring.Carrier

isSetRing : (R : Ring {ℓ}) → isSet ⟨ R ⟩
isSetRing R = R .Ring.isRing .IsRing.·-isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

makeIsRing : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
             (is-setR : isSet R)
             (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
             (+-rid : (x : R) → x + 0r ≡ x)
             (+-rinv : (x : R) → x + (- x) ≡ 0r)
             (+-comm : (x y : R) → x + y ≡ y + x)
             (r+-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
             (·-rid : (x : R) → x · 1r ≡ x)
             (·-lid : (x : R) → 1r · x ≡ x)
             (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
             (·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
           → IsRing 0r 1r _+_ _·_ -_
makeIsRing is-setR assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ =
  isring (makeIsAbGroup is-setR assoc +-rid +-rinv +-comm)
         (makeIsMonoid is-setR ·-assoc ·-rid ·-lid)
         λ x y z → ·-rdist-+ x y z , ·-ldist-+ x y z

makeRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
           (is-setR : isSet R)
           (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
           (+-rid : (x : R) → x + 0r ≡ x)
           (+-rinv : (x : R) → x + (- x) ≡ 0r)
           (+-comm : (x y : R) → x + y ≡ y + x)
           (+-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
           (·-rid : (x : R) → x · 1r ≡ x)
           (·-lid : (x : R) → 1r · x ≡ x)
           (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
           (·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
         → Ring
makeRing 0r 1r _+_ _·_ -_ is-setR assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ =
  ring _ 0r 1r _+_ _·_ -_
       (makeIsRing is-setR assoc +-rid +-rinv +-comm
                   ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ )

record RingEquiv (R S : Ring {ℓ}) : Type ℓ where

  constructor ringequiv

  private
    module R = Ring R
    module S = Ring S

  field
    e : ⟨ R ⟩ ≃ ⟨ S ⟩
    pres1 : equivFun e R.1r ≡ S.1r
    isHom+ : (x y : ⟨ R ⟩) → equivFun e (x R.+ y) ≡ equivFun e x S.+ equivFun e y
    isHom· : (x y : ⟨ R ⟩) → equivFun e (x R.· y) ≡ equivFun e x S.· equivFun e y

module RingΣTheory {ℓ} where

  RawRingStructure = λ (X : Type ℓ) → (X → X → X) × X × (X → X → X)

  RawRingEquivStr = AutoEquivStr RawRingStructure

  rawRingUnivalentStr : UnivalentStr _ RawRingEquivStr
  rawRingUnivalentStr = autoUnivalentStr RawRingStructure

  RingAxioms : (R : Type ℓ) (s : RawRingStructure R) → Type ℓ
  RingAxioms R (_+_ , 1r , _·_) =
    AbGroupΣTheory.AbGroupAxioms R _+_
    × IsMonoid 1r _·_
    × ((x y z : R) → (x · (y + z) ≡ (x · y) + (x · z)) × ((x + y) · z ≡ (x · z) + (y · z)))

  RingStructure : Type ℓ → Type ℓ
  RingStructure = AxiomsStructure RawRingStructure RingAxioms

  RingΣ : Type (ℓ-suc ℓ)
  RingΣ = TypeWithStr ℓ RingStructure

  RingEquivStr : StrEquiv RingStructure ℓ
  RingEquivStr = AxiomsEquivStr RawRingEquivStr RingAxioms

  isPropRingAxioms : (R : Type ℓ) (s : RawRingStructure R) → isProp (RingAxioms R s)
  isPropRingAxioms R (_+_ , 1r , _·_) =
    isProp× (AbGroupΣTheory.isPropAbGroupAxioms R _+_)
            (isPropΣ (isPropIsMonoid 1r _·_)
                     λ R → isPropΠ3 λ _ _ _ →
                           isProp× (IsSemigroup.is-set (R .IsMonoid.isSemigroup) _ _)
                                   (IsSemigroup.is-set (R .IsMonoid.isSemigroup) _ _))

  Ring→RingΣ : Ring → RingΣ
  Ring→RingΣ (ring R 0r 1r _+_ _·_ -_ (isring +-isAbelianGroup ·-isMonoid dist)) =
    ( R
    , (_+_ , 1r , _·_)
    , AbGroupΣTheory.AbGroup→AbGroupΣ (abgroup _ _ _ _ +-isAbelianGroup) .snd .snd
    , ·-isMonoid , dist
    )

  RingΣ→Ring : RingΣ → Ring
  RingΣ→Ring (_ , (y1 , y2 , y3) , z , w1 , w2) =
    ring _ _ y2 y1 y3 _
      (isring (AbGroupΣTheory.AbGroupΣ→AbGroup (_ , _ , z ) .AbGroup.isAbGroup)
              w1 w2)

  open import Cubical.Algebra.Group.Base hiding (⟨_⟩)
  RingIsoRingΣ : Iso Ring RingΣ
  RingIsoRingΣ = iso Ring→RingΣ RingΣ→Ring (λ _ → refl) helper
    where
      -- helper will be refl, if eta-equality is activated for all structure-records
      open IsRing
      open MonoidΣTheory
      monoid-helper : retract (Monoid→MonoidΣ {ℓ}) MonoidΣ→Monoid
      monoid-helper = Iso.leftInv MonoidIsoMonoidΣ
      open AbGroupΣTheory
      abgroup-helper : retract (AbGroup→AbGroupΣ {ℓ}) AbGroupΣ→AbGroup
      abgroup-helper = Iso.leftInv AbGroupIsoAbGroupΣ

      helper : _
      Ring.Carrier (helper a i) = ⟨ a ⟩
      Ring.0r (helper a i) = Ring.0r a
      Ring.1r (helper a i) = Ring.1r a
      Ring._+_ (helper a i) = Ring._+_ a
      Ring._·_ (helper a i) = Ring._·_ a
      Ring.- helper a i = Ring.- a
      +-isAbGroup (Ring.isRing (helper a i)) =
        AbGroup.isAbGroup (abgroup-helper (abgroup _ _ _ _ (Ring.+-isAbGroup a)) i)
      ·-isMonoid (Ring.isRing (helper a i)) =
        Monoid.isMonoid (monoid-helper (monoid _ _ _ (Ring.·-isMonoid a)) i)
      dist (Ring.isRing (helper a i)) = dist (Ring.isRing a)

  ringUnivalentStr : UnivalentStr RingStructure RingEquivStr
  ringUnivalentStr = axiomsUnivalentStr _ isPropRingAxioms rawRingUnivalentStr

  RingΣPath : (R S : RingΣ) → (R ≃[ RingEquivStr ] S) ≃ (R ≡ S)
  RingΣPath = SIP ringUnivalentStr

  RingEquivΣ : (R S : Ring) → Type ℓ
  RingEquivΣ R S = Ring→RingΣ R ≃[ RingEquivStr ] Ring→RingΣ S

  RingIsoΣPath : {R S : Ring} → Iso (RingEquiv R S) (RingEquivΣ R S)
  fun RingIsoΣPath (ringequiv e h1 h2 h3) = e , h2 , h1 , h3
  inv RingIsoΣPath (e , h1 , h2 , h3)    = ringequiv e h2 h1 h3
  rightInv RingIsoΣPath _                = refl
  leftInv RingIsoΣPath _                 = refl

  RingPath : (R S : Ring) → (RingEquiv R S) ≃ (R ≡ S)
  RingPath R S =
    RingEquiv R S               ≃⟨ isoToEquiv RingIsoΣPath ⟩
    RingEquivΣ R S              ≃⟨ RingΣPath _ _ ⟩
    Ring→RingΣ R ≡ Ring→RingΣ S ≃⟨ isoToEquiv (invIso (congIso RingIsoRingΣ)) ⟩
    R ≡ S ■


RingPath : (R S : Ring {ℓ}) → (RingEquiv R S) ≃ (R ≡ S)
RingPath = RingΣTheory.RingPath

isPropIsRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsRing 0r 1r _+_ _·_ -_)
isPropIsRing 0r 1r _+_ _·_ -_ (isring RG RM RD) (isring SG SM SD) =
  λ i → isring (isPropIsAbGroup _ _ _ RG SG i)
               (isPropIsMonoid _ _ RM SM i)
               (isPropDistr RD SD i)
  where
  isSetR : isSet _
  isSetR = RM .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropDistr : isProp ((x y z : _) → ((x · (y + z)) ≡ ((x · y) + (x · z)))
                                    × (((x + y) · z) ≡ ((x · z) + (y · z))))
  isPropDistr = isPropΠ3 λ _ _ _ → isProp× (isSetR _ _) (isSetR _ _)


-- Rings have an abelian group and a monoid

Ring→AbGroup : Ring {ℓ} → AbGroup {ℓ}
Ring→AbGroup (ring _ _ _ _ _ _ R) = abgroup _ _ _ _ (IsRing.+-isAbGroup R)

Ring→Monoid : Ring {ℓ} → Monoid {ℓ}
Ring→Monoid (ring _ _ _ _ _ _ R) = monoid _ _ _ (IsRing.·-isMonoid R)
