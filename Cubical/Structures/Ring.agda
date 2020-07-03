{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Ring where

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
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid    hiding (⟨_⟩)
open import Cubical.Structures.AbGroup   hiding (⟨_⟩)

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
    ; isGroup     to +-isGroup
    )

  open IsMonoid ·-isMonoid public
    renaming
    ( assoc       to ·-assoc
    ; identity    to ·-identity
    ; lid         to ·-lid
    ; rid         to ·-rid
    ; isSemigroup to ·-isSemigroup
    )

  ·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·-rdist-+ x y z = dist x y z .fst

  ·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·-ldist-+ x y z = dist x y z .snd

  -- TODO: prove these somewhere
  -- -> these are 0-rightNullifies and 0-leftNullifies below in theory

  -- zero-lid : (x : R) → 0r · x ≡ 0r
  -- zero-lid x = zero x .snd

  -- zero-rid : (x : R) → x · 0r ≡ 0r
  -- zero-rid x = zero x .fst

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
             (+-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
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

  RingIsoRingΣ : Iso Ring RingΣ
  RingIsoRingΣ = iso Ring→RingΣ RingΣ→Ring (λ _ → refl) (λ _ → refl)

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


{-
  some basic calculations (used for example in QuotientRing.agda),
  that should become obsolete or subject to change once we have a
  ring solver (see https://github.com/agda/cubical/issues/297)
-}
module RingTheory (R : Ring {ℓ}) where

  open Ring R

  implicitInverse : (x y : ⟨ R ⟩)
                 → x + y ≡ 0r
                 → y ≡ - x
  implicitInverse x y p =
    y               ≡⟨ sym (+-lid y) ⟩
    0r + y          ≡⟨ cong (λ u → u + y) (sym (+-linv x)) ⟩
    (- x + x) + y   ≡⟨ sym (+-assoc _ _ _) ⟩
    (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
    (- x) + 0r      ≡⟨ +-rid _ ⟩
    - x             ∎

  0-selfinverse : - 0r ≡ 0r
  0-selfinverse = sym (implicitInverse _ _ (+-rid 0r))

  0-idempotent : 0r + 0r ≡ 0r
  0-idempotent = +-lid 0r

  +-idempotency→0 : (x : ⟨ R ⟩) → x ≡ x + x → 0r ≡ x
  +-idempotency→0 x p =
    0r              ≡⟨ sym (+-rinv _) ⟩
    x + (- x)       ≡⟨ cong (λ u → u + (- x)) p ⟩
    (x + x) + (- x) ≡⟨ sym (+-assoc _ _ _) ⟩
    x + (x + (- x)) ≡⟨ cong (λ u → x + u) (+-rinv _) ⟩
    x + 0r          ≡⟨ +-rid x ⟩
    x               ∎

  0-rightNullifies : (x : ⟨ R ⟩) → x · 0r ≡ 0r
  0-rightNullifies x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·-rdist-+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in sym (+-idempotency→0 _ x·0-is-idempotent)

  0-leftNullifies : (x : ⟨ R ⟩) → 0r · x ≡ 0r
  0-leftNullifies x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ cong (λ u → u · x) (sym 0-idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·-ldist-+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in sym (+-idempotency→0 _ 0·x-is-idempotent)

  -commutesWithRight-· : (x y : ⟨ R ⟩) →  x · (- y) ≡ - (x · y)
  -commutesWithRight-· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (·-rdist-+ _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ cong (λ u → x · u) (+-rinv y) ⟩
                               x · 0r                 ≡⟨ 0-rightNullifies x ⟩
                               0r ∎)

  -commutesWithLeft-· : (x y : ⟨ R ⟩) →  (- x) · y ≡ - (x · y)
  -commutesWithLeft-· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (·-ldist-+ _ _ _) ⟩
                              (x - x) · y            ≡⟨ cong (λ u → u · y) (+-rinv x) ⟩
                              0r · y                 ≡⟨ 0-leftNullifies y ⟩
                              0r ∎)

  -isDistributive : (x y : ⟨ R ⟩) → (- x) + (- y) ≡ - (x + y)
  -isDistributive x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (+-assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                         (λ u → x + (y + u))
                                         (+-comm _ _) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (+-assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (+-rinv _) ⟩
          x + (0r + (- x))           ≡⟨ cong (λ u → x + u) (+-lid _) ⟩
          x + (- x)                 ≡⟨ +-rinv _ ⟩
          0r ∎)

  translatedDifference : (x a b : ⟨ R ⟩) → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (+-lid _)) ⟩
              (a + (0r + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (+-rinv _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (sym (+-assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (+-assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (+-comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-isDistributive _ _) ⟩
              ((x + a) - (x + b)) ∎
