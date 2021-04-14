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
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup

open import Cubical.Reflection.StrictEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsRing {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isring

  field
    +IsAbGroup : IsAbGroup 0r _+_ -_
    ·IsMonoid  : IsMonoid 1r _·_
    dist        : (x y z : R) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z))
    -- This is in the Agda stdlib, but it's redundant
    -- zero             : (x : R) → (x · 0r ≡ 0r) × (0r · x ≡ 0r)

  open IsAbGroup +IsAbGroup public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; inverse     to +Inv
      ; invl        to +Linv
      ; invr        to +Rinv
      ; comm        to +Comm
      ; isSemigroup to +IsSemigroup
      ; isMonoid    to +IsMonoid
      ; isGroup     to +IsGroup )

  open IsMonoid ·IsMonoid public
    renaming
      ( assoc       to ·Assoc
      ; identity    to ·Identity
      ; lid         to ·Lid
      ; rid         to ·Rid
      ; isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

  ·Rdist+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·Rdist+ x y z = dist x y z .fst

  ·Ldist+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·Ldist+ x y z = dist x y z .snd

record RingStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor ringstr

  field
    0r      : A
    1r      : A
    _+_     : A → A → A
    _·_     : A → A → A
    -_      : A → A
    isRing  : IsRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsRing isRing public

Ring : Type (ℓ-suc ℓ)
Ring = TypeWithStr _ RingStr

isSetRing : (R : Ring {ℓ}) → isSet ⟨ R ⟩
isSetRing R = R .snd .RingStr.isRing .IsRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

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
  _ , ringstr 0r 1r _+_ _·_ -_
       (makeIsRing is-setR assoc +-rid +-rinv +-comm
                   ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ )

record RingEquiv (R : Ring {ℓ}) (S : Ring {ℓ'}) (e : ⟨ R ⟩ ≃ ⟨ S ⟩) : Type (ℓ-max ℓ ℓ') where

  constructor ringequiv

  private
    module R = RingStr (snd R)
    module S = RingStr (snd S)

  field
    pres1 : equivFun e R.1r ≡ S.1r
    isHom+ : (x y : ⟨ R ⟩) → equivFun e (x R.+ y) ≡ equivFun e x S.+ equivFun e y
    isHom· : (x y : ⟨ R ⟩) → equivFun e (x R.· y) ≡ equivFun e x S.· equivFun e y


record RingHom (R S : Ring {ℓ}) : Type ℓ where

  constructor ringhom

  private
    module R = RingStr (snd R)
    module S = RingStr (snd S)

  field
    map : ⟨ R ⟩ → ⟨ S ⟩
    pres1 : map R.1r ≡ S.1r
    isHom+ : (x y : ⟨ R ⟩) → map (x R.+ y) ≡ map x S.+ map y
    isHom· : (x y : ⟨ R ⟩) → map (x R.· y) ≡ map x S.· map y

_$_ : {R S : Ring {ℓ}} → (φ : RingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $ x = RingHom.map φ x

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
  Ring→RingΣ (R , ringstr 0r 1r _+_ _·_ -_ (isring +-isAbelianGroup ·-isMonoid dist)) =
    ( R
    , (_+_ , 1r , _·_)
    , AbGroupΣTheory.AbGroup→AbGroupΣ (_ , abgroupstr _ _ _ +-isAbelianGroup) .snd .snd
    , ·-isMonoid , dist
    )

  RingΣ→Ring : RingΣ → Ring
  RingΣ→Ring (_ , (y1 , y2 , y3) , z , w1 , w2) =
    _ , ringstr _ y2 y1 y3 _
      (isring (AbGroupΣTheory.AbGroupΣ→AbGroup (_ , _ , z ) .snd .AbGroupStr.isAbGroup)
              w1 w2)

  RingIsoRingΣ : Iso Ring RingΣ
  RingIsoRingΣ = iso Ring→RingΣ RingΣ→Ring (λ _ → refl) (λ _ → refl)

  ringUnivalentStr : UnivalentStr RingStructure RingEquivStr
  ringUnivalentStr = axiomsUnivalentStr _ isPropRingAxioms rawRingUnivalentStr

  RingΣPath : (R S : RingΣ) → (R ≃[ RingEquivStr ] S) ≃ (R ≡ S)
  RingΣPath = SIP ringUnivalentStr

  RingEquivΣ : (R S : Ring) → Type ℓ
  RingEquivΣ R S = Ring→RingΣ R ≃[ RingEquivStr ] Ring→RingΣ S

  RingIsoΣPath : {R S : Ring} → Iso (Σ[ e ∈ ⟨ R ⟩ ≃ ⟨ S ⟩ ] RingEquiv R S e) (RingEquivΣ R S)
  fun RingIsoΣPath (e , ringequiv h1 h2 h3) = e , h2 , h1 , h3
  inv RingIsoΣPath (e , h1 , h2 , h3)       = e , ringequiv h2 h1 h3
  rightInv RingIsoΣPath _                   = refl
  leftInv RingIsoΣPath _                    = refl

  RingPath : (R S : Ring) → (Σ[ e ∈ ⟨ R ⟩ ≃ ⟨ S ⟩ ] RingEquiv R S e) ≃ (R ≡ S)
  RingPath R S =
    Σ[ e ∈ ⟨ R ⟩ ≃ ⟨ S ⟩ ] RingEquiv R S e ≃⟨ strictIsoToEquiv RingIsoΣPath ⟩
    RingEquivΣ R S              ≃⟨ RingΣPath _ _ ⟩
    Ring→RingΣ R ≡ Ring→RingΣ S ≃⟨ isoToEquiv (invIso (congIso RingIsoRingΣ)) ⟩
    R ≡ S ■


RingPath : (R S : Ring {ℓ}) → (Σ[ e ∈ ⟨ R ⟩ ≃ ⟨ S ⟩ ] RingEquiv R S e) ≃ (R ≡ S)
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
Ring→AbGroup (A , ringstr _ _ _ _ _ R) = A , abgroupstr _ _ _ (IsRing.+IsAbGroup R)

Ring→Monoid : Ring {ℓ} → Monoid {ℓ}
Ring→Monoid (A , ringstr _ _ _ _ _ R) = monoid _ _ _ (IsRing.·IsMonoid R)
