module Cubical.Algebra.HeytingField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Order.Apartness.Base

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    F : Type ℓ

record IsHeytingField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_#_ : F → F → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isheytingfield
  field
    isCommRing  : IsCommRing 0f 1f _+_ _·_ -_
    isApartness : IsApartness _#_
    isTight     : ∀ x y → ¬ x # y → x ≡ y
    +Respect#R  : ∀ x y z → x # y → (x + z) # (y + z)
    #0→isInv    : ∀ x → x # 0f → Σ[ y ∈ F ] x · y ≡ 1f
    isInv→#0    : ∀ x y → x · y ≡ 1f → x # 0f

  open IsCommRing isCommRing public
  open IsApartness isApartness hiding (is-set) public

unquoteDecl IsHeytingFieldIsoΣ = declareRecordIsoΣ IsHeytingFieldIsoΣ (quote IsHeytingField)

record HeytingFieldStr (ℓ' : Level) (F : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor heytingfieldstr
  field
    0f 1f   : F
    _+_ _·_ : F → F → F
    -_      : F → F
    _#_     : F → F → Type ℓ'
    isHeytingField : IsHeytingField 0f 1f _+_ _·_ -_ _#_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix  4 _#_

  open IsHeytingField isHeytingField public

HeytingField : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
HeytingField ℓ ℓ' = TypeWithStr ℓ (HeytingFieldStr ℓ')

HeytingFieldStr→CommRingStr : HeytingFieldStr ℓ' F → CommRingStr F
HeytingFieldStr→CommRingStr (heytingfieldstr _ _ _ _ _ _ H) =
  commringstr _ _ _ _ _ (IsHeytingField.isCommRing H)

HeytingFieldStr→RingStr : HeytingFieldStr ℓ' F → RingStr F
HeytingFieldStr→RingStr F = CommRingStr→RingStr (HeytingFieldStr→CommRingStr F)

HeytingField→CommRing : HeytingField ℓ ℓ' → CommRing ℓ
HeytingField→CommRing (F , H) = F , HeytingFieldStr→CommRingStr H

HeytingField→Ring : HeytingField ℓ ℓ' → Ring ℓ
HeytingField→Ring F = CommRing→Ring (HeytingField→CommRing F)

HeytingFieldStr→ApartnessStr : HeytingFieldStr ℓ' F → ApartnessStr ℓ' F
HeytingFieldStr→ApartnessStr (heytingfieldstr _ _ _ _ _ _ H) =
  apartnessstr _ (IsHeytingField.isApartness H)

HeytingField→Apartness : HeytingField ℓ ℓ' → Apartness ℓ ℓ'
HeytingField→Apartness (F , H) = F , HeytingFieldStr→ApartnessStr H

isPropIsHeytingField : (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_#_ : F → F → Type ℓ')
                     → isProp (IsHeytingField 0f 1f _+_ _·_ -_ _#_)
isPropIsHeytingField _ _ _ _ _ _ = isOfHLevelRetractFromIso 1 IsHeytingFieldIsoΣ $
  isPropΣ (isPropIsCommRing _ _ _ _ _) λ isCommRing →
  isPropΣ (isPropIsApartness _) λ isApartness →
  isProp×3
    (isPropΠ3 λ _ _ _ → isCommRing .is-set _ _)
    (isPropΠ4 λ _ _ _ _ → isApartness .is-prop-valued _ _)
    (isPropΠ2 λ _ _ → Units.inverseUniqueness (_ , commringstr _ _ _ _ _ isCommRing) _)
    (isPropΠ3 λ _ _ _ → isApartness .is-prop-valued _ _)
  where open IsApartness; open IsCommRing

record IsHeytingFieldHom
  {A : Type ℓ} {B : Type ℓ'}
  (F : HeytingFieldStr ℓ'' A) (f : A → B) (K : HeytingFieldStr ℓ''' B)
  : Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')) where
  no-eta-equality
  private
    module F = HeytingFieldStr F
    module K = HeytingFieldStr K

  field
    pres0 : f F.0f ≡ K.0f
    pres1 : f F.1f ≡ K.1f
    pres+ : (x y : A) → f (x F.+ y) ≡ f x K.+ f y
    pres· : (x y : A) → f (x F.· y) ≡ f x K.· f y
    pres- : (x : A) → f (F.- x) ≡ K.- (f x)
    pres# : (x y : A) → (x F.# y) ≃ (f x K.# f y) -- This is actually redundant

unquoteDecl IsHeytingFieldHomIsoΣ = declareRecordIsoΣ IsHeytingFieldHomIsoΣ (quote IsHeytingFieldHom)

isPropIsHeytingFieldHom : {A : Type ℓ} {B : Type ℓ'}
                        → (F : HeytingFieldStr ℓ'' A)
                        → (f : A → B)
                        → (K : HeytingFieldStr ℓ''' B)
                        → isProp (IsHeytingFieldHom F f K)
isPropIsHeytingFieldHom F f K = isOfHLevelRetractFromIso 1 IsHeytingFieldHomIsoΣ $
  isProp×5
    (is-set _ _)
    (is-set _ _)
    (isPropΠ2 λ _ _ → is-set _ _)
    (isPropΠ2 λ _ _ → is-set _ _)
    (isPropΠ  λ _   → is-set _ _)
    (isPropΠ2 λ _ _ → isOfHLevel⁺≃ᵣ 0 (is-prop-valued _ _))
  where open HeytingFieldStr K

isHeytingFieldHom→isRingHom : {A : Type ℓ} {B : Type ℓ'}
                            → (F : HeytingFieldStr ℓ'' A)
                            → (f : A → B)
                            → (K : HeytingFieldStr ℓ''' B)
                            → IsHeytingFieldHom F f K
                            → IsRingHom (HeytingFieldStr→RingStr F) f  (HeytingFieldStr→RingStr K)
isHeytingFieldHom→isRingHom F f K fIsHom = isRingHomf where
  module f = IsHeytingFieldHom fIsHom
  open IsRingHom

  isRingHomf : IsRingHom _ f _
  isRingHomf .pres0 = f.pres0
  isRingHomf .pres1 = f.pres1
  isRingHomf .pres+ = f.pres+
  isRingHomf .pres· = f.pres·
  isRingHomf .pres- = f.pres-

HeytingFieldHom : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''') → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
HeytingFieldHom (A , F) (B , K) = Σ[ f ∈ (A → B) ] IsHeytingFieldHom F f K

isSetHeytingFieldHom : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''') → isSet (HeytingFieldHom F K)
isSetHeytingFieldHom F K = isSetΣSndProp (isSet→ is-set) λ f → isPropIsHeytingFieldHom _ f _
  where open HeytingFieldStr (str K)

HeytingFieldHom→RingHom : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''')
                        → HeytingFieldHom F K
                        → RingHom (HeytingField→Ring F) (HeytingField→Ring K)
HeytingFieldHom→RingHom F K (f , fIsHom) = f , isHeytingFieldHom→isRingHom _ f _ fIsHom

IsHeytingFieldEquiv : {A : Type ℓ} {B : Type ℓ'}
                    → (F : HeytingFieldStr ℓ'' A) (e : A ≃ B) (K : HeytingFieldStr ℓ''' B)
                    → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
IsHeytingFieldEquiv F e K = IsHeytingFieldHom F (e .fst) K

HeytingFieldEquiv : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''') → Type (ℓ-max (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
HeytingFieldEquiv (A , F) (B , K) = Σ[ e ∈ A ≃ B ] IsHeytingFieldEquiv F e K

isSetHeytingFieldEquiv : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''') → isSet (HeytingFieldEquiv F K)
isSetHeytingFieldEquiv F K =
  isSetΣSndProp (isOfHLevel⁺≃ᵣ 1 is-set) λ (f , _) → isPropIsHeytingFieldHom _ f _
  where open HeytingFieldStr (str K)

HeytingFieldEquiv→RingEquiv : (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''')
                            → HeytingFieldEquiv F K
                            → RingEquiv (HeytingField→Ring F) (HeytingField→Ring K)
HeytingFieldEquiv→RingEquiv F K (e , eIsHom) = e , isHeytingFieldHom→isRingHom _ _ _ eIsHom

𝒮ᴰ-HeytingField : DUARel (𝒮-Univ ℓ) (HeytingFieldStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-HeytingField =
  𝒮ᴰ-Record (𝒮-Univ _) IsHeytingFieldEquiv (fields:
    data[ 0f ∣ null ∣ pres0 ]
    data[ 1f ∣ null ∣ pres1 ]
    data[ _+_ ∣ bin ∣ pres+ ]
    data[ _·_ ∣ bin ∣ pres· ]
    data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
    data[ _#_ ∣ autoDUARel _ _ ∣ pres# ]
    prop[ isHeytingField ∣ (λ _ _ → isPropIsHeytingField _ _ _ _ _ _) ]
  )
  where
    open HeytingFieldStr
    open IsHeytingFieldHom

    null = autoDUARel (𝒮-Univ _) λ A → A
    bin = autoDUARel (𝒮-Univ _) λ A → A → A → A

HeytingFieldPath : (F K : HeytingField ℓ ℓ') → HeytingFieldEquiv F K ≃ (F ≡ K)
HeytingFieldPath = ∫ 𝒮ᴰ-HeytingField .UARel.ua

uaHeytingField : {F K : HeytingField ℓ ℓ'} → HeytingFieldEquiv F K → F ≡ K
uaHeytingField = HeytingFieldPath _ _ .fst

isGroupoidHeytingField : isGroupoid (HeytingField ℓ ℓ')
isGroupoidHeytingField _ _ = isOfHLevelRespectEquiv 2 (HeytingFieldPath _ _) (isSetHeytingFieldEquiv _ _)
