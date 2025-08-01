{-
   Keep in mind, that here are many different notions of "field" in constructive algebra.
   In the terminology of "A Course in Constructive Algebra" (by Mines, Richman, Ruitenburg) (p. 45),
   the notion of field we use below, would be a nontrivial field (where the apartness relation
   used in the definition of field is inequality in our case).
   This is a very weak notion of field, but behaves a lot like the classical notion, if the carrier
   type has decidable equality.
-}
module Cubical.Algebra.Field.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level


record IsField {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isfield

  field
    isCommRing : IsCommRing 0r 1r _+_ _·_ -_
    hasInverse : (x : R) → ¬ x ≡ 0r → Σ[ y ∈ R ] x · y ≡ 1r
    0≢1        : ¬ 0r ≡ 1r

  open IsCommRing isCommRing public

  _[_]⁻¹ : (x : R) → ¬ x ≡ 0r → R
  x [ ¬x≡0 ]⁻¹ = hasInverse x ¬x≡0 .fst

  ·⁻¹≡1 : (x : R) (≢0 : ¬ x ≡ 0r) → x · (x [ ≢0 ]⁻¹) ≡ 1r
  ·⁻¹≡1 x ¬x≡0 = hasInverse x ¬x≡0 .snd


record FieldStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor fieldstr

  field
    0r         : A
    1r         : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    isField    : IsField 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsField isField public


Field : ∀ ℓ → Type (ℓ-suc ℓ)
Field ℓ = TypeWithStr ℓ FieldStr


makeIsField : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
                 {_[_]⁻¹ : (x : R) → ¬ (x ≡ 0r) → R}
                 (is-setR : isSet R)
                 (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
                 (+-rid : (x : R) → x + 0r ≡ x)
                 (+-rinv : (x : R) → x + (- x) ≡ 0r)
                 (+-comm : (x y : R) → x + y ≡ y + x)
                 (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
                 (·-rid : (x : R) → x · 1r ≡ x)
                 (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
                 (·-comm : (x y : R) → x · y ≡ y · x)
                 (·⁻¹≡1 : (x : R) (≢0 : ¬ (x ≡ 0r)) → x · (x [ ≢0 ]⁻¹) ≡ 1r)
                 (0≢1 : ¬ (0r ≡ 1r))
               → IsField 0r 1r _+_ _·_ -_
makeIsField {R = R} {0r = 0r} {1r = 1r} {_+_ = _+_} {_·_ = _·_} {_[_]⁻¹ = _[_]⁻¹}
  is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm ·⁻¹≡1 0≢1 =
  isfield (makeIsCommRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm) ·-inv 0≢1
    where
    ·-inv : (x : R) → ¬ x ≡ 0r → Σ[ y ∈ R ] x · y ≡ 1r
    ·-inv x ¬x≡0 = x [ ¬x≡0 ]⁻¹ , ·⁻¹≡1 x ¬x≡0

makeField : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) (_[_]⁻¹ : (x : R) → ¬ (x ≡ 0r) → R)
                 (is-setR : isSet R)
                 (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
                 (+-rid : (x : R) → x + 0r ≡ x)
                 (+-rinv : (x : R) → x + (- x) ≡ 0r)
                 (+-comm : (x y : R) → x + y ≡ y + x)
                 (·-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
                 (·-rid : (x : R) → x · 1r ≡ x)
                 (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
                 (·-comm : (x y : R) → x · y ≡ y · x)
                 (·⁻¹≡1 : (x : R) (≢0 : ¬ (x ≡ 0r)) → x · (x [ ≢0 ]⁻¹) ≡ 1r)
                 (0≢1 : ¬ (0r ≡ 1r))
               → Field ℓ
makeField 0r 1r _+_ _·_ -_ _[_]⁻¹ is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm ·⁻¹≡1 0≢1 =
  _ , fieldstr _ _ _ _ _ (makeIsField is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm ·⁻¹≡1 0≢1)


module _ (R : CommRing ℓ) where

  open CommRingStr (R .snd)

  makeFieldFromCommRing :
    (hasInv : (x : R .fst) → ¬ x ≡ 0r → Σ[ y ∈ R .fst ] x · y ≡ 1r)
    (0≢1 : ¬ 0r ≡ 1r)
    → Field ℓ
  makeFieldFromCommRing hasInv 0≢1 .fst = R .fst
  makeFieldFromCommRing hasInv 0≢1 .snd = fieldstr _ _ _ _ _ (isfield isCommRing hasInv 0≢1)


FieldStr→CommRingStr : {A : Type ℓ} → FieldStr A → CommRingStr A
FieldStr→CommRingStr (fieldstr _ _ _ _ _ H) = commringstr _ _ _ _ _ (IsField.isCommRing H)

Field→CommRing : Field ℓ → CommRing ℓ
Field→CommRing (_ , fieldstr _ _ _ _ _ H) = _ , commringstr _ _ _ _ _ (IsField.isCommRing H)


record IsFieldHom {A : Type ℓ} {B : Type ℓ'} (R : FieldStr A) (f : A → B) (S : FieldStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module R = FieldStr R
    module S = FieldStr S

  field
    pres0  : f R.0r ≡ S.0r
    pres1  : f R.1r ≡ S.1r
    pres+  : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres·  : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres-  : (x : A) → f (R.- x) ≡ S.- (f x)

unquoteDecl IsFieldHomIsoΣ = declareRecordIsoΣ IsFieldHomIsoΣ (quote IsFieldHom)

FieldHom : (R : Field ℓ) (S : Field ℓ') → Type (ℓ-max ℓ ℓ')
FieldHom R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsFieldHom (R .snd) f (S .snd)


IsFieldEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : FieldStr A) (e : A ≃ B) (S : FieldStr B) → Type (ℓ-max ℓ ℓ')
IsFieldEquiv R e S = IsFieldHom R (e .fst) S

FieldEquiv : (R : Field ℓ) (S : Field ℓ') → Type (ℓ-max ℓ ℓ')
FieldEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsFieldEquiv (R .snd) e (S .snd)


_$f_ : {R S : Field ℓ} → (φ : FieldHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $f x = φ .fst x


FieldEquiv→FieldHom : {A B : Field ℓ} → FieldEquiv A B → FieldHom A B
FieldEquiv→FieldHom (e , eIsHom) = e .fst , eIsHom


isPropIsField : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsField 0r 1r _+_ _·_ -_)
isPropIsField {R = R} 0r 1r _+_ _·_ -_ H@(isfield RR RC RD) (isfield SR SC SD) =
  λ i → isfield (isPropIsCommRing _ _ _ _ _ RR SR i)
                   (isPropInv RC SC i) (isProp¬ _ RD SD i)
  where
  isPropInv : isProp ((x : _) → ¬ x ≡ 0r → Σ[ y ∈ R ] x · y ≡ 1r)
  isPropInv = isPropΠ2 (λ x _ → Units.inverseUniqueness (Field→CommRing (_ , fieldstr _ _ _ _ _ H)) x)


𝒮ᴰ-Field : DUARel (𝒮-Univ ℓ) FieldStr ℓ
𝒮ᴰ-Field =
  𝒮ᴰ-Record (𝒮-Univ _) IsFieldEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isField ∣ (λ _ _ → isPropIsField _ _ _ _ _) ])
  where
  open FieldStr
  open IsFieldHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

FieldPath : (R S : Field ℓ) → FieldEquiv R S ≃ (R ≡ S)
FieldPath = ∫ 𝒮ᴰ-Field .UARel.ua

uaField : {A B : Field ℓ} → FieldEquiv A B → A ≡ B
uaField {A = A} {B = B} = equivFun (FieldPath A B)
