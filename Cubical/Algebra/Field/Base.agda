{-# OPTIONS --safe #-}
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
  hiding (_$_)
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
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
                  (_[_]⁻¹ : (x : R) → ¬ (x ≡ 0r) → R) : Type ℓ where

  constructor isfield

  field
    isCommRing : IsCommRing 0r 1r _+_ _·_ -_
    ·⁻¹≡1      : (x : R) (≢0 : ¬ (x ≡ 0r)) → x · (x [ ≢0 ]⁻¹) ≡ 1r
    0≢1        : ¬ (0r ≡ 1r)

  open IsCommRing isCommRing public

record FieldStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor fieldstr

  field
    0r         : A
    1r         : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    _[_]⁻¹     : (x : A) → ¬ (x ≡ 0r) → A
    isField    : IsField 0r 1r _+_ _·_ -_ _[_]⁻¹

  infix  20 _⁻¹
  infix  8 -_
  infixl 7 _·_
  infixl 7 _/_
  infixl 6 _+_

  _⁻¹ : (x : A) → { ≢0 : ¬ (x ≡ 0r) } → A
  (x ⁻¹) { ≢0 } = x [ ≢0 ]⁻¹

  _/_ : (x y : A) → { ≢0 : ¬ (y ≡ 0r) } → A
  (x / y) {≢0} = x · (y [ ≢0 ]⁻¹)

  open IsField isField public

Field : ∀ ℓ → Type (ℓ-suc ℓ)
Field ℓ = TypeWithStr ℓ FieldStr

isSetField : (R : Field ℓ) → isSet ⟨ R ⟩
isSetField R = R .snd .FieldStr.isField .IsField.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

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
               → IsField 0r 1r _+_ _·_ -_ _[_]⁻¹
makeIsField {_+_ = _+_} is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm ·⁻¹≡1 0≢1 =
  isfield (makeIsCommRing is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm) ·⁻¹≡1 0≢1

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
  _ , fieldstr _ _ _ _ _ _ (makeIsField is-setR +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-rdist-+ ·-comm ·⁻¹≡1 0≢1)

FieldStr→CommRingStr : {A : Type ℓ} → FieldStr A → CommRingStr A
FieldStr→CommRingStr (fieldstr _ _ _ _ _ _ H) = commringstr _ _ _ _ _ (IsField.isCommRing H)

Field→CommRing : Field ℓ → CommRing ℓ
Field→CommRing (_ , fieldstr _ _ _ _ _ _ H) = _ , commringstr _ _ _ _ _ (IsField.isCommRing H)

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
    pres⁻¹ : (x : A) (≢0 : ¬ (x ≡ R.0r)) (f≢0 : ¬ (f x ≡ S.0r))  → f (x R.[ ≢0 ]⁻¹) ≡ ((f x) S.[ f≢0 ]⁻¹)

unquoteDecl IsFieldHomIsoΣ = declareRecordIsoΣ IsFieldHomIsoΣ (quote IsFieldHom)

FieldHom : (R : Field ℓ) (S : Field ℓ') → Type (ℓ-max ℓ ℓ')
FieldHom R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsFieldHom (R .snd) f (S .snd)

IsFieldEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : FieldStr A) (e : A ≃ B) (S : FieldStr B) → Type (ℓ-max ℓ ℓ')
IsFieldEquiv R e S = IsFieldHom R (e .fst) S

FieldEquiv : (R : Field ℓ) (S : Field ℓ') → Type (ℓ-max ℓ ℓ')
FieldEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsFieldEquiv (R .snd) e (S .snd)

_$_ : {R S : Field ℓ} → (φ : FieldHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $ x = φ .fst x

FieldEquiv→FieldHom : {A B : Field ℓ} → FieldEquiv A B → FieldHom A B
FieldEquiv→FieldHom (e , eIsHom) = e .fst , eIsHom

isPropIsField : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) (_[_]⁻¹ : (x : R) → ¬ (x ≡ 0r) → R)
             → isProp (IsField 0r 1r _+_ _·_ -_ _[_]⁻¹)
isPropIsField 0r 1r _+_ _·_ -_ _[_]⁻¹ (isfield RR RC RD) (isfield SR SC SD) =
  λ i → isfield (isPropIsCommRing _ _ _ _ _ RR SR i)
                   (isPropInv RC SC i) (isProp→⊥ RD SD i)
  where
  isSetR : isSet _
  isSetR =  RR .IsCommRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropInv : isProp ((x : _) → (≢0 : ¬ (x ≡ 0r)) → x · (x [ ≢0 ]⁻¹) ≡ 1r)
  isPropInv = isPropΠ2 λ _ _ → isSetR _ _

  isProp→⊥ : ∀ {A : Type ℓ} → isProp (A → ⊥)
  isProp→⊥ = isPropΠ λ _ → isProp⊥
