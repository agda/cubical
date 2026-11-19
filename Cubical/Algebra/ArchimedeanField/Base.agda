module Cubical.Algebra.ArchimedeanField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.HeytingField
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedField.Base
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.OrderedField.PropertiesWithRationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ

private
  variable
    ℓ ℓ' ℓ'' ℓ<≤ ℓ<≤' ℓ<≤'' : Level

record IsArchimedeanField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ')
  (ι : ℚ → F) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isarchimedeanfield
  field
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_
  private
    Fofield = orderedfieldstr _ _ _ _ _ _ _ isOrderedField
  field
    isOrderedFieldHomι : IsOrderedFieldHom {B = F} (snd ℚOrderedField) ι _
    isArchimedeanWithι : ℚ↪Theory.isArchimedean (_ , Fofield) (ι , isOrderedFieldHomι)

  open IsOrderedField isOrderedField public
  open IsOrderedFieldHom isOrderedFieldHomι public
    renaming
      ( isOrderedCommRingHom to isOrderedCommRingHomι ;
        isCommRingHom to isCommRingHomι ;
        pres0 to ιpres0 ;
        pres1 to ιpres1 ;
        pres+ to ιpres+ ;
        pres· to ιpres· ;
        pres- to ιpres- ;
        pres≤ to ιpres≤ ;
        reflect< to ιreflect< ;
        pres< to ιpres<)

record ArchimedeanFieldStr (ℓ' : Level) (F : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    ι : ℚ → F
    isArchimedeanField : IsArchimedeanField 0f 1f _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanField isArchimedeanField public

  infix 8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanField ℓ ℓ' = TypeWithStr ℓ (ArchimedeanFieldStr ℓ')

ArchimedeanField→OrderedField : ArchimedeanField ℓ ℓ' → OrderedField ℓ ℓ'
fst (ArchimedeanField→OrderedField F) = fst F
snd (ArchimedeanField→OrderedField F) = orderedfieldstr _ _ _ _ _ _ _ isOrderedField
  where open ArchimedeanFieldStr (snd F)

ArchimedeanField→HeytingField : ArchimedeanField ℓ ℓ' → HeytingField ℓ ℓ'
ArchimedeanField→HeytingField =
  OrderedField→HeytingField ∘ ArchimedeanField→OrderedField

ArchimedeanField→OrderedCommRing : ArchimedeanField ℓ ℓ' → OrderedCommRing ℓ ℓ'
ArchimedeanField→OrderedCommRing =
  OrderedField→OrderedCommRing ∘ ArchimedeanField→OrderedField

ArchimedeanField→CommRing : ArchimedeanField ℓ ℓ' → CommRing ℓ
ArchimedeanField→CommRing = OrderedCommRing→CommRing ∘ ArchimedeanField→OrderedCommRing

ArchimedeanField→Ring : ArchimedeanField ℓ ℓ' → Ring ℓ
ArchimedeanField→Ring = CommRing→Ring ∘ ArchimedeanField→CommRing

record IsArchimedeanFieldHom {A : Type ℓ} {B : Type ℓ'}
  (F : ArchimedeanFieldStr ℓ<≤ A)
  (f : A → B)
  (K : ArchimedeanFieldStr ℓ<≤' B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤')))
  where
  no-eta-equality
  private
    Fofield = snd (ArchimedeanField→OrderedField (A , F))
    Kofield = snd (ArchimedeanField→OrderedField (B , K))
  field
    isOrderedFieldHom : IsOrderedFieldHom Fofield f Kofield

  open IsOrderedFieldHom isOrderedFieldHom public

ArchimedeanFieldHom : ArchimedeanField ℓ ℓ<≤ → ArchimedeanField ℓ' ℓ<≤' → Type _
ArchimedeanFieldHom F K =
  Σ[ f ∈ (⟨ F ⟩ → ⟨ K ⟩) ] IsArchimedeanFieldHom (F .snd) f (K .snd)

ArchimedeanFieldHom→OrderedFieldHom : {F : ArchimedeanField ℓ  ℓ<≤}
                                    → {K : ArchimedeanField ℓ' ℓ<≤'}
                                    → ArchimedeanFieldHom F K
                                    → OrderedFieldHom
                                        (ArchimedeanField→OrderedField F)
                                        (ArchimedeanField→OrderedField K)
fst (ArchimedeanFieldHom→OrderedFieldHom f) = fst f
snd (ArchimedeanFieldHom→OrderedFieldHom f) = isOrderedFieldHom
  where open IsArchimedeanFieldHom (snd f)

ArchimedeanFieldHom→OrderedCommRingMono : {F : ArchimedeanField ℓ  ℓ<≤}
                                        → {K : ArchimedeanField ℓ' ℓ<≤'}
                                        → ArchimedeanFieldHom F K
                                        → OrderedCommRingMono
                                            (ArchimedeanField→OrderedCommRing F)
                                            (ArchimedeanField→OrderedCommRing K)
ArchimedeanFieldHom→OrderedCommRingMono =
  OrderedFieldHom→OrderedCommRingMono ∘ ArchimedeanFieldHom→OrderedFieldHom

ArchimedeanFieldHom→OrderedCommRingHom : {F : ArchimedeanField ℓ  ℓ<≤}
                                       → {K : ArchimedeanField ℓ' ℓ<≤'}
                                       → ArchimedeanFieldHom F K
                                       → OrderedCommRingHom
                                          (ArchimedeanField→OrderedCommRing F)
                                          (ArchimedeanField→OrderedCommRing K)
ArchimedeanFieldHom→OrderedCommRingHom =
  OrderedFieldHom→OrderedCommRingHom ∘ ArchimedeanFieldHom→OrderedFieldHom

ArchimedeanFieldHom→CommRingHom : {F : ArchimedeanField ℓ  ℓ<≤}
                                → {K : ArchimedeanField ℓ' ℓ<≤'}
                                → ArchimedeanFieldHom F K
                                → CommRingHom
                                   (ArchimedeanField→CommRing F)
                                   (ArchimedeanField→CommRing K)
ArchimedeanFieldHom→CommRingHom =
  OrderedFieldHom→CommRingHom ∘ ArchimedeanFieldHom→OrderedFieldHom

idAFHom : (F : ArchimedeanField ℓ ℓ<≤) → ArchimedeanFieldHom F F
idAFHom F .fst = idfun ⟨ F ⟩
idAFHom F .snd .IsArchimedeanFieldHom.isOrderedFieldHom = snd (idOFHom _)

module _
  {F : ArchimedeanField ℓ ℓ<≤}
  {K : ArchimedeanField ℓ' ℓ<≤'}
  {H : ArchimedeanField ℓ'' ℓ<≤''}
  where

  open IsArchimedeanFieldHom renaming (isOrderedFieldHom to isOFHom)

  compAFHom : ArchimedeanFieldHom F K → ArchimedeanFieldHom K H → ArchimedeanFieldHom F H
  compAFHom f g .fst = fst g ∘ fst f
  compAFHom f g .snd .isOFHom =
    snd (compOFHom (_ , isOFHom (snd f)) (_ , isOFHom (snd g)))

  _∘af_ : ArchimedeanFieldHom K H → ArchimedeanFieldHom F K → ArchimedeanFieldHom F H
  _∘af_ = flip compAFHom
