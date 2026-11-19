module Cubical.Algebra.ArchimedeanField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Fast.Int.Base using ()
open import Cubical.Data.NatPlusOne.Base using ()
open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedField.Base
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.ArchimedeanField.Base

open ArchimedeanFieldStr
open OrderedFieldStr

open 1/2∈R ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)

ℚArchimedeanField : ArchimedeanField ℓ-zero ℓ-zero
fst ℚArchimedeanField = ℚ
0f  (snd ℚArchimedeanField) = 0
1f  (snd ℚArchimedeanField) = 1
_+_ (snd ℚArchimedeanField) = _+ℚ_
_·_ (snd ℚArchimedeanField) = _·ℚ_
-_  (snd ℚArchimedeanField) = -ℚ_
_<_ (snd ℚArchimedeanField) = _<ℚ_
_≤_ (snd ℚArchimedeanField) = _≤ℚ_
ι   (snd ℚArchimedeanField) = idfun ℚ
isArchimedeanField (snd ℚArchimedeanField) = isArchimedeanFieldℚ
  where
  open IsArchimedeanField
  isArchimedeanFieldℚ : IsArchimedeanField _ _ _ _ _ _ _ _
  isArchimedeanFieldℚ .isOrderedField     = isOrderedField $ snd ℚOrderedField
  isArchimedeanFieldℚ .isOrderedFieldHomι = snd $ idOFHom ℚOrderedField
  isArchimedeanFieldℚ .isArchimedeanWithι =
    λ x y x<y → ∣ mean x y , <→<mean x y x<y , <→mean< x y x<y ∣₁
