module Cubical.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.HeytingField.Base
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Binary.Order.Apartness

private
  variable
    ℓ ℓ' ℓ'' ℓ<≤ ℓ<≤' ℓ<≤'' : Level

record IsOrderedField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isorderedfield
  field
    isOrderedCommRing : IsOrderedCommRing 0f 1f _+_ _·_ -_ _<_ _≤_
    #0→isInv          : ∀ x → (x < 0f) ⊎ (0f < x) → Σ[ y ∈ F ] x · y ≡ 1f
    isInv→#0          : ∀ x y → x · y ≡ 1f → (x < 0f) ⊎ (0f < x)

  open IsOrderedCommRing isOrderedCommRing public

record OrderedFieldStr (ℓ' : Level) (F : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_

  open IsOrderedField isOrderedField public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix  4 _<_ _≤_

OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = TypeWithStr ℓ (OrderedFieldStr ℓ')

OrderedField→OrderedCommRing : OrderedField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedField→OrderedCommRing F .fst = F . fst
OrderedField→OrderedCommRing F .snd = orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing
  where open OrderedFieldStr (snd F)

OrderedField→CommRing : OrderedField ℓ ℓ' → CommRing ℓ
OrderedField→CommRing = OrderedCommRing→CommRing ∘ OrderedField→OrderedCommRing

OrderedField→Apartness : OrderedField ℓ ℓ' → Apartness ℓ ℓ'
OrderedField→Apartness = OrderedCommRing→Apartness ∘ OrderedField→OrderedCommRing

-- The definition "OCR + invertible iff apart from zero", where apartness is derived
-- from the strict order, is sufficient to satisfy the conditions of an Heyting Fields.
OrderedField→HeytingField : OrderedField ℓ ℓ' → HeytingField ℓ ℓ'
fst (OrderedField→HeytingField F) = fst F
snd (OrderedField→HeytingField F) = heytingfieldstr _ _ _ _ _ _ isHF where
  open IsHeytingField
  module F where
    open OrderedFieldStr (str F) public
    open ApartnessStr (str (OrderedField→Apartness F)) public
    open OrderedCommRingTheory (OrderedField→OrderedCommRing F) hiding (_#_) public

  isHF : IsHeytingField F.0f F.1f F._+_ F._·_ F.-_ F._#_
  isHF .isCommRing  = F.isCommRing
  isHF .isApartness = F.isApartness
  isHF .isTight     = F.isTight#
  isHF .+Respect#R  = λ x y z → ⊎.map (F.+MonoR< x y z) (F.+MonoR< y x z)
  isHF .#0→isInv    = F.#0→isInv
  isHF .isInv→#0    = F.isInv→#0

-- OrderedField homomorphisms are just OCR monomorphisms on the underlying OCR structure,
-- but we still define them as records, because this helps with implicit argument
-- resolution in later definitions (e.g. `compOFHom`)
record IsOrderedFieldHom {A : Type ℓ} {B : Type ℓ'}
  (F : OrderedFieldStr ℓ<≤ A)
  (f : A → B)
  (K : OrderedFieldStr ℓ<≤' B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤')))
  where
  no-eta-equality
  private
    Focring = snd (OrderedField→OrderedCommRing (A , F))
    Kocring = snd (OrderedField→OrderedCommRing (B , K))

  field
    isOrderedCommRingMono : IsOrderedCommRingMono Focring f Kocring

  open IsOrderedCommRingMono isOrderedCommRingMono public

OrderedFieldHom : OrderedField ℓ ℓ<≤ → OrderedField ℓ' ℓ<≤' → Type _
OrderedFieldHom F K = Σ[ f ∈ (⟨ F ⟩ → ⟨ K ⟩) ] IsOrderedFieldHom (F .snd) f (K .snd)

OrderedFieldHom→OrderedCommRingMono : {F : OrderedField ℓ  ℓ<≤}
                                    → {K : OrderedField ℓ' ℓ<≤'}
                                    → OrderedFieldHom F K
                                    → OrderedCommRingMono
                                        (OrderedField→OrderedCommRing F)
                                        (OrderedField→OrderedCommRing K)
fst (OrderedFieldHom→OrderedCommRingMono f) = fst f
snd (OrderedFieldHom→OrderedCommRingMono f) = isOrderedCommRingMono
  where open IsOrderedFieldHom (snd f)

OrderedFieldHom→OrderedCommRingHom : {F : OrderedField ℓ  ℓ<≤}
                                   → {K : OrderedField ℓ' ℓ<≤'}
                                   → OrderedFieldHom F K
                                   → OrderedCommRingHom
                                      (OrderedField→OrderedCommRing F)
                                      (OrderedField→OrderedCommRing K)
OrderedFieldHom→OrderedCommRingHom =
  OrderedCommRingMono→OrderedCommRingHom ∘ OrderedFieldHom→OrderedCommRingMono

OrderedFieldHom→CommRingHom : {F : OrderedField ℓ  ℓ<≤}
                            → {K : OrderedField ℓ' ℓ<≤'}
                            → OrderedFieldHom F K
                            → CommRingHom
                               (OrderedField→CommRing F)
                               (OrderedField→CommRing K)
OrderedFieldHom→CommRingHom =
  OrderedCommRingMono→CommRingHom ∘ OrderedFieldHom→OrderedCommRingMono

idOFHom : (F : OrderedField ℓ ℓ<≤) → OrderedFieldHom F F
idOFHom F .fst = idfun ⟨ F ⟩
idOFHom F .snd .IsOrderedFieldHom.isOrderedCommRingMono = snd (idOCRMono _)

module _
  {F : OrderedField ℓ ℓ<≤} {K : OrderedField ℓ' ℓ<≤'} {H : OrderedField ℓ'' ℓ<≤''}
  where

  open IsOrderedFieldHom renaming (isOrderedCommRingMono to isOCR↪)

  compOFHom : OrderedFieldHom F K → OrderedFieldHom K H → OrderedFieldHom F H
  compOFHom f g .fst = fst g ∘ fst f
  compOFHom f g .snd .isOCR↪ =
    snd (compOCRMono (_ , isOCR↪ (snd f)) (_ , isOCR↪ (snd g)))

  _∘of_ : OrderedFieldHom K H → OrderedFieldHom F K → OrderedFieldHom F H
  _∘of_ = flip compOFHom
