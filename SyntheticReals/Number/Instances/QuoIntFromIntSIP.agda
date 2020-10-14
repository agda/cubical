{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Instances.QuoIntFromIntSIP where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything hiding (⋆) renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

-- open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
-- open import Cubical.Relation.Binary.Base
-- open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
-- open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
-- open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
-- open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation --.Properties
open import Cubical.Foundations.SIP

-- open import SyntheticReals.Utils using (!_; !!_)
-- open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions
-- open import SyntheticReals.MoreLogic.Properties
-- open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
-- open import SyntheticReals.MorePropAlgebra.Structures
-- open import SyntheticReals.MorePropAlgebra.Bundles
-- open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.Number.Structures2
open import SyntheticReals.Number.Bundles2

-- import Agda.Builtin.Int as Builtin
-- import Data.Integer.Base as BuiltinBase
-- import Data.Integer.Properties as BuiltinProps

-- open import Cubical.Data.Nat.Literals
-- open import Number.Prelude.Nat
-- open import Number.Prelude.Int
-- import Cubical.Data.Int as Int
-- import Number.Instances.Int

-- LinearlyOrderedCommRing ≡ LOCR

record LOCRStructure {ℓ ℓ'} (Carrier : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor locrstructure
  field
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
    is-LOCR : [ isLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max ]

LOCRΣ : ∀{ℓ ℓ'} → Type (ℓ-suc (ℓ-max ℓ ℓ'))
LOCRΣ {ℓ} {ℓ'} = TypeWithStr {ℓ' = ℓ-max ℓ (ℓ-suc ℓ')} ℓ (LOCRStructure {ℓ} {ℓ'})

record LOCRΣEquiv {ℓ} {ℓ'} (Σ₁ Σ₂ : LOCRΣ {ℓ} {ℓ'}) (Carrier₁≃₂ : fst Σ₁ ≃ fst Σ₂) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor locrΣequiv
  Carrier₁   = fst Σ₁
  Carrier₂   = fst Σ₂
  Structure₁ = snd Σ₁
  Structure₂ = snd Σ₂
  private
    module ₁ = LOCRStructure Structure₁
    module ₂ = LOCRStructure Structure₂
  〚_〛 = equivFun Carrier₁≃₂
  field
    pres0 : 〚 ₁.0f 〛 ≡ ₂.0f
    pres1 : 〚 ₁.1f 〛 ≡ ₂.1f
    isHom--   : ∀ y   → 〚         ₁.- y 〛 ≡             ₂.- 〚 y 〛
    isHom-+   : ∀ x y → 〚       x ₁.+ y 〛 ≡       〚 x 〛 ₂.+ 〚 y 〛
    isHom-·   : ∀ x y → 〚       x ₁.· y 〛 ≡       〚 x 〛 ₂.· 〚 y 〛
    isHom-min : ∀ x y → 〚 ₁.min x     y 〛 ≡ ₂.min 〚 x 〛     〚 y 〛
    isHom-max : ∀ x y → 〚 ₁.max x     y 〛 ≡ ₂.max 〚 x 〛     〚 y 〛
    isHom-<   : ∀ x y →         x ₁.< y   ≡       〚 x 〛 ₂.< 〚 y 〛

LOCREquivStr : ∀{ℓ ℓ'} → StrEquiv (LOCRStructure {ℓ} {ℓ'}) (ℓ-max ℓ (ℓ-suc ℓ'))
LOCREquivStr Σ₁@(Carrier₁ , Structure₁) Σ₂@(Carrier₂ , Structure₂) Carrier₁≃₂ = LOCRΣEquiv Σ₁ Σ₂ Carrier₁≃₂

LOCRUnivalentStructure : ∀{ℓ ℓ'} → UnivalentStr (LOCRStructure {ℓ} {ℓ'}) LOCREquivStr
LOCRUnivalentStructure {A = Σ₁@(Carrier₁ , Structure₁)} {B = Σ₂@(Carrier₂ , Structure₂)} Carrier₁≃₂ = f , φ where
  Carrier₁≡Carrier₂ : Carrier₁ ≡ Carrier₂
  Carrier₁≡Carrier₂ = ua Carrier₁≃₂
  module ₁ = LOCRStructure Structure₁
  module ₂ = LOCRStructure Structure₂
  〚_〛 = equivFun Carrier₁≃₂
  -- {-# DISPLAY equivFun Carrier₁≃₂ x = 〚 x 〛 #-} -- somehow omits its `x` ?

  -- I guess this is what we have "the machinery" for
  f : LOCREquivStr Σ₁ Σ₂ Carrier₁≃₂
    → PathP (λ i → LOCRStructure (Carrier₁≡Carrier₂ i)) Structure₁ Structure₂
  f (locrΣequiv pres0 pres1 isHom-- isHom-+ isHom-· isHom-min isHom-max isHom-<) = {!   !}
  φ : isEquiv f
  φ .equiv-proof Structure₁≡₂ = {!   !}

-- R ≃[ LOCREquivStr ] S ≡ Σ _ (LOCRΣEquiv R S)
-- LOCRΣPath : ∀{ℓ ℓ'} (R S : LOCRΣ {ℓ} {ℓ'}) → (R ≃[ LOCREquivStr ] S) ≃ (R ≡ S)
-- "an equivalence between the two carriers that fulfills the axioms in `LOCRΣEquiv` is equivalent to a path between the two structures"
LOCRΣPath* : ∀{ℓ ℓ'} (R S : LOCRΣ {ℓ} {ℓ'}) → Σ _ (LOCRΣEquiv R S) ≃ (R ≡ S)
LOCRΣPath* = SIP LOCRUnivalentStructure

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint -- congIso

module _ {ℓ ℓ'} where
  LOCRRawStructure'    = λ(X : Type ℓ) → X × X × (X → X) × (X → X → X) × (X → X → X) × (X → X → X) × (X → X → X) × (X → X → hProp ℓ')
  LOCRRawEquivStr'     = AutoEquivStr LOCRRawStructure'

  LOCRRawUnivalentStr' : UnivalentStr _ LOCRRawEquivStr'
  LOCRRawUnivalentStr' = autoUnivalentStr LOCRRawStructure'

  LOCRAxioms' : (X : Type ℓ) (Structure : LOCRRawStructure' X) → _
  LOCRAxioms' X (0f , 1f , -_ , _+_ , _·_ , min , max , _<_) = [ isLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max ]

  LOCRStructure'          = AxiomsStructure LOCRRawStructure' LOCRAxioms'
  LOCRΣ'                  = TypeWithStr ℓ LOCRStructure'
  LOCREquivStr'           = AxiomsEquivStr LOCRRawEquivStr' LOCRAxioms'

  LOCRUnivalentStructure' : UnivalentStr LOCRStructure' LOCREquivStr'
  LOCRUnivalentStructure' = axiomsUnivalentStr _ γ LOCRRawUnivalentStr' where
    γ : (X : Type ℓ) (s : LOCRRawStructure' X) → isProp (LOCRAxioms' X s)
    γ X (0f , 1f , -_ , _+_ , _·_ , min , max , _<_) = isProp[] (isLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max)

  LOCRΣPath' : (A B : LOCRΣ') → (A ≃[ LOCREquivStr' ] B) ≃ (A ≡ B)
  LOCRΣPath' = SIP LOCRUnivalentStructure'

  LOCRΣ→' : LOCRΣ {ℓ} {ℓ'} → LOCRΣ'
  LOCRΣ→' (X , s) = let open LOCRStructure s in X , (0f , 1f , -_ , _+_ , _·_ , min , max , _<_) , is-LOCR

  LOCRΣ←' : LOCRΣ' → LOCRΣ {ℓ} {ℓ'}
  LOCRΣ←' (X , (0f , 1f , -_ , _+_ , _·_ , min , max , _<_) , is-LOCR) = (X , γ) where
    γ : LOCRStructure {ℓ} {ℓ'} X
    γ  .LOCRStructure.0f      = 0f
    γ  .LOCRStructure.1f      = 1f
    γ  .LOCRStructure._+_     = _+_
    γ  .LOCRStructure.-_      = -_
    γ  .LOCRStructure._·_     = _·_
    γ  .LOCRStructure.min     = min
    γ  .LOCRStructure.max     = max
    γ  .LOCRStructure._<_     = _<_
    γ  .LOCRStructure.is-LOCR = is-LOCR

  LOCRΣIso : Iso LOCRΣ LOCRΣ'
  LOCRΣIso = iso LOCRΣ→' LOCRΣ←' (λ _ → refl) (λ _ → refl)

  LOCRΣEquiv' = λ(A B : LOCRΣ {ℓ} {ℓ'}) → LOCRΣ→' A ≃[ LOCREquivStr' ] LOCRΣ→' B

  LOCRΣEquivIso : {R S : LOCRΣ} → Iso (Σ _ (LOCRΣEquiv R S)) (LOCRΣEquiv' R S)
  LOCRΣEquivIso .Iso.fun (Carrier₁≃₂ , locrΣequiv pres0   pres1   isHom--   isHom-+   isHom-·   isHom-min   isHom-max   isHom-<) =
                         (Carrier₁≃₂ ,            pres0 , pres1 , isHom-- , isHom-+ , isHom-· , isHom-min , isHom-max , isHom-<)
  LOCRΣEquivIso .Iso.inv (Carrier₁≃₂ ,            pres0 , pres1 , isHom-- , isHom-+ , isHom-· , isHom-min , isHom-max , isHom-<) =
                         (Carrier₁≃₂ , locrΣequiv pres0   pres1   isHom--   isHom-+   isHom-·   isHom-min   isHom-max   isHom-<)
  LOCRΣEquivIso .Iso.rightInv _ = refl
  LOCRΣEquivIso .Iso.leftInv  _ = refl

  -- obtained by SIP-machinery:
  --   our previously defined LOCRΣEquiv-record is equivalent to a path
  LOCRΣPath : (R S : LOCRΣ {ℓ} {ℓ'}) → Σ _ (LOCRΣEquiv R S) ≃ (R ≡ S)
  LOCRΣPath R S =
    Σ _ (LOCRΣEquiv R S) ≃⟨ isoToEquiv LOCRΣEquivIso ⟩
    LOCRΣEquiv' R S ≃⟨ LOCRΣPath' _ _ ⟩
    LOCRΣ→' R ≡ LOCRΣ→' S ≃⟨ isoToEquiv (invIso (congIso LOCRΣIso)) ⟩
    R ≡ S ■
