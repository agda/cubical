module Cubical.Algebra.HeytingField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.HeytingField.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Functions.Logic using (_⊔′_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

open Characterizations.BinSum

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    F K H : HeytingField ℓ ℓ'

module HeytingFieldTheory (F : HeytingField ℓ ℓ') where
  open HeytingFieldStr (str F)
  open Sum (HeytingField→Ring F)
  open RingTheory (HeytingField→Ring F) public
  private
    FCRing = HeytingField→CommRing F
  open CommRingTheory FCRing public
  open Units FCRing renaming (Rˣ to Fˣ) public

  private
    variable
      x y : ⟨ F ⟩

  -- defined inside an instance block, in order to support ⁻¹ and / notation from `Units`
  instance
    #0→∈Fˣ : ⦃ x # 0f ⦄ → x ∈ Fˣ
    #0→∈Fˣ {x} ⦃ x#0 ⦄ = #0→isInv x x#0

  ∈Fˣ→#0 : x ∈ Fˣ → x # 0f
  ∈Fˣ→#0 = uncurry $ isInv→#0 _

  #→≢ : ∀ x y → x # y → ¬ x ≡ y
  #→≢ x _ = flip $ J (λ y _ → ¬ (x # y)) (is-irrefl x)

  isSeparatedField : Separated ⟨ F ⟩
  isSeparatedField x y = isTight x y ∘ (_∘ #→≢ x y)

  contrapos#→≡ : ∀ x y z w → (x # y → z # w) → z ≡ w → x ≡ y
  contrapos#→≡ x y z w x#y→z#w z≡w = isTight x y $ flip (#→≢ z w) z≡w ∘ x#y→z#w

  isNonTrivialField : 1f # 0f
  isNonTrivialField = ∈Fˣ→#0 RˣContainsOne

  +Respect#L : ∀ x y z → x # y → z + x # z + y
  +Respect#L x y z = subst2 _#_ (+Comm _ _) (+Comm _ _) ∘ +Respect#R x y z

  -- x # y is the same as invertibility of x - y
  -- However, in the definition I chose to let the user give a custom implementation of # for two reasons:
  -- It's sometimes more convenient, for example in an ordered field where we can define x # y to be x < y or y < x
  -- I also allow it to have a smaller universe level, which is useful when implementing e.g. the Dedekind reals predicatively
  #→ΔIsInv : ∀ x y → x # y → (x - y) ∈ Fˣ
  #→ΔIsInv x y = #0→isInv (x - y) ∘ subst (x - y #_) (+InvR y) ∘ +Respect#R x y (- y)

  ΔIsInv→# : ∀ x y → (x - y) ∈ Fˣ → x # y
  ΔIsInv→# x y (x-y⁻¹ , p) =
    subst2 _#_ (solve! FCRing) (+IdL y) (+Respect#R _ _ y (isInv→#0 _ x-y⁻¹ p))

  ·Respect#R : ∀ x y z → z # 0f → x # y → x · z # y · z
  ·Respect#R x y z z#0 x#y = ΔIsInv→# _ _ $ subst (_∈ Fˣ) (solve! FCRing) $
    RˣMultClosed _ _ ⦃ #→ΔIsInv _ _ x#y ⦄ ⦃ #0→∈Fˣ ⦃ z#0 ⦄ ⦄

  ·Respect#L : ∀ x y z → z # 0f → x # y → z · x # z · y
  ·Respect#L x y z z#0 = subst2 _#_ (·Comm _ _) (·Comm _ _) ∘ ·Respect#R x y z z#0

  +Cancel#R : ∀ x y z → x + z # y + z → x # y
  +Cancel#R x y z = subst2 _#_ (solve! FCRing) (solve! FCRing) ∘ +Respect#R _ _ (- z)

  +Cancel#L : ∀ x y z → z + x # z + y → x # y
  +Cancel#L x y z = +Cancel#R x y z ∘ subst2 _#_ (+Comm _ _) (+Comm _ _)

  _⁻¹#0 : ∀ z → ⦃ z#0 : z # 0f ⦄ → z ⁻¹ # 0f
  _⁻¹#0 z = ∈Fˣ→#0 (RˣInvClosed z)

  ·Cancel#R : ∀ x y z → x · z # y · z → x # y
  ·Cancel#R x y z xz#yz with #→ΔIsInv _ _ xz#yz
  ... | (xz-yz⁻¹ , p) = ΔIsInv→# _ _ $ z · xz-yz⁻¹ , solve! FCRing ∙ p

  ·Cancel#L : ∀ x y z → z · x # z · y → x # y
  ·Cancel#L x y z = ·Cancel#R x y z ∘ subst2 _#_ (·Comm _ _) (·Comm _ _)

  ·CancelR : ∀ x y z → z # 0f → x · z ≡ y · z → x ≡ y
  ·CancelR x y z = contrapos#→≡ _ _ _ _ ∘ ·Respect#R x y z

  ·CancelL : ∀ x y z → z # 0f → z · x ≡ z · y → x ≡ y
  ·CancelL x y z = contrapos#→≡ _ _ _ _ ∘ ·Respect#L x y z

  ·L/ : ∀ x y ⦃ _ : x # 0f ⦄ → (x · y) / x ≡ y
  ·L/ x y = multiplyDivide' y x

  ·R/ : ∀ x y ⦃ _ : y # 0f ⦄ → (x · y) / y ≡ x
  ·R/ x y = multiplyDivide x y

  is#BinSumLocalField : ∀ x y → x + y # 0f → (x # 0f) ⊔′ (y # 0f)
  is#BinSumLocalField x y = PT.map
    (⊎.map
      (idfun _)
      (is-sym _ _ ∘ subst2 _#_ (+InvL y) (+IdL y) ∘ +Respect#R _ _ y))
    ∘ is-cotrans x _ _ ∘ subst2 _#_ (solve! FCRing) (solve! FCRing)
    ∘ +Respect#R _ _ (- y)

  isBinSumLocalField : BinSum FCRing
  isBinSumLocalField x y =
    PT.map (⊎.map (#0→isInv x) (#0→isInv y)) ∘ is#BinSumLocalField x y ∘ ∈Fˣ→#0

  isLocalField : isLocal FCRing
  isLocalField =
    alternative→isLocal FCRing (#→≢ _ _ isNonTrivialField , isBinSumLocalField)

  is#LocalField : ∀ {n} (xs : FinVec ⟨ F ⟩ n) → (∑ xs) # 0f → ∃[ i ∈ Fin n ] (xs i # 0f)
  is#LocalField xs = PT.map (map-snd ∈Fˣ→#0) ∘ isLocalField xs ∘ #0→isInv _

-- Any homomorphism of rings automatically preserves the apartness
module _
  (F : HeytingField ℓ ℓ'') (K : HeytingField ℓ' ℓ''') (f : ⟨ F ⟩ → ⟨ K ⟩)
  (fIsRingHom : IsRingHom (HeytingFieldStr→RingStr (str F)) f (HeytingFieldStr→RingStr (str K))) where
  private
    module F where
      open HeytingFieldTheory F public
      open HeytingFieldStr (str F) public
    module K where
      open HeytingFieldTheory K public
      open HeytingFieldStr (str K) public

  isRingHomOfFieldsPres# : ∀ x y → x F.# y → f x K.# f y
  isRingHomOfFieldsPres# x y x#y =
    let (x-y⁻¹ , p) = F.#→ΔIsInv _ _ x#y
    in K.ΔIsInv→# _ _ $
      f x-y⁻¹
    , sym (pres· _ _ ∙∙ congL K._·_ (pres+ _ _) ∙∙ congL K._·_ (congR K._+_ (pres- _)))
      ∙∙ cong f p
      ∙∙ pres1
    where open IsRingHom fIsRingHom

  isInjRingHomOfFields : ∀ x y → f x ≡ f y → x ≡ y
  isInjRingHomOfFields x y fx≡fy =
    F.isTight _ _ λ x#y → K.#→≢ (f x) (f y) (isRingHomOfFieldsPres# x y x#y) fx≡fy

  module _ (strongExt : ∀ x y → f x K.# f y → x F.# y) where
    open IsHeytingFieldHom
    open IsRingHom

    strongExtRingHomIsFieldHom : IsHeytingFieldHom (str F) f (str K)
    strongExtRingHomIsFieldHom .pres0 = fIsRingHom .pres0
    strongExtRingHomIsFieldHom .pres1 = fIsRingHom .pres1
    strongExtRingHomIsFieldHom .pres+ = fIsRingHom .pres+
    strongExtRingHomIsFieldHom .pres· = fIsRingHom .pres·
    strongExtRingHomIsFieldHom .pres- = fIsRingHom .pres-
    strongExtRingHomIsFieldHom .pres# = λ x y → propBiimpl→Equiv
      (F.is-prop-valued _ _) (K.is-prop-valued _ _)
      (isRingHomOfFieldsPres# x y) (strongExt x y)

module _ {F : HeytingField ℓ ℓ''} {K : HeytingField ℓ' ℓ'''} (f : HeytingFieldHom F K) where
  isInjFieldHom : ∀ x y → f .fst x ≡ f .fst y → x ≡ y
  isInjFieldHom = isInjRingHomOfFields F K (f .fst) (isHeytingFieldHom→isRingHom (F .snd) _ (K .snd) (f .snd))

-- We can make a smart constructor for field homomorphisms,
-- as they are just strongly extensional ring homomorphisms
module _ {A : Type ℓ} {B : Type ℓ'} {F : HeytingFieldStr ℓ'' A} {K : HeytingFieldStr ℓ''' B} {f : A → B} where
  private
    module F = HeytingFieldStr F
    module K = HeytingFieldStr K

  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x K.+ f y) (pres1 : f F.1f ≡ K.1f)
           (pres· : ∀ x y → f (x F.· y) ≡ f x K.· f y) (strongExt : ∀ x y → f x K.# f y → x F.# y) where

    makeIsFieldHom : IsHeytingFieldHom F f K
    makeIsFieldHom = strongExtRingHomIsFieldHom _ _ f (makeIsRingHom pres1 pres+ pres·) strongExt

module _ {F : HeytingField ℓ ℓ''} {K : HeytingField ℓ' ℓ'''} (f : ⟨ F ⟩ → ⟨ K ⟩) where
  private
    module F = HeytingFieldStr (str F)
    module K = HeytingFieldStr (str K)

  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x K.+ f y) (pres1 : f F.1f ≡ K.1f)
           (pres· : ∀ x y → f (x F.· y) ≡ f x K.· f y) (strongExt : ∀ x y → f x K.# f y → x F.# y) where

    makeFieldHom : HeytingFieldHom F K
    makeFieldHom = f , makeIsFieldHom pres+ pres1 pres· strongExt

-- Although not every ring homomorphism is a field homomorphism, every ring equivalence is an equivalence of fields:
module _
  {A : Type ℓ} {B : Type ℓ'}
  {F : HeytingFieldStr ℓ'' A} (e : A ≃ B) {K : HeytingFieldStr ℓ''' B}
  (eIsRingEquiv : IsRingEquiv (HeytingFieldStr→RingStr F) e (HeytingFieldStr→RingStr K))
  where
  private
    module F = HeytingFieldStr F
    module K = HeytingFieldStr K

  ringEquivIsStrongExt : ∀ x y → e .fst x K.# e .fst y → x F.# y
  ringEquivIsStrongExt x y = subst2 F._#_ (retEq e x) (retEq e y) ∘
    isRingHomOfFieldsPres# (B , K) (A , F) (invEq e) (isRingHomInv (e , eIsRingEquiv)) _ _
    where open RingEquivs

  ringEquivIsFieldEquiv : IsHeytingFieldEquiv F e K
  ringEquivIsFieldEquiv = strongExtRingHomIsFieldHom _ _ _ eIsRingEquiv ringEquivIsStrongExt

module _ {F : HeytingField ℓ ℓ''} {K : HeytingField ℓ' ℓ'''} where
  RingEquiv→FieldEquiv : RingEquiv (HeytingField→Ring F) (HeytingField→Ring K) → HeytingFieldEquiv F K
  RingEquiv→FieldEquiv (e , eIsHom) = e , ringEquivIsFieldEquiv e eIsHom

  FieldEquiv≃RingEquiv : HeytingFieldEquiv F K ≃ RingEquiv (HeytingField→Ring F) (HeytingField→Ring K)
  FieldEquiv≃RingEquiv = Σ-cong-equiv-snd λ e →
    propBiimpl→Equiv (isPropIsHeytingFieldHom _ _ _) (isPropIsRingHom _ _ _)
                     (isHeytingFieldHom→isRingHom _ _ _) (ringEquivIsFieldEquiv e)

  isEquivHeytingFieldEquiv→RingEquiv : isEquiv (HeytingFieldEquiv→RingEquiv F K)
  isEquivHeytingFieldEquiv→RingEquiv = FieldEquiv≃RingEquiv .snd

  FieldEquiv≡ : {f g : HeytingFieldEquiv F K} → f .fst .fst ≡ g .fst .fst → f ≡ g
  FieldEquiv≡ = Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) ∘ Σ≡Prop (λ _ → isPropIsEquiv _)

open RingHoms
open IsHeytingFieldHom

idFieldHom : HeytingFieldHom F F
idFieldHom = _ , strongExtRingHomIsFieldHom _ _ _ (idRingHom _ .snd) λ _ _ → idfun _

compFieldHom : HeytingFieldHom F K → HeytingFieldHom K H → HeytingFieldHom F H
compFieldHom f g = _ , strongExtRingHomIsFieldHom _ _ _
  (compIsRingHom (HeytingFieldHom→RingHom _ _ g .snd) (HeytingFieldHom→RingHom _ _ f .snd))
  λ x y x#y → invEq (f .snd .pres# _ _) (invEq (g .snd .pres# _ _) x#y)

open RingEquivs

idFieldEquiv : HeytingFieldEquiv F F
idFieldEquiv = RingEquiv→FieldEquiv (idRingEquiv _)

compFieldEquiv : HeytingFieldEquiv F K → HeytingFieldEquiv K H → HeytingFieldEquiv F H
compFieldEquiv f g = RingEquiv→FieldEquiv $ compRingEquiv
  (HeytingFieldEquiv→RingEquiv _ _ f) (HeytingFieldEquiv→RingEquiv _ _ g)

invFieldEquiv : HeytingFieldEquiv F K → HeytingFieldEquiv K F
invFieldEquiv = RingEquiv→FieldEquiv ∘ invRingEquiv ∘ HeytingFieldEquiv→RingEquiv _ _

-- Discrete (Geometric) fields
module _ (F : HeytingField ℓ ℓ') where
  open HeytingFieldStr (str F)
  open HeytingFieldTheory F

  isDiscField : Type _
  isDiscField = ∀ x y → Dec (x # y)

  -- The underlying set of a Geometric field is discrete
  isDiscField→isDisc : isDiscField → Discrete ⟨ F ⟩
  isDiscField→isDisc FDisc x y with FDisc x y
  ... | yes x#y = no (#→≢ x y x#y)
  ... | no ¬x#y = yes (isTight x y ¬x#y)
