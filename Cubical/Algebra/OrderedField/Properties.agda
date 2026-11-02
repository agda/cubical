module Cubical.Algebra.OrderedField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.HeytingField
open import Cubical.Algebra.OrderedCommRing as OCR hiding (module Positive)
open import Cubical.Algebra.OrderedField.Base
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

private
  variable
    ℓ ℓ' : Level

OrderedField→StrictOrder : OrderedField ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedField→StrictOrder = OrderedCommRing→StrictOrder ∘ OrderedField→OrderedCommRing

OrderedField→Ring : OrderedField ℓ ℓ' → Ring ℓ
OrderedField→Ring = OrderedCommRing→Ring ∘ OrderedField→OrderedCommRing

OrderedField→PseudoLattice : OrderedField ℓ ℓ' → Pseudolattice ℓ ℓ'
OrderedField→PseudoLattice = OrderedCommRing→PseudoLattice ∘ OrderedField→OrderedCommRing

OrderedField→Poset : OrderedField ℓ ℓ' → Poset ℓ ℓ'
OrderedField→Poset = OrderedCommRing→Poset ∘ OrderedField→OrderedCommRing

OrderedField→Quoset : OrderedField ℓ ℓ' → Quoset ℓ ℓ'
OrderedField→Quoset = OrderedCommRing→Quoset ∘ OrderedField→OrderedCommRing

module _ (F' : OrderedField ℓ ℓ') where
  private
    F = fst F'
    FOCR = OrderedField→OrderedCommRing F'
    FCR  = OrderedField→CommRing F'

  open module OrderedFieldReasoning = OrderedCommRingReasoning FOCR

  open OrderedFieldStr (snd F')
  open HeytingFieldStr (snd (OrderedField→HeytingField F')) using (_#_)

  open Exponentiation FCR

  module OrderedFieldTheory where
    open OrderedCommRingTheory FOCR hiding (_#_) public
    open HeytingFieldTheory (OrderedField→HeytingField F') public

    0<→∈Fˣ : {x : F} {0< : 0f < x} → x ∈ Fˣ
    0<→∈Fˣ {x} {0<} = #0→isInv x (inr 0<)

    0<→0<⁻¹ : (x : F) → 0f < x → ⦃ _ : x # 0f ⦄ → 0f < x ⁻¹
    0<→0<⁻¹ x 0<x with uncurry (isInv→#0 (x ⁻¹)) (RˣInvClosed x)
    ... | inl x⁻¹<0 = ⊥.rec $ is-asym 0f 1f 0<1 $
      subst2 _<_ (·-rinv x) (0RightAnnihilates x) ([ x , 0<x ]·< x⁻¹<0)
    ... | inr 0<x⁻¹ = 0<x⁻¹

    <0→⁻¹<0 : (x : F) → x < 0f → ⦃ _ : x # 0f ⦄ → x ⁻¹ < 0f
    <0→⁻¹<0 x x<0 with uncurry (isInv→#0 (x ⁻¹)) (RˣInvClosed x)
    ... | inl x⁻¹<0 = x⁻¹<0
    ... | inr 0<x⁻¹ = ⊥.rec $ is-asym (- 1f) 0f (0<→-<0 1f 0<1) $
      subst2 _<_ (0RightAnnihilates (- x)) (-DistL· x (x ⁻¹) ∙ cong -_ (·-rinv x))
        ([ - x , <0→0<- x x<0 ]·< 0<x⁻¹)

    ·CancelR< : ∀ x y z → 0f < z → x · z < y · z → x < y
    ·CancelR< x y z 0<z = let instance z#0 = inr 0<z in
        subst2 _<_ (multiplyDivide x z) (multiplyDivide y z)
      ∘ ·MonoR< _ _ (z ⁻¹) (0<→0<⁻¹ z 0<z)

    ·CancelL< : ∀ x y z → 0f < z → z · x < z · y → x < y
    ·CancelL< x y z 0<z = ·CancelR< x y z 0<z ∘ subst2 _<_ (·Comm _ _) (·Comm _ _)

    0<→⁻¹Flip< : (x y : F) ⦃ _ : x # 0f ⦄ ⦃ _ : y # 0f ⦄ → 0f < x → x < y → y ⁻¹ < x ⁻¹
    0<→⁻¹Flip< x y 0<x x<y = ·CancelL< _ _ (x · y)
      (subst (_< _) (0LeftAnnihilates y) (·MonoR< _ _ _ (is-trans< _ _ _ 0<x x<y) 0<x))
      (subst2 _<_ (sym (·R/ x y)) (sym (·L/ x y)) x<y)

    0<→⁻¹Flip<' : (x y : F) ⦃ _ : x # 0f ⦄ ⦃ _ : y # 0f ⦄ → 0f < y → y ⁻¹ < x ⁻¹ → x < y
    0<→⁻¹Flip<' x y 0<y y⁻¹<x⁻¹ = subst2 _<_
      (isInvol⁻¹ x ⦃ r⁻¹∈Rˣ = #0→isInv (x ⁻¹) (x ⁻¹#0) ⦄)
      (isInvol⁻¹ y ⦃ r⁻¹∈Rˣ = #0→isInv (y ⁻¹) (y ⁻¹#0) ⦄)
      (0<→⁻¹Flip< _ _ ⦃ y ⁻¹#0 ⦄ ⦃ x ⁻¹#0 ⦄ (0<→0<⁻¹ y 0<y) y⁻¹<x⁻¹)

  open OrderedFieldTheory

  module Positive
    (0<+Closed : (x y : F) → 0f < x → 0f < y → 0f < x + y)
    (0<·Closed : (x y : F) → 0f < x → 0f < y → 0f < x · y)
    where

    open OCR.Positive FOCR 0<+Closed 0<·Closed public renaming (
      R₊ to F₊ ; isSetR₊ to isSetF₊ ; ≡₊→R₊ to ≡₊→F₊)

    instance
      ₊→#0 : {y : F₊} → ⟨ y ⟩₊ # 0f
      ₊→#0 {y} = inr (snd y)

    _⁻¹₊ : F₊ → F₊
    fst (y ⁻¹₊) = ⟨ y ⟩₊ ⁻¹
    snd (y ⁻¹₊) = 0<→0<⁻¹ ⟨ y ⟩₊ (snd y) ⦃ inr (snd y) ⦄

    _/₊_ : F → F₊ → F
    x /₊ y = x · ⟨ y ⁻¹₊ ⟩₊

    _₊/₊_ : F₊ → F₊ → F₊
    x ₊/₊ y = x ·₊ y ⁻¹₊

    infix 9 _⁻¹₊
    infixl 9 _/₊_ _₊/₊_

    ·₊-rinv : ∀ x → ⟨ x ₊/₊ x ⟩₊ ≡ 1f
    ·₊-rinv x = ·-rinv ⟨ x ⟩₊

    ·₊-linv : ∀ x → ⟨ x ⁻¹₊ ·₊ x ⟩₊ ≡ 1f
    ·₊-linv x = ·-linv ⟨ x ⟩₊

    /₊· : ∀ x y → x /₊ y · ⟨ y ⟩₊ ≡ x
    /₊· x y = divideMultiply x ⟨ y ⟩₊

    ₊/₊· : ∀ x y → ⟨ x ₊/₊ y ⟩₊ · ⟨ y ⟩₊ ≡ ⟨ x ⟩₊
    ₊/₊· x y = divideMultiply ⟨ x ⟩₊ ⟨ y ⟩₊

    ·/₊ : ∀ x y → ⟨ y ⟩₊ · x /₊ y ≡ x
    ·/₊ x y = divideMultiply' x ⟨ y ⟩₊

    ·₊/₊ : ∀ x y → ⟨ y ⟩₊ · ⟨ x ₊/₊ y ⟩₊ ≡ ⟨ x ⟩₊
    ·₊/₊ x y = divideMultiply' ⟨ x ⟩₊ ⟨ y ⟩₊

    ⁻¹Flip<₊ : ∀ x y → x <₊ y → y ⁻¹₊ <₊ x ⁻¹₊
    ⁻¹Flip<₊ x y = 0<→⁻¹Flip< ⟨ x ⟩₊ ⟨ y ⟩₊ (snd x)

    ⁻¹Flip<₊' : ∀ x y → y ⁻¹₊ <₊ x ⁻¹₊ → x <₊ y
    ⁻¹Flip<₊' x y = 0<→⁻¹Flip<' ⟨ x ⟩₊ ⟨ y ⟩₊ (snd y)

    <₊1→1<₊⁻¹ : ∀ x → x <₊ 1₊ → 1₊ <₊ x ⁻¹₊
    <₊1→1<₊⁻¹ x = subst (_< ⟨ x ⁻¹₊ ⟩₊) 1⁻¹≡1 ∘ ⁻¹Flip<₊ x 1₊

    <→1<₊/₊ : ∀ x y → x <₊ y → 1₊ <₊ y ₊/₊ x
    <→1<₊/₊ x y = ·CancelR< _ _ _ (snd x) ∘ subst2 _<_ (sym (·IdL _)) (sym (₊/₊· y x))

    ₊^-⁻¹₊ : ∀ x n → ⟨ (x ⁻¹₊) ₊^ n ⟩₊ ≡ ⟨ (x ₊^ n) ⁻¹₊ ⟩₊
    ₊^-⁻¹₊ x n = ^-⁻¹ ⟨ x ⟩₊ n
