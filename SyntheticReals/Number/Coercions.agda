{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Coercions where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Inclusions
open import SyntheticReals.Number.Base
open import SyntheticReals.MoreNatProperties

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

open PatternsProp

module Coerce-ℕ↪ℤ where
  open ℤ
  open IsROrderedCommSemiringInclusion -- ℕ↪ℤinc
  private f = ℕ↪ℤ
  abstract
    coerce-ℕ↪ℤ : ∀{p} → (x : Number (isNat , p)) → PositivityKindInterpretation isInt (coerce-PositivityKind isNat isInt p) (ℕ↪ℤ (num x))
    coerce-ℕ↪ℤ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℤ {x#0} (x ,, q) = preserves-#0 ℕ↪ℤinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℤ {0≤x} (x ,, q) = preserves-0≤ ℕ↪ℤinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℤ {0<x} (x ,, q) = preserves-0< ℕ↪ℤinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℕ↪ℤ {x≤0} (x ,, q) = preserves-≤0 ℕ↪ℤinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℚ where
  open ℚ
  open IsROrderedCommSemiringInclusion -- ℕ↪ℚinc
  private f = ℕ↪ℚ
  abstract
    coerce-ℕ↪ℚ : ∀{p} → (x : Number (isNat , p)) → PositivityKindInterpretation isRat (coerce-PositivityKind isNat isRat p) (ℕ↪ℚ (num x))
    coerce-ℕ↪ℚ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℚ {x#0} (x ,, q) = preserves-#0 ℕ↪ℚinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℚ {0≤x} (x ,, q) = preserves-0≤ ℕ↪ℚinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℚ {0<x} (x ,, q) = preserves-0< ℕ↪ℚinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℕ↪ℚ {x≤0} (x ,, q) = preserves-≤0 ℕ↪ℚinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℝ where
  open ℝ
  open IsROrderedCommSemiringInclusion -- ℕ↪ℝinc
  private f = ℕ↪ℝ
  abstract
    coerce-ℕ↪ℝ : ∀{p} → (x : Number (isNat , p)) → PositivityKindInterpretation isReal (coerce-PositivityKind isNat isReal p) (ℕ↪ℝ (num x))
    coerce-ℕ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℝ {x#0} (x ,, q) = preserves-#0 ℕ↪ℝinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℝ {0≤x} (x ,, q) = preserves-0≤ ℕ↪ℝinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℝ {0<x} (x ,, q) = preserves-0< ℕ↪ℝinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℕ↪ℝ {x≤0} (x ,, q) = preserves-≤0 ℕ↪ℝinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℂ where
  open ℂ
  open Isℕ↪ℂ -- ℕ↪ℂinc
  private f = ℕ↪ℂ
  abstract
    coerce-ℕ↪ℂ : ∀{p} → (x : Number (isNat , p)) → PositivityKindInterpretation isComplex (coerce-PositivityKind isNat isComplex p) (ℕ↪ℂ (num x))
    coerce-ℕ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 ℕ↪ℂinc i) (preserves-# ℕ↪ℂinc _ _ q)
    coerce-ℕ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℕ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 ℕ↪ℂinc i) (preserves-# ℕ↪ℂinc _ _ (ℕ.#-sym _ _ (ℕ.<-implies-# _ _ q)))
    coerce-ℕ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℤ↪ℚ where
  open ℚ
  open IsROrderedCommRingInclusion -- ℤ↪ℚinc
  private f = ℤ↪ℚ
  abstract
    coerce-ℤ↪ℚ : ∀{p} → (x : Number (isInt , p)) → PositivityKindInterpretation isRat (coerce-PositivityKind isInt isRat p) (ℤ↪ℚ (num x))
    coerce-ℤ↪ℚ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℚ {x#0} (x ,, q) = preserves-#0 ℤ↪ℚinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℤ↪ℚ {0≤x} (x ,, q) = preserves-0≤ ℤ↪ℚinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℤ↪ℚ {0<x} (x ,, q) = preserves-0< ℤ↪ℚinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℤ↪ℚ {x<0} (x ,, q) = preserves-<0 ℤ↪ℚinc _ q -- transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℤ↪ℚ {x≤0} (x ,, q) = preserves-≤0 ℤ↪ℚinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℤ↪ℝ where
  open ℝ
  open IsROrderedCommRingInclusion --  ℤ↪ℝinc
  private f = ℤ↪ℝ
  abstract
    coerce-ℤ↪ℝ : ∀{p} → (x : Number (isInt , p)) → PositivityKindInterpretation isReal (coerce-PositivityKind isInt isReal p) (ℤ↪ℝ (num x))
    coerce-ℤ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℝ {x#0} (x ,, q) = preserves-#0 ℤ↪ℝinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℤ↪ℝ {0≤x} (x ,, q) = preserves-0≤ ℤ↪ℝinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℤ↪ℝ {0<x} (x ,, q) = preserves-0< ℤ↪ℝinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℤ↪ℝ {x<0} (x ,, q) = preserves-<0 ℤ↪ℝinc _ q -- transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℤ↪ℝ {x≤0} (x ,, q) = preserves-≤0 ℤ↪ℝinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℤ↪ℂ where
  open ℂ
  open Isℤ↪ℂ -- ℤ↪ℂinc
  private f = ℤ↪ℂ
  abstract
    coerce-ℤ↪ℂ : ∀{p} → (x : Number (isInt , p)) → PositivityKindInterpretation isComplex (coerce-PositivityKind isInt isComplex p) (ℤ↪ℂ (num x))
    coerce-ℤ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 ℤ↪ℂinc i) (preserves-# ℤ↪ℂinc _ _ q)
    coerce-ℤ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℤ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 ℤ↪ℂinc i) (preserves-# ℤ↪ℂinc _ _ (ℤ.#-sym _ _ (ℤ.<-implies-# _ _ q)))
    coerce-ℤ↪ℂ {x<0} (x ,, q) = transport (λ i → f x # preserves-0 ℤ↪ℂinc i) (preserves-# ℤ↪ℂinc _ _              (ℤ.<-implies-# _ _ q) )
    coerce-ℤ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℚ↪ℝ where
  open ℝ
  open IsROrderedFieldInclusion -- ℚ↪ℝinc
  private f = ℚ↪ℝ
  abstract
    coerce-ℚ↪ℝ : ∀{p} → (x : Number (isRat , p)) → PositivityKindInterpretation isReal (coerce-PositivityKind isRat isReal p) (ℚ↪ℝ (num x))
    coerce-ℚ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℚ↪ℝ {x#0} (x ,, q) = preserves-#0 ℚ↪ℝinc _ q -- transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℚ↪ℝ {0≤x} (x ,, q) = preserves-0≤ ℚ↪ℝinc _ q -- transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℚ↪ℝ {0<x} (x ,, q) = preserves-0< ℚ↪ℝinc _ q -- transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℚ↪ℝ {x<0} (x ,, q) = preserves-<0 ℚ↪ℝinc _ q -- transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℚ↪ℝ {x≤0} (x ,, q) = preserves-≤0 ℚ↪ℝinc _ q -- transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℚ↪ℂ where
  open ℂ
  open IsRFieldInclusion -- ℚ↪ℂinc
  private f = ℚ↪ℂ
  abstract
    coerce-ℚ↪ℂ : ∀{p} → (x : Number (isRat , p)) → PositivityKindInterpretation isComplex (coerce-PositivityKind isRat isComplex p) (ℚ↪ℂ (num x))
    coerce-ℚ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℚ↪ℂ {x#0} (x ,, q) = preserves-#0 ℚ↪ℂinc _ q -- transport (λ i → f x # preserves-0 ℚ↪ℂinc i) (preserves-# ℚ↪ℂinc _ _ q)
    coerce-ℚ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℚ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 ℚ↪ℂinc i) (preserves-# ℚ↪ℂinc _ _ (ℚ.#-sym _ _ (ℚ.<-implies-# _ _ q)))
    coerce-ℚ↪ℂ {x<0} (x ,, q) = transport (λ i → f x # preserves-0 ℚ↪ℂinc i) (preserves-# ℚ↪ℂinc _ _              (ℚ.<-implies-# _ _ q) )
    coerce-ℚ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℝ↪ℂ where
  -- open ℂ
  open IsRFieldInclusion -- ℝ↪ℂinc
  private f = ℝ↪ℂ
  abstract
    coerce-ℝ↪ℂ : ∀{p} → (x : Number (isReal , p)) → PositivityKindInterpretation isComplex (coerce-PositivityKind isReal isComplex p) (ℝ↪ℂ (num x))
    coerce-ℝ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℝ↪ℂ {x#0} (x ,, q) = preserves-#0 ℝ↪ℂinc _ q -- transport (λ i → f x # preserves-0 ℝ↪ℂinc i) (preserves-# ℝ↪ℂinc _ _ q)
    coerce-ℝ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℝ↪ℂ {0<x} (x ,, q) = transport (λ i → f x ℂ.# preserves-0 ℝ↪ℂinc i) (preserves-# ℝ↪ℂinc _ _ (ℝ.#-sym _ _ (ℝ.<-implies-# _ _ q)))
    coerce-ℝ↪ℂ {x<0} (x ,, q) = transport (λ i → f x ℂ.# preserves-0 ℝ↪ℂinc i) (preserves-# ℝ↪ℂinc _ _              (ℝ.<-implies-# _ _ q) )
    coerce-ℝ↪ℂ {x≤0} (x ,, q) = lift tt

-- NOTE: typechecking of this module is very slow
--       the cause might be opening of the ten `IsXInclusion` instances
--       it could be related to https://github.com/agda/agda/issues/1646 (Exponential module chain leads to infeasible scope checking)
--       YES: this is the case. After shifting the module arguments from `open` into the code, checking became instant again

-- does this make anything faster?
open Coerce-ℕ↪ℤ public
open Coerce-ℕ↪ℚ public
open Coerce-ℕ↪ℝ public
open Coerce-ℕ↪ℂ public
open Coerce-ℤ↪ℚ public
open Coerce-ℤ↪ℝ public
open Coerce-ℤ↪ℂ public
open Coerce-ℚ↪ℝ public
open Coerce-ℚ↪ℂ public
open Coerce-ℝ↪ℂ public

coerce : (from : NumberKind)
       → (to   : NumberKind)
       → from ≤ₙₗ to
       → ∀{p}
       → Number (from ,                               p)
       → Number (to   , coerce-PositivityKind from to p)
coerce isNat     isNat     q {p} x = x
coerce isInt     isInt     q {p} x = x
coerce isRat     isRat     q {p} x = x
coerce isReal    isReal    q {p} x = x
coerce isComplex isComplex q {p} x = x
coerce isNat     isInt     q {p} x = (ℕ↪ℤ (num x) ,, coerce-ℕ↪ℤ x)
coerce isNat     isRat     q {p} x = (ℕ↪ℚ (num x) ,, coerce-ℕ↪ℚ x)
coerce isNat     isReal    q {p} x = (ℕ↪ℝ (num x) ,, coerce-ℕ↪ℝ x)
coerce isNat     isComplex q {p} x = (ℕ↪ℂ (num x) ,, coerce-ℕ↪ℂ x)
coerce isInt     isRat     q {p} x = (ℤ↪ℚ (num x) ,, coerce-ℤ↪ℚ x)
coerce isInt     isReal    q {p} x = (ℤ↪ℝ (num x) ,, coerce-ℤ↪ℝ x)
coerce isInt     isComplex q {p} x = (ℤ↪ℂ (num x) ,, coerce-ℤ↪ℂ x)
coerce isRat     isReal    q {p} x = (ℚ↪ℝ (num x) ,, coerce-ℚ↪ℝ x)
coerce isRat     isComplex q {p} x = (ℚ↪ℂ (num x) ,, coerce-ℚ↪ℂ x)
coerce isReal    isComplex q {p} x = (ℝ↪ℂ (num x) ,, coerce-ℝ↪ℂ x)
--coerce x         y         = nothing
coerce isInt     isNat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)
coerce isRat     isNat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)
coerce isRat     isInt  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isNat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isInt  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isRat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  , p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isNat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , coerce-PositivityKind isComplex isNat  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isInt  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , coerce-PositivityKind isComplex isInt  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isRat  r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  , coerce-PositivityKind isComplex isRat  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isReal r@(k , q) {p} x = ⊥-elim {A = λ _ → Number (isReal , coerce-PositivityKind isComplex isReal p)} (k+x+sy≢x _ _ _ q)
