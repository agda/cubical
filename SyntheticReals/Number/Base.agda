{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.Number.Base where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)

open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Bundles

data NumberKind : Type where
  isNat     : NumberKind
  isInt     : NumberKind
  isRat     : NumberKind
  isReal    : NumberKind
  isComplex : NumberKind

-- NumberKindEnumeration
NLE : NumberKind → Nat
NLE isNat     = 0
NLE isInt     = 1
NLE isRat     = 2
NLE isReal    = 3
NLE isComplex = 4

-- inverse of NumberKindEnumeration
NLE⁻¹ : Nat → NumberKind
NLE⁻¹ 0 = isNat
NLE⁻¹ 1 = isInt
NLE⁻¹ 2 = isRat
NLE⁻¹ 3 = isReal
NLE⁻¹ 4 = isComplex
NLE⁻¹ x = isComplex -- doesn't matter

-- proof of inversity
NLE⁻¹-isRetraction : ∀ x → NLE⁻¹ (NLE x) ≡ x
NLE⁻¹-isRetraction isNat     = refl
NLE⁻¹-isRetraction isInt     = refl
NLE⁻¹-isRetraction isRat     = refl
NLE⁻¹-isRetraction isReal    = refl
NLE⁻¹-isRetraction isComplex = refl

-- order lifted from Nat
open import SyntheticReals.Enumeration NLE NLE⁻¹ NLE⁻¹-isRetraction using () renaming
  ( _≤'_ to _≤ₙₗ_
  ; min' to minₙₗ
  ; max' to maxₙₗ
  ; max-implies-≤' to max-implies-≤ₙₗ₂
  ) public

data PositivityKindOrderedRing : Type where
  anyPositivityᵒʳ : PositivityKindOrderedRing
  isNonzeroᵒʳ     : PositivityKindOrderedRing
  isNonnegativeᵒʳ : PositivityKindOrderedRing
  isPositiveᵒʳ    : PositivityKindOrderedRing
  isNegativeᵒʳ    : PositivityKindOrderedRing
  isNonpositiveᵒʳ : PositivityKindOrderedRing

data PositivityKindField : Type where
  anyPositivityᶠ : PositivityKindField
  isNonzeroᶠ     : PositivityKindField

PositivityKindType : NumberKind → Type
PositivityKindType isNat     = PositivityKindOrderedRing
PositivityKindType isInt     = PositivityKindOrderedRing
PositivityKindType isRat     = PositivityKindOrderedRing
PositivityKindType isReal    = PositivityKindOrderedRing
PositivityKindType isComplex = PositivityKindField

NumberProp = Σ NumberKind PositivityKindType

module PatternsType where
  -- ordered ring patterns
  pattern X   = anyPositivityᵒʳ
  pattern X⁺⁻ = isNonzeroᵒʳ
  pattern X₀⁺ = isNonnegativeᵒʳ
  pattern X⁺  = isPositiveᵒʳ
  pattern X⁻  = isNegativeᵒʳ
  pattern X₀⁻ = isNonpositiveᵒʳ
  -- field patterns (overlapping)
  pattern X   = anyPositivityᶠ
  pattern X⁺⁻ = isNonzeroᶠ

module PatternsProp where
  -- ordered ring patterns
  pattern ⁇x⁇ = anyPositivityᵒʳ
  pattern x#0 = isNonzeroᵒʳ
  pattern 0≤x = isNonnegativeᵒʳ
  pattern 0<x = isPositiveᵒʳ
  pattern x<0 = isNegativeᵒʳ
  pattern x≤0 = isNonpositiveᵒʳ
  -- field patterns (overlapping)
  pattern ⁇x⁇ = anyPositivityᶠ
  pattern x#0 = isNonzeroᶠ

open PatternsProp

coerce-PositivityKind-OR2F : PositivityKindOrderedRing → PositivityKindField
coerce-PositivityKind-OR2F ⁇x⁇ = ⁇x⁇
coerce-PositivityKind-OR2F x#0 = x#0
coerce-PositivityKind-OR2F 0≤x = ⁇x⁇
coerce-PositivityKind-OR2F 0<x = x#0
coerce-PositivityKind-OR2F x<0 = x#0
coerce-PositivityKind-OR2F x≤0 = ⁇x⁇

coerce-PositivityKind-F2OR : PositivityKindField → PositivityKindOrderedRing
coerce-PositivityKind-F2OR ⁇x⁇ = ⁇x⁇
coerce-PositivityKind-F2OR x#0 = x#0

coerce-PositivityKind-OR2 : PositivityKindOrderedRing → (to : NumberKind) → PositivityKindType to
coerce-PositivityKind-OR2 pl isNat     = pl
coerce-PositivityKind-OR2 pl isInt     = pl
coerce-PositivityKind-OR2 pl isRat     = pl
coerce-PositivityKind-OR2 pl isReal    = pl
coerce-PositivityKind-OR2 pl isComplex = coerce-PositivityKind-OR2F pl

coerce-PositivityKind-F2 : PositivityKindField → (to : NumberKind) → PositivityKindType to
coerce-PositivityKind-F2 pl isNat     = coerce-PositivityKind-F2OR pl
coerce-PositivityKind-F2 pl isInt     = coerce-PositivityKind-F2OR pl
coerce-PositivityKind-F2 pl isRat     = coerce-PositivityKind-F2OR pl
coerce-PositivityKind-F2 pl isReal    = coerce-PositivityKind-F2OR pl
coerce-PositivityKind-F2 pl isComplex = pl

coerce-PositivityKind : (from to : NumberKind) → PositivityKindType from → PositivityKindType to
coerce-PositivityKind isNat     to x = coerce-PositivityKind-OR2 x to
coerce-PositivityKind isInt     to x = coerce-PositivityKind-OR2 x to
coerce-PositivityKind isRat     to x = coerce-PositivityKind-OR2 x to
coerce-PositivityKind isReal    to x = coerce-PositivityKind-OR2 x to
coerce-PositivityKind isComplex to x = coerce-PositivityKind-F2  x to

-- NumberKind interpretation

NumberKindLevel : NumberKind → Level
NumberKindLevel isNat     = ℕℓ
NumberKindLevel isInt     = ℤℓ
NumberKindLevel isRat     = ℚℓ
NumberKindLevel isReal    = ℝℓ
NumberKindLevel isComplex = ℂℓ

NumberKindProplevel : NumberKind → Level
NumberKindProplevel isNat     = ℕℓ'
NumberKindProplevel isInt     = ℤℓ'
NumberKindProplevel isRat     = ℚℓ'
NumberKindProplevel isReal    = ℝℓ'
NumberKindProplevel isComplex = ℂℓ'

NumberKindInterpretation : (x : NumberKind) → Type (NumberKindLevel x)
NumberKindInterpretation isNat     = let open ℕ* in ℕ
NumberKindInterpretation isInt     = let open ℤ* in ℤ
NumberKindInterpretation isRat     = let open ℚ* in ℚ
NumberKindInterpretation isReal    = let open ℝ* in ℝ
NumberKindInterpretation isComplex = let open ℂ* in ℂ

-- PositivityKind interpretation

PositivityKindInterpretation : (nl : NumberKind) → PositivityKindType nl → (x : NumberKindInterpretation nl) → Type (NumberKindProplevel nl)
PositivityKindInterpretation isNat     ⁇x⁇ x =               Unit
PositivityKindInterpretation isNat     x#0 x = let open ℕ in  x # 0f
PositivityKindInterpretation isNat     0≤x x = let open ℕ in 0f ≤  x
PositivityKindInterpretation isNat     0<x x = let open ℕ in 0f <  x
PositivityKindInterpretation isNat     x≤0 x = let open ℕ in  x ≤ 0f
PositivityKindInterpretation isNat     x<0 x =               ⊥
PositivityKindInterpretation isInt     ⁇x⁇ x =               Lift Unit
PositivityKindInterpretation isInt     x#0 x = let open ℤ in  x # 0f
PositivityKindInterpretation isInt     0≤x x = let open ℤ in 0f ≤  x
PositivityKindInterpretation isInt     0<x x = let open ℤ in 0f <  x
PositivityKindInterpretation isInt     x≤0 x = let open ℤ in  x ≤ 0f
PositivityKindInterpretation isInt     x<0 x = let open ℤ in  x < 0f
PositivityKindInterpretation isRat     ⁇x⁇ x =               Lift Unit
PositivityKindInterpretation isRat     x#0 x = let open ℚ in  x # 0f
PositivityKindInterpretation isRat     0≤x x = let open ℚ in 0f ≤  x
PositivityKindInterpretation isRat     0<x x = let open ℚ in 0f <  x
PositivityKindInterpretation isRat     x≤0 x = let open ℚ in  x ≤ 0f
PositivityKindInterpretation isRat     x<0 x = let open ℚ in  x < 0f
PositivityKindInterpretation isReal    ⁇x⁇ x =               Lift Unit
PositivityKindInterpretation isReal    x#0 x = let open ℝ in  x # 0f
PositivityKindInterpretation isReal    0≤x x = let open ℝ in 0f ≤  x
PositivityKindInterpretation isReal    0<x x = let open ℝ in 0f <  x
PositivityKindInterpretation isReal    x≤0 x = let open ℝ in  x ≤ 0f
PositivityKindInterpretation isReal    x<0 x = let open ℝ in  x < 0f
PositivityKindInterpretation isComplex ⁇x⁇ x =               Lift Unit
PositivityKindInterpretation isComplex x#0 x = let open ℂ in  x # 0f

NumberLevel : NumberKind → Level
NumberLevel l = ℓ-max (NumberKindLevel l) (NumberKindProplevel l)

-- NumberProp interpretation
NumberInterpretation : ((l , p) : NumberProp) → Type (NumberLevel l)
NumberInterpretation (level , positivity) = Σ (NumberKindInterpretation level) (PositivityKindInterpretation level positivity)

-- generic number type
data Number (p : NumberProp) : Type (NumberLevel (fst p)) where
  _,,_ : (x :  NumberKindInterpretation (fst p))
       → (PositivityKindInterpretation (fst p) (snd p) x)
       → Number p

num : ∀{(l , p) : NumberProp} → Number (l , p) → NumberKindInterpretation l
num (p ,, q) = p

prp : ∀{pp@(l , p) : NumberProp} → (x : Number pp) → PositivityKindInterpretation l p (num x)
prp (p ,, q) = q

pop : ∀{p : NumberProp} → Number p → NumberInterpretation p
pop (x ,, p) = x , p

open PatternsType


{- NOTE: overlapping patterns makes this possible:

_ : NumberProp'
_ = isRat , X⁺⁻

_ : NumberProp'
_ = isComplex , X⁺⁻

-}
