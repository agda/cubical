{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Operations.Specification where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Unit.Base -- Unit

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Base

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

open PatternsType

-- workflow:
-- 1. split on the both positivities at once
-- 2. add a general clause on top
-- 3. check file
-- 4. remove all unreachable clauses and goto 2.
-- feel free to remove too many clauses and let agda display the missing ones
+-Positivityᵒʳ : PositivityKindOrderedRing → PositivityKindOrderedRing → PositivityKindOrderedRing
+-Positivityᵒʳ _   X   = X
+-Positivityᵒʳ X   _   = X
+-Positivityᵒʳ _   X⁺⁻ = X
+-Positivityᵒʳ X⁺⁻ _   = X
-- clauses with same sign
+-Positivityᵒʳ X₀⁺ X₀⁺ = X₀⁺
+-Positivityᵒʳ X₀⁻ X₀⁻ = X₀⁻
+-Positivityᵒʳ X₀⁺ X⁺  = X⁺
+-Positivityᵒʳ X⁺  X₀⁺ = X⁺
+-Positivityᵒʳ X⁺  X⁺  = X⁺
+-Positivityᵒʳ X₀⁻ X⁻  = X⁻
+-Positivityᵒʳ X⁻  X⁻  = X⁻
+-Positivityᵒʳ X⁻  X₀⁻ = X⁻
-- remaining clauses with alternating sign
+-Positivityᵒʳ X₀⁻ X₀⁺ = X
+-Positivityᵒʳ X₀⁺ X₀⁻ = X
+-Positivityᵒʳ X⁻  X₀⁺ = X
+-Positivityᵒʳ X₀⁺ X⁻  = X
+-Positivityᵒʳ X⁻  X⁺  = X
+-Positivityᵒʳ X⁺  X⁻  = X
+-Positivityᵒʳ X₀⁻ X⁺  = X
+-Positivityᵒʳ X⁺  X₀⁻ = X

+-Positivityᶠ : PositivityKindField → PositivityKindField → PositivityKindField
-- positivity information is lost after _+_ on a field
+-Positivityᶠ x   y   = X

+-Positivityʰ : (l : NumberKind) → PositivityKindType l → PositivityKindType l → PositivityKindType l
+-Positivityʰ isNat     = +-Positivityᵒʳ
+-Positivityʰ isInt     = +-Positivityᵒʳ
+-Positivityʰ isRat     = +-Positivityᵒʳ
+-Positivityʰ isReal    = +-Positivityᵒʳ
+-Positivityʰ isComplex = +-Positivityᶠ

·-Positivityᵒʳ : PositivityKindOrderedRing → PositivityKindOrderedRing → PositivityKindOrderedRing
·-Positivityᵒʳ _   X   = X
·-Positivityᵒʳ X   _   = X
·-Positivityᵒʳ X₀⁺ X⁺⁻ = X
·-Positivityᵒʳ X⁺⁻ X₀⁺ = X
·-Positivityᵒʳ X₀⁻ X⁺⁻ = X
·-Positivityᵒʳ X⁺⁻ X₀⁻ = X
-- multiplying nonzero numbers gives a nonzero number
·-Positivityᵒʳ X⁺⁻ X⁺⁻ = X⁺⁻
·-Positivityᵒʳ X⁺  X⁺⁻ = X⁺⁻
·-Positivityᵒʳ X⁺⁻ X⁺  = X⁺⁻
·-Positivityᵒʳ X⁻  X⁺⁻ = X⁺⁻
·-Positivityᵒʳ X⁺⁻ X⁻  = X⁺⁻
-- multiplying positive numbers gives a positive number
·-Positivityᵒʳ X₀⁺ X₀⁺ = X₀⁺
·-Positivityᵒʳ X₀⁺ X⁺  = X₀⁺
·-Positivityᵒʳ X⁺  X₀⁺ = X₀⁺
·-Positivityᵒʳ X⁺  X⁺  = X⁺
-- multiplying negative numbers gives a positive number
·-Positivityᵒʳ X₀⁻ X⁻  = X₀⁺
·-Positivityᵒʳ X⁻  X₀⁻ = X₀⁺
·-Positivityᵒʳ X₀⁻ X₀⁻ = X₀⁺
·-Positivityᵒʳ X⁻  X⁻  = X⁺
-- multiplying a positive and a negative number gives a negative number
·-Positivityᵒʳ X⁻  X₀⁺ = X₀⁻
·-Positivityᵒʳ X₀⁺ X⁻  = X₀⁻
·-Positivityᵒʳ X₀⁻ X⁺  = X₀⁻
·-Positivityᵒʳ X⁺  X₀⁻ = X₀⁻
·-Positivityᵒʳ X₀⁻ X₀⁺ = X₀⁻
·-Positivityᵒʳ X₀⁺ X₀⁻ = X₀⁻
·-Positivityᵒʳ X⁻  X⁺  = X⁻
·-Positivityᵒʳ X⁺  X⁻  = X⁻

·-Positivityᶠ : PositivityKindField → PositivityKindField → PositivityKindField
·-Positivityᶠ X   X   = X
·-Positivityᶠ X   X⁺⁻ = X
·-Positivityᶠ X⁺⁻ X   = X
-- multiplying nonzero numbers gives a nonzero number
·-Positivityᶠ X⁺⁻ X⁺⁻ = X⁺⁻

·-Positivityʰ : (l : NumberKind) → PositivityKindType l → PositivityKindType l → PositivityKindType l
·-Positivityʰ isNat     = ·-Positivityᵒʳ
·-Positivityʰ isInt     = ·-Positivityᵒʳ
·-Positivityʰ isRat     = ·-Positivityᵒʳ
·-Positivityʰ isReal    = ·-Positivityᵒʳ
·-Positivityʰ isComplex = ·-Positivityᶠ

min-Positivityᵒʳ : PositivityKindOrderedRing → PositivityKindOrderedRing → PositivityKindOrderedRing
min-Positivityᵒʳ X   X   = X
min-Positivityᵒʳ X   X⁺⁻ = X
min-Positivityᵒʳ X   X₀⁺ = X
min-Positivityᵒʳ X   X⁺  = X
min-Positivityᵒʳ X   X⁻  = X⁻
min-Positivityᵒʳ X   X₀⁻ = X₀⁻
min-Positivityᵒʳ X⁺⁻ X   = X
min-Positivityᵒʳ X⁺⁻ X⁺⁻ = X⁺⁻
min-Positivityᵒʳ X⁺⁻ X₀⁺ = X
min-Positivityᵒʳ X⁺⁻ X⁺  = X⁺⁻
min-Positivityᵒʳ X⁺⁻ X⁻  = X⁻
min-Positivityᵒʳ X⁺⁻ X₀⁻ = X₀⁻
min-Positivityᵒʳ X₀⁺ X   = X
min-Positivityᵒʳ X₀⁺ X⁺⁻ = X
min-Positivityᵒʳ X₀⁺ X₀⁺ = X₀⁺
min-Positivityᵒʳ X₀⁺ X⁺  = X₀⁺
min-Positivityᵒʳ X₀⁺ X⁻  = X⁻
min-Positivityᵒʳ X₀⁺ X₀⁻ = X₀⁻
min-Positivityᵒʳ X⁺  X   = X
min-Positivityᵒʳ X⁺  X⁺⁻ = X⁺⁻
min-Positivityᵒʳ X⁺  X₀⁺ = X₀⁺
min-Positivityᵒʳ X⁺  X⁺  = X⁺
min-Positivityᵒʳ X⁺  X⁻  = X⁻
min-Positivityᵒʳ X⁺  X₀⁻ = X₀⁻
min-Positivityᵒʳ X⁻  X   = X⁻
min-Positivityᵒʳ X⁻  X⁺⁻ = X⁻
min-Positivityᵒʳ X⁻  X₀⁺ = X⁻
min-Positivityᵒʳ X⁻  X⁺  = X⁻
min-Positivityᵒʳ X⁻  X⁻  = X⁻
min-Positivityᵒʳ X⁻  X₀⁻ = X⁻
min-Positivityᵒʳ X₀⁻ X   = X₀⁻
min-Positivityᵒʳ X₀⁻ X⁺⁻ = X₀⁻
min-Positivityᵒʳ X₀⁻ X₀⁺ = X₀⁻
min-Positivityᵒʳ X₀⁻ X⁺  = X₀⁻
min-Positivityᵒʳ X₀⁻ X⁻  = X⁻
min-Positivityᵒʳ X₀⁻ X₀⁻ = X₀⁻

max-Positivityᵒʳ : PositivityKindOrderedRing → PositivityKindOrderedRing → PositivityKindOrderedRing
max-Positivityᵒʳ X   X   = X
max-Positivityᵒʳ X   X⁺⁻ = X
max-Positivityᵒʳ X   X₀⁺ = X₀⁺
max-Positivityᵒʳ X   X⁺  = X⁺
max-Positivityᵒʳ X   X⁻  = X
max-Positivityᵒʳ X   X₀⁻ = X
max-Positivityᵒʳ X⁺⁻ X   = X
max-Positivityᵒʳ X⁺⁻ X⁺⁻ = X⁺⁻
max-Positivityᵒʳ X⁺⁻ X₀⁺ = X₀⁺
max-Positivityᵒʳ X⁺⁻ X⁺  = X⁺
max-Positivityᵒʳ X⁺⁻ X⁻  = X⁺⁻
max-Positivityᵒʳ X⁺⁻ X₀⁻ = X
max-Positivityᵒʳ X₀⁺ X   = X₀⁺
max-Positivityᵒʳ X₀⁺ X⁺⁻ = X₀⁺
max-Positivityᵒʳ X₀⁺ X₀⁺ = X₀⁺
max-Positivityᵒʳ X₀⁺ X⁺  = X⁺
max-Positivityᵒʳ X₀⁺ X⁻  = X₀⁺
max-Positivityᵒʳ X₀⁺ X₀⁻ = X₀⁺
max-Positivityᵒʳ X⁺  X   = X⁺
max-Positivityᵒʳ X⁺  X⁺⁻ = X⁺
max-Positivityᵒʳ X⁺  X₀⁺ = X⁺
max-Positivityᵒʳ X⁺  X⁺  = X⁺
max-Positivityᵒʳ X⁺  X⁻  = X⁺
max-Positivityᵒʳ X⁺  X₀⁻ = X⁺
max-Positivityᵒʳ X⁻  X   = X
max-Positivityᵒʳ X⁻  X⁺⁻ = X⁺⁻
max-Positivityᵒʳ X⁻  X₀⁺ = X₀⁺
max-Positivityᵒʳ X⁻  X⁺  = X⁺
max-Positivityᵒʳ X⁻  X⁻  = X⁻
max-Positivityᵒʳ X⁻  X₀⁻ = X₀⁻
max-Positivityᵒʳ X₀⁻ X   = X
max-Positivityᵒʳ X₀⁻ X⁺⁻ = X
max-Positivityᵒʳ X₀⁻ X₀⁺ = X₀⁺
max-Positivityᵒʳ X₀⁻ X⁺  = X⁺
max-Positivityᵒʳ X₀⁻ X⁻  = X₀⁻
max-Positivityᵒʳ X₀⁻ X₀⁻ = X₀⁻

min-Positivityʰ : (l : NumberKind) → PositivityKindType l → PositivityKindType l → PositivityKindType l
min-Positivityʰ isNat     = min-Positivityᵒʳ
min-Positivityʰ isInt     = min-Positivityᵒʳ
min-Positivityʰ isRat     = min-Positivityᵒʳ
min-Positivityʰ isReal    = min-Positivityᵒʳ
min-Positivityʰ isComplex = λ _ _ → X -- doesn't matter since `min` is undefined for ℂ

max-Positivityʰ : (l : NumberKind) → PositivityKindType l → PositivityKindType l → PositivityKindType l
max-Positivityʰ isNat     = max-Positivityᵒʳ
max-Positivityʰ isInt     = max-Positivityᵒʳ
max-Positivityʰ isRat     = max-Positivityᵒʳ
max-Positivityʰ isReal    = max-Positivityᵒʳ
max-Positivityʰ isComplex = λ _ _ → X -- doesn't matter since `max` is undefined for ℂ

+-Types : NumberProp → NumberProp → NumberProp
+-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , +-Positivityʰ level (coerce-PositivityKind level₀ level pos₀) (coerce-PositivityKind level₁ level pos₁)

·-Types : NumberProp → NumberProp → NumberProp
·-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , ·-Positivityʰ level (coerce-PositivityKind level₀ level pos₀) (coerce-PositivityKind level₁ level pos₁)

⁻¹-Types : ∀{l p} → Number (l , p) → Type (ℓ-max (NumberLevel (maxₙₗ l isRat)) (NumberKindProplevel l))
-- numbers that can be zero need an additional apartness proof
⁻¹-Types {isNat    } {X  } (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isInt    } {X  } (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isRat    } {X  } (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isReal   } {X  } (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺⁻)
⁻¹-Types {isComplex} {X  } (x ,, p) = ∀{{ q : x #ᶜ 0ᶜ }} → Number (isComplex , X⁺⁻)
⁻¹-Types {isNat    } {X₀⁺} (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X₀⁺} (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁺ )
⁻¹-Types {isRat    } {X₀⁺} (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺ )
⁻¹-Types {isReal   } {X₀⁺} (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺ )
⁻¹-Types {isNat    } {X₀⁻} (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁻ )
⁻¹-Types {isInt    } {X₀⁻} (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁻ )
⁻¹-Types {isRat    } {X₀⁻} (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁻ )
⁻¹-Types {isReal   } {X₀⁻} (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁻ )
-- positive, negative and nonzero numbers are already apart from zero
⁻¹-Types {isNat    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isNat    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isNat    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isNat    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isInt    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁻ )
⁻¹-Types {isRat    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isRat    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isRat    } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁻ )
⁻¹-Types {isReal   } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁺⁻)
⁻¹-Types {isReal   } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁺ )
⁻¹-Types {isReal   } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁻ )
⁻¹-Types {isComplex} {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isComplex} Unit }} → Number (isComplex , X⁺⁻)

-Types : ∀{l p} → Number (l , p) → Type (NumberLevel (maxₙₗ l isInt))
-Types {isInt    } {X  } (x ,, p) = Number (isInt     , X)
-Types {isRat    } {X  } (x ,, p) = Number (isRat     , X)
-Types {isReal   } {X  } (x ,, p) = Number (isReal    , X)
-Types {isComplex} {X  } (x ,, p) = Number (isComplex , X)
-- the negative of a natural number is a Nonpositive integer
-Types {isNat    } {X  } (x ,, p) = Number (isInt     , X₀⁻)
-- the negative of a nonzero number is a nonzero number
-Types {isNat    } {X⁺⁻} (x ,, p) = Number (isInt     , X⁺⁻)
-Types {isInt    } {X⁺⁻} (x ,, p) = Number (isInt     , X⁺⁻)
-Types {isRat    } {X⁺⁻} (x ,, p) = Number (isRat     , X⁺⁻)
-Types {isReal   } {X⁺⁻} (x ,, p) = Number (isReal    , X⁺⁻)
-Types {isComplex} {X⁺⁻} (x ,, p) = Number (isComplex , X⁺⁻)
-- the negative of a positive number is a negative number
-Types {isNat    } {X₀⁺} (x ,, p) = Number (isInt     , X₀⁻)
-Types {isInt    } {X₀⁺} (x ,, p) = Number (isInt     , X₀⁻)
-Types {isRat    } {X₀⁺} (x ,, p) = Number (isRat     , X₀⁻)
-Types {isReal   } {X₀⁺} (x ,, p) = Number (isReal    , X₀⁻)
-Types {isNat    } {X⁺ } (x ,, p) = Number (isInt     , X⁻ )
-Types {isInt    } {X⁺ } (x ,, p) = Number (isInt     , X⁻ )
-Types {isRat    } {X⁺ } (x ,, p) = Number (isRat     , X⁻ )
-Types {isReal   } {X⁺ } (x ,, p) = Number (isReal    , X⁻ )
-- the negative of a negative number is a positive number
-Types {isNat    } {X₀⁻} (x ,, p) = Number (isInt     , X₀⁺)
-Types {isInt    } {X₀⁻} (x ,, p) = Number (isInt     , X₀⁺)
-Types {isRat    } {X₀⁻} (x ,, p) = Number (isRat     , X₀⁺)
-Types {isReal   } {X₀⁻} (x ,, p) = Number (isReal    , X₀⁺)
-Types {isInt    } {X⁻ } (x ,, p) = Number (isInt     , X⁺ )
-Types {isRat    } {X⁻ } (x ,, p) = Number (isRat     , X⁺ )
-Types {isReal   } {X⁻ } (x ,, p) = Number (isReal    , X⁺ )

abs-Types : ∀{l p} → Number (l , p) → Type (NumberLevel (minₙₗ l isReal))
abs-Types {isNat    } {X  } (x ,, p) = Number (isNat  , X₀⁺)
abs-Types {isNat    } {X⁺⁻} (x ,, p) = Number (isNat  , X⁺ )
abs-Types {isNat    } {X₀⁺} (x ,, p) = Number (isNat  , X₀⁺)
abs-Types {isNat    } {X⁺ } (x ,, p) = Number (isNat  , X⁺ )
abs-Types {isNat    } {X₀⁻} (x ,, p) = Number (isNat  , X₀⁺)
abs-Types {isInt    } {X  } (x ,, p) = Number (isInt  , X₀⁺)
abs-Types {isInt    } {X⁺⁻} (x ,, p) = Number (isInt  , X⁺ )
abs-Types {isInt    } {X₀⁺} (x ,, p) = Number (isInt  , X₀⁺)
abs-Types {isInt    } {X⁺ } (x ,, p) = Number (isInt  , X⁺ )
abs-Types {isInt    } {X⁻ } (x ,, p) = Number (isInt  , X⁺ )
abs-Types {isInt    } {X₀⁻} (x ,, p) = Number (isInt  , X₀⁺)
abs-Types {isRat    } {X  } (x ,, p) = Number (isRat  , X₀⁺)
abs-Types {isRat    } {X⁺⁻} (x ,, p) = Number (isRat  , X⁺ )
abs-Types {isRat    } {X₀⁺} (x ,, p) = Number (isRat  , X₀⁺)
abs-Types {isRat    } {X⁺ } (x ,, p) = Number (isRat  , X⁺ )
abs-Types {isRat    } {X⁻ } (x ,, p) = Number (isRat  , X⁺ )
abs-Types {isRat    } {X₀⁻} (x ,, p) = Number (isRat  , X₀⁺)
abs-Types {isReal   } {X  } (x ,, p) = Number (isReal , X₀⁺)
abs-Types {isReal   } {X⁺⁻} (x ,, p) = Number (isReal , X⁺ )
abs-Types {isReal   } {X₀⁺} (x ,, p) = Number (isReal , X₀⁺)
abs-Types {isReal   } {X⁺ } (x ,, p) = Number (isReal , X⁺ )
abs-Types {isReal   } {X⁻ } (x ,, p) = Number (isReal , X⁺ )
abs-Types {isReal   } {X₀⁻} (x ,, p) = Number (isReal , X₀⁺)
abs-Types {isComplex} {X  } (x ,, p) = Number (isReal , X₀⁺)
abs-Types {isComplex} {X⁺⁻} (x ,, p) = Number (isReal , X⁺ )
