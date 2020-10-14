{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Prettyprint where

open import Cubical.Data.Sigma.Base
open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Base

[ℕ]   = Number (isNat     , anyPositivityᵒʳ)
[ℕ⁺⁻] = Number (isNat     , isNonzeroᵒʳ    )
[ℕ₀⁺] = Number (isNat     , isNonnegativeᵒʳ)
[ℕ⁺]  = Number (isNat     , isPositiveᵒʳ   )
[ℕ₀⁻] = Number (isNat     , isNonpositiveᵒʳ)
[ℤ]   = Number (isInt     , anyPositivityᵒʳ)
[ℤ⁺⁻] = Number (isInt     , isNonzeroᵒʳ    )
[ℤ₀⁺] = Number (isInt     , isNonnegativeᵒʳ)
[ℤ⁺]  = Number (isInt     , isPositiveᵒʳ   )
[ℤ⁻]  = Number (isInt     , isNegativeᵒʳ   )
[ℤ₀⁻] = Number (isInt     , isNonpositiveᵒʳ)
[ℚ]   = Number (isRat     , anyPositivityᵒʳ)
[ℚ⁺⁻] = Number (isRat     , isNonzeroᵒʳ    )
[ℚ₀⁺] = Number (isRat     , isNonnegativeᵒʳ)
[ℚ⁺]  = Number (isRat     , isPositiveᵒʳ   )
[ℚ⁻]  = Number (isRat     , isNegativeᵒʳ   )
[ℚ₀⁻] = Number (isRat     , isNonpositiveᵒʳ)
[ℝ]   = Number (isReal    , anyPositivityᵒʳ)
[ℝ⁺⁻] = Number (isReal    , isNonzeroᵒʳ    )
[ℝ₀⁺] = Number (isReal    , isNonnegativeᵒʳ)
[ℝ⁺]  = Number (isReal    , isPositiveᵒʳ   )
[ℝ⁻]  = Number (isReal    , isNegativeᵒʳ   )
[ℝ₀⁻] = Number (isReal    , isNonpositiveᵒʳ)
[ℂ]   = Number (isComplex , anyPositivityᶠ )
[ℂ⁺⁻] = Number (isComplex , isNonzeroᶠ     )

{-# DISPLAY Number (isNat     , anyPositivityᵒʳ) = [ℕ]   #-}
{-# DISPLAY Number (isNat     , isNonzeroᵒʳ    ) = [ℕ⁺⁻] #-}
{-# DISPLAY Number (isNat     , isNonnegativeᵒʳ) = [ℕ₀⁺] #-}
{-# DISPLAY Number (isNat     , isPositiveᵒʳ   ) = [ℕ⁺]  #-}
{-# DISPLAY Number (isNat     , isNonpositiveᵒʳ) = [ℕ₀⁻] #-}
{-# DISPLAY Number (isInt     , anyPositivityᵒʳ) = [ℤ]   #-}
{-# DISPLAY Number (isInt     , isNonzeroᵒʳ    ) = [ℤ⁺⁻] #-}
{-# DISPLAY Number (isInt     , isNonnegativeᵒʳ) = [ℤ₀⁺] #-}
{-# DISPLAY Number (isInt     , isPositiveᵒʳ   ) = [ℤ⁺]  #-}
{-# DISPLAY Number (isInt     , isNegativeᵒʳ   ) = [ℤ⁻]  #-}
{-# DISPLAY Number (isInt     , isNonpositiveᵒʳ) = [ℤ₀⁻] #-}
{-# DISPLAY Number (isRat     , anyPositivityᵒʳ) = [ℚ]   #-}
{-# DISPLAY Number (isRat     , isNonzeroᵒʳ    ) = [ℚ⁺⁻] #-}
{-# DISPLAY Number (isRat     , isNonnegativeᵒʳ) = [ℚ₀⁺] #-}
{-# DISPLAY Number (isRat     , isPositiveᵒʳ   ) = [ℚ⁺]  #-}
{-# DISPLAY Number (isRat     , isNegativeᵒʳ   ) = [ℚ⁻]  #-}
{-# DISPLAY Number (isRat     , isNonpositiveᵒʳ) = [ℚ₀⁻] #-}
{-# DISPLAY Number (isReal    , anyPositivityᵒʳ) = [ℝ]   #-}
{-# DISPLAY Number (isReal    , isNonzeroᵒʳ    ) = [ℝ⁺⁻] #-}
{-# DISPLAY Number (isReal    , isNonnegativeᵒʳ) = [ℝ₀⁺] #-}
{-# DISPLAY Number (isReal    , isPositiveᵒʳ   ) = [ℝ⁺]  #-}
{-# DISPLAY Number (isReal    , isNegativeᵒʳ   ) = [ℝ⁻]  #-}
{-# DISPLAY Number (isReal    , isNonpositiveᵒʳ) = [ℝ₀⁻] #-}
{-# DISPLAY Number (isComplex , anyPositivityᶠ ) = [ℂ]   #-}
{-# DISPLAY Number (isComplex , isNonzeroᶠ     ) = [ℂ⁺⁻] #-}
