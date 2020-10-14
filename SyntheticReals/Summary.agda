{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Summary where

import Cubical.Data.Nat using (ℕ)
open import Cubical.Foundations.Prelude using (Lift; refl)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.Data.Sigma.Base

infix 1 _≅_
_≅_ = Iso

open import Number.Postulates
open import Number.Base
open import Number.Prettyprint

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

number-≅-Σ : ∀{p} → Number p ≅ NumberInterpretation p
number-≅-Σ = λ where
  .Iso.fun               → pop
  .Iso.inv      (x ,  p) → x ,, p
  .Iso.leftInv  (x ,, p) → refl
  .Iso.rightInv (x ,  p) → refl

iso00 : [ℕ]   ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] Unit
iso01 : [ℕ⁺⁻] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] x  #ⁿ 0ⁿ
iso02 : [ℕ₀⁺] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] 0ⁿ ≤ⁿ x
iso03 : [ℕ⁺]  ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] 0ⁿ <ⁿ x
iso04 : [ℕ₀⁻] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] x  ≤ⁿ 0ⁿ
iso05 : [ℤ]   ≅ Σ[ x ∈ ℤ.Carrier          ] Lift {j = ℤℓ'} Unit
iso06 : [ℤ⁺⁻] ≅ Σ[ x ∈ ℤ.Carrier          ] x  #ᶻ 0ᶻ
iso07 : [ℤ₀⁺] ≅ Σ[ x ∈ ℤ.Carrier          ] 0ᶻ ≤ᶻ x
iso08 : [ℤ⁺]  ≅ Σ[ x ∈ ℤ.Carrier          ] 0ᶻ <ᶻ x
iso09 : [ℤ⁻]  ≅ Σ[ x ∈ ℤ.Carrier          ] x  <ᶻ 0ᶻ
iso10 : [ℤ₀⁻] ≅ Σ[ x ∈ ℤ.Carrier          ] x  ≤ᶻ 0ᶻ
iso11 : [ℚ]   ≅ Σ[ x ∈ ℚ.Carrier          ] Lift {j = ℚℓ'} Unit
iso12 : [ℚ⁺⁻] ≅ Σ[ x ∈ ℚ.Carrier          ] x  #ᶠ 0ᶠ
iso13 : [ℚ₀⁺] ≅ Σ[ x ∈ ℚ.Carrier          ] 0ᶠ ≤ᶠ x
iso14 : [ℚ⁺]  ≅ Σ[ x ∈ ℚ.Carrier          ] 0ᶠ <ᶠ x
iso15 : [ℚ⁻]  ≅ Σ[ x ∈ ℚ.Carrier          ] x  <ᶠ 0ᶠ
iso16 : [ℚ₀⁻] ≅ Σ[ x ∈ ℚ.Carrier          ] x  ≤ᶠ 0ᶠ
iso17 : [ℝ]   ≅ Σ[ x ∈ ℝ.Carrier          ] Lift {j = ℝℓ'} Unit
iso18 : [ℝ⁺⁻] ≅ Σ[ x ∈ ℝ.Carrier          ] x  #ʳ 0ʳ
iso19 : [ℝ₀⁺] ≅ Σ[ x ∈ ℝ.Carrier          ] 0ʳ ≤ʳ x
iso20 : [ℝ⁺]  ≅ Σ[ x ∈ ℝ.Carrier          ] 0ʳ <ʳ x
iso21 : [ℝ⁻]  ≅ Σ[ x ∈ ℝ.Carrier          ] x  <ʳ 0ʳ
iso22 : [ℝ₀⁻] ≅ Σ[ x ∈ ℝ.Carrier          ] x  ≤ʳ 0ʳ
iso23 : [ℂ]   ≅ Σ[ x ∈ ℂ.Carrier          ] Lift {j = ℂℓ'} Unit
iso24 : [ℂ⁺⁻] ≅ Σ[ x ∈ ℂ.Carrier          ] x  #ᶜ 0ᶜ

iso00 = number-≅-Σ
iso01 = number-≅-Σ
iso02 = number-≅-Σ
iso03 = number-≅-Σ
iso04 = number-≅-Σ
iso05 = number-≅-Σ
iso06 = number-≅-Σ
iso07 = number-≅-Σ
iso08 = number-≅-Σ
iso09 = number-≅-Σ
iso10 = number-≅-Σ
iso11 = number-≅-Σ
iso12 = number-≅-Σ
iso13 = number-≅-Σ
iso14 = number-≅-Σ
iso15 = number-≅-Σ
iso16 = number-≅-Σ
iso17 = number-≅-Σ
iso18 = number-≅-Σ
iso19 = number-≅-Σ
iso20 = number-≅-Σ
iso21 = number-≅-Σ
iso22 = number-≅-Σ
iso23 = number-≅-Σ
iso24 = number-≅-Σ
