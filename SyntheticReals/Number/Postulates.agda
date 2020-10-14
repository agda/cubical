{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.Number.Postulates where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Function.Base using (_∋_)

ℕℓ  = ℓ-zero
ℕℓ' = ℓ-zero

postulate
  ℤℓ ℤℓ' : Level
  ℚℓ ℚℓ' : Level
  ℝℓ ℝℓ' : Level
  ℂℓ ℂℓ' : Level

open import SyntheticReals.Number.Structures
open import SyntheticReals.Number.Bundles
import SyntheticReals.Number.Inclusions

import SyntheticReals.MoreAlgebra

module ℕ* where
  import Cubical.Data.Nat as Nat
  import Cubical.Data.Nat.Order as Order

  open import Agda.Builtin.Nat using () renaming (Nat to ℕ) public

  module Postulates where
    postulate
      min max : ℕ → ℕ → ℕ
      isROrderedCommSemiring : IsROrderedCommSemiring
        (Order._<_)
        (Order._≤_)
        ((SyntheticReals.MoreAlgebra.Definitions._#'_ {_<_ = Order._<_}))
        (min)
        (max)
        (Nat.zero)
        (1)
        (Nat._+_)
        (Nat._*_)

  module Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}
  Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}

  Carrier = ℕ

  bundle : Bundle
  bundle = (record
    { Carrier = ℕ
    ; _<_ = Order._<_
    ; _≤_ = Order._≤_
    ; _#_ = (SyntheticReals.MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Postulates.min
    ; max = Postulates.max
    ; 0f  = Nat.zero
    ; 1f  = (Nat.suc Nat.zero)
    ; _+_ = Nat._+_
    ; _·_ = Nat._*_
    ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
    })

  open import Cubical.Data.Nat.Order using (_≤_; _<_) public
  import SyntheticReals.MoreAlgebra
  open SyntheticReals.MoreAlgebra.Definitions using (_#'_) public
  open import Agda.Builtin.Nat using () renaming (zero to 0f)  public

  -- _<_ = Bundle._<_ bundle
  -- _≤_ = Bundle._≤_ bundle
  _#_ = Bundle._#_ bundle
  min = Bundle.min bundle
  max = Bundle.max bundle
  -- 0f  = Bundle.0f  bundle
  1f  = Bundle.1f  bundle
  _+_ = Bundle._+_ bundle
  _·_ = Bundle._·_ bundle
  isROrderedCommSemiring = Bundle.isROrderedCommSemiring bundle

  abs : ℕ → ℕ
  abs x = x

  open IsROrderedCommSemiring isROrderedCommSemiring public

module ℕ  = ℕ* hiding (ℕ)
module ℕⁿ = ℕ*
    renaming
    ( Carrier to Carrierⁿ
    ; _<_ to _<ⁿ_
    ; _≤_ to _≤ⁿ_
    ; _#_ to _#ⁿ_
    ; min to minⁿ
    ; max to maxⁿ
    ; 0f  to 0ⁿ
    ; 1f  to 1ⁿ
    ; _+_ to _+ⁿ_
    ; _·_ to _·ⁿ_
    ; isROrderedCommSemiring to isROrderedCommSemiringⁿ
    ; abs to absⁿ
    )

module ℤ* where
  module Postulates where
    postulate
      ℤ           : Type ℤℓ
      _<_ _≤_ _#_ : Rel ℤ ℤ ℤℓ'
      min max     : ℤ → ℤ → ℤ
      0f 1f       : ℤ
      _+_ _·_     : ℤ → ℤ → ℤ
      -_          : ℤ → ℤ

    abs : ℤ → ℤ
    abs x = max x (- x)

    postulate
      isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
      isAbsOrderedCommRing : IsAbsOrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ abs

  module Bundle = ROrderedCommRing {ℤℓ} {ℤℓ'}
  Bundle = ROrderedCommRing {ℤℓ} {ℤℓ'}

  open Postulates public

  Carrier = ℤ

  bundle : Bundle
  bundle = (record
    { Carrier = ℤ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f
    ; 1f  = 1f
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; isROrderedCommRing = isROrderedCommRing
    ; isAbsOrderedCommRing = isAbsOrderedCommRing
    })

  open IsROrderedCommRing isROrderedCommRing public

  -- abs : ℤ → ℤ
  -- abs x = max x (- x)

module ℤ  = ℤ* hiding (ℤ)
module ℤᶻ = ℤ*
    renaming
    ( Carrier to Carrierᶻ
    ; _<_ to _<ᶻ_
    ; _≤_ to _≤ᶻ_
    ; _#_ to _#ᶻ_
    ; min to minᶻ
    ; max to maxᶻ
    ; 0f  to 0ᶻ
    ; 1f  to 1ᶻ
    ; _+_ to _+ᶻ_
    ; _·_ to _·ᶻ_
    ; -_  to -ᶻ_
    ; isROrderedCommRing to isROrderedCommRingᶻ
    ; abs to absᶻ
    )

module ℚ* where
  module Postulates where
    postulate
      ℚ           : Type ℚℓ
      _<_ _≤_ _#_ : Rel ℚ ℚ ℚℓ'
      min max     : ℚ → ℚ → ℚ
      0f 1f       : ℚ
      _+_ _·_     : ℚ → ℚ → ℚ
      -_          : ℚ → ℚ
      _⁻¹         : (x : ℚ) → {{ x # 0f }} → ℚ

    abs : ℚ → ℚ
    abs x = max x (- x)

    postulate
      isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹
      isAbsOrderedCommRing : IsAbsOrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ abs

  module Bundle = ROrderedField {ℚℓ} {ℚℓ'}
  Bundle = ROrderedField {ℚℓ} {ℚℓ'}

  open Postulates public

  Carrier = ℚ

  bundle : Bundle
  bundle = (record
    { Carrier = ℚ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f
    ; 1f  = 1f
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; _⁻¹ = _⁻¹
    ; isROrderedField = isROrderedField
    ; isAbsOrderedCommRing = isAbsOrderedCommRing
    })

  -- abs : ℚ → ℚ
  -- abs x = max x (- x)

  open IsROrderedField isROrderedField public

module ℚ  = ℚ* hiding (ℚ)
module ℚᶠ = ℚ*
  renaming
  ( Carrier to Carrierᶠ
  ; _<_ to _<ᶠ_
  ; _≤_ to _≤ᶠ_
  ; _#_ to _#ᶠ_
  ; min to minᶠ
  ; max to maxᶠ
  ; 0f  to 0ᶠ
  ; 1f  to 1ᶠ
  ; _+_ to _+ᶠ_
  ; _·_ to _·ᶠ_
  ; -_  to -ᶠ_
  ; _⁻¹ to _⁻¹ᶠ
  ; isROrderedField to isROrderedFieldᶠ
  ; abs to absᶠ
  )

module ℝ* where
  private
    module Postulates where
      postulate
        ℝ           : Type ℝℓ
        _<_ _≤_ _#_ : Rel ℝ ℝ ℝℓ'
        min max     : ℝ → ℝ → ℝ
        0f 1f       : ℝ
        _+_ _·_     : ℝ → ℝ → ℝ
        -_          : ℝ → ℝ
        _⁻¹         : (x : ℝ) → {{ x # 0f }} → ℝ

      abs : ℝ → ℝ
      abs x = max x (- x)

      postulate
        isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹
        isAbsOrderedCommRing : IsAbsOrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ abs

        -- square root on ℝ₀⁺
        sqrt : (x : ℝ) → {{0f ≤ x}} → ℝ
        0≤sqrt : ∀ x → {{p : 0f ≤ x}} → 0f ≤ sqrt x {{p}}
        sqrt-reflects-≡ : ∀ x y → {{px : 0f ≤ x}} → {{py : 0f ≤ y}} → sqrt x {{px}} ≡ sqrt y {{py}} → x ≡ y
        sqrt-inv : ∀ x → {{p : 0f ≤ x}} → {{q : 0f ≤ (x · x)}}→ sqrt (x · x) {{q}} ≡ x
        sqrt²-id : ∀ x → {{p : 0f ≤ x}} → sqrt x {{p}} · sqrt x {{p}} ≡ x

  module Bundle = ROrderedField {ℝℓ} {ℝℓ'}
  Bundle = ROrderedField {ℝℓ} {ℝℓ'}

  open Postulates public

  Carrier = ℝ

  bundle : Bundle
  bundle = (record
    { Carrier = ℝ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f
    ; 1f  = 1f
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; _⁻¹ = _⁻¹
    ; isROrderedField = isROrderedField
    ; isAbsOrderedCommRing = isAbsOrderedCommRing
    })

  -- abs : ℝ → ℝ
  -- abs x = max x (- x)

  open IsROrderedField isROrderedField public

module ℝ  = ℝ* hiding (ℝ)
module ℝʳ = ℝ*
    renaming
    ( Carrier to Carrierʳ
    ; _<_ to _<ʳ_
    ; _≤_ to _≤ʳ_
    ; _#_ to _#ʳ_
    ; min to minʳ
    ; max to maxʳ
    ; 0f  to 0ʳ
    ; 1f  to 1ʳ
    ; _+_ to _+ʳ_
    ; _·_ to _·ʳ_
    ; -_  to -ʳ_
    ; _⁻¹ to _⁻¹ʳ
    ; isROrderedField to isROrderedFieldʳ
    ; isRField to isRFieldʳ
    ; Bundle to Bundleʳ
    ; bundle to bundleʳ
    ; abs to absʳ
    )

module ℂ* where
  open ℝʳ
  module Postulates where
    postulate
      ℂ           : Type ℂℓ
      _#_         : Rel ℂ ℂ ℂℓ'
      0f 1f       : ℂ
      _+_ _·_     : ℂ → ℂ → ℂ
      -_          : ℂ → ℂ
      _⁻¹         : (x : ℂ) → {{ x # 0f }} → ℂ
      isRField : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹
      abs         : ℂ → ℝ
      0≤abs       : ∀ x → 0ʳ ≤ʳ abs x
      abs-preserves-0 : ∀ x → x ≡ 0f → abs x ≡ 0ʳ
      abs-reflects-0  : ∀ x → abs x ≡ 0ʳ → x ≡ 0f
      abs-preserves-· : ∀ x y → abs (x · y) ≡ (abs x) ·ʳ (abs y)
      abs-preserves-#0 : ∀ x → x # 0f → abs x #ʳ 0ʳ
      abs-reflects-#0 : ∀ x → abs x #ʳ 0ʳ → x # 0f


  module Bundle = RField {ℂℓ} {ℂℓ'}
  Bundle = RField {ℂℓ} {ℂℓ'}

  open Postulates public

  Carrier = ℂ

  bundle : Bundle
  bundle = (record
    { Carrier  = ℂ
    ; _#_      = _#_
    ; 0f       = 0f
    ; 1f       = 1f
    ; _+_      = _+_
    ; _·_      = _·_
    ; -_       = -_
    ; _⁻¹      = _⁻¹
    ; isRField = isRField
    })

  open IsRField isRField public

module ℂ  = ℂ* hiding (ℂ)
module ℂᶜ = ℂ*
    renaming
    ( Carrier to Carrierᶜ
    ; _#_ to _#ᶜ_
    ; 0f  to 0ᶜ
    ; 1f  to 1ᶜ
    ; _+_ to _+ᶜ_
    ; _·_ to _·ᶜ_
    ; -_  to -ᶜ_
    ; _⁻¹ to _⁻¹ᶜ
    ; isRField to isRFieldᶜ
    ; abs to absᶜ
    )

Isℕ↪ℤ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
Isℕ↪ℚ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
Isℕ↪ℂ = SyntheticReals.Number.Inclusions.IsRCommSemiringInclusion
Isℕ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
Isℤ↪ℚ = SyntheticReals.Number.Inclusions.IsROrderedCommRingInclusion
Isℤ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedCommRingInclusion
Isℤ↪ℂ = SyntheticReals.Number.Inclusions.IsRCommRingInclusion
Isℚ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedFieldInclusion
Isℚ↪ℂ = SyntheticReals.Number.Inclusions.IsRFieldInclusion
Isℝ↪ℂ = SyntheticReals.Number.Inclusions.IsRFieldInclusion

module Isℕ↪ℤ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℕ↪ℚ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℕ↪ℂ = SyntheticReals.Number.Inclusions.IsRCommSemiringInclusion
module Isℕ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℤ↪ℚ = SyntheticReals.Number.Inclusions.IsROrderedCommRingInclusion
module Isℤ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedCommRingInclusion
module Isℤ↪ℂ = SyntheticReals.Number.Inclusions.IsRCommRingInclusion
module Isℚ↪ℝ = SyntheticReals.Number.Inclusions.IsROrderedFieldInclusion
module Isℚ↪ℂ = SyntheticReals.Number.Inclusions.IsRFieldInclusion
module Isℝ↪ℂ = SyntheticReals.Number.Inclusions.IsRFieldInclusion

module _ where
  open ℕ* using (ℕ)
  open ℤ* using (ℤ)
  open ℚ* using (ℚ)
  open ℝ* using (ℝ)
  open ℂ* using (ℂ)
  postulate
    ℕ↪ℤ : ℕ → ℤ
    ℕ↪ℚ : ℕ → ℚ
    ℕ↪ℂ : ℕ → ℂ
    ℕ↪ℝ : ℕ → ℝ
    ℤ↪ℚ : ℤ → ℚ
    ℤ↪ℝ : ℤ → ℝ
    ℤ↪ℂ : ℤ → ℂ
    ℚ↪ℝ : ℚ → ℝ
    ℚ↪ℂ : ℚ → ℂ
    ℝ↪ℂ : ℝ → ℂ

    ℕ↪ℤinc : Isℕ↪ℤ (record {ℕ*}) (record {ℤ*}) ℕ↪ℤ
    ℕ↪ℚinc : Isℕ↪ℚ (record {ℕ*}) (record {ℚ*}) ℕ↪ℚ
    ℕ↪ℂinc : Isℕ↪ℂ (record {ℕ*}) (record {ℂ*}) ℕ↪ℂ
    ℕ↪ℝinc : Isℕ↪ℝ (record {ℕ*}) (record {ℝ*}) ℕ↪ℝ
    ℤ↪ℚinc : Isℤ↪ℚ (record {ℤ*}) (record {ℚ*}) ℤ↪ℚ
    ℤ↪ℝinc : Isℤ↪ℝ (record {ℤ*}) (record {ℝ*}) ℤ↪ℝ
    ℤ↪ℂinc : Isℤ↪ℂ (record {ℤ*}) (record {ℂ*}) ℤ↪ℂ
    ℚ↪ℝinc : Isℚ↪ℝ (record {ℚ*}) (record {ℝ*}) ℚ↪ℝ
    ℚ↪ℂinc : Isℚ↪ℂ (record {ℚ*}) (record {ℂ*}) ℚ↪ℂ
    ℝ↪ℂinc : Isℝ↪ℂ (record {ℝ*}) (record {ℂ*}) ℝ↪ℂ

    {-
    ℕ↪ℤinc : Isℕ↪ℤ                    ℕ.bundle    (record { ℤ.Bundle ℤ.bundle }) ℕ↪ℤ
    ℕ↪ℚinc : Isℕ↪ℚ                    ℕ.bundle    (record { ℚ.Bundle ℚ.bundle }) ℕ↪ℚ
    ℕ↪ℂinc : Isℕ↪ℂ                    ℕ.bundle                       ℂ.bundle    ℕ↪ℂ
    ℕ↪ℝinc : Isℕ↪ℝ                    ℕ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℕ↪ℝ
    ℤ↪ℚinc : Isℤ↪ℚ                    ℤ.bundle    (record { ℚ.Bundle ℚ.bundle }) ℤ↪ℚ
    ℤ↪ℝinc : Isℤ↪ℝ                    ℤ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℤ↪ℝ
    ℤ↪ℂinc : Isℤ↪ℂ                    ℤ.bundle                       ℂ.bundle    ℤ↪ℂ
    ℚ↪ℝinc : Isℚ↪ℝ                    ℚ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℚ↪ℝ
    ℚ↪ℂinc : Isℚ↪ℂ (record { ℚ.Bundle ℚ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℚ↪ℂ
    ℝ↪ℂinc : Isℝ↪ℂ (record { ℝ.Bundle ℝ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℝ↪ℂ
    -}
