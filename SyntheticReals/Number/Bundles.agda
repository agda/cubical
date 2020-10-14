{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.Number.Bundles where

private
  variable
    ℓ ℓ' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)

open import SyntheticReals.MoreAlgebra
open import SyntheticReals.Number.Structures

-- ℕ ℤ ℚ ℝ ℂ and ℚ₀⁺ ℝ₀⁺ ...
-- ring without additive inverse
record RCommSemiring : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier     : Type ℓ
    _#_ : Rel Carrier Carrier ℓ'
    -- RCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    isRCommSemiring : IsRCommSemiring _#_ 0f 1f _+_ _·_

  open IsRCommSemiring isRCommSemiring public

-- ℤ ℚ ℝ ℂ
record RCommRing : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier     : Type ℓ
    _#_ : Rel Carrier Carrier ℓ'
    -- RCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- RCommRing
    -_          : Carrier → Carrier
    isRCommRing : IsRCommRing _#_ 0f 1f _+_ _·_ -_

  open IsRCommRing isRCommRing public

-- ℚ ℝ ℂ
record RField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier     : Type ℓ
    _#_ : Rel Carrier Carrier ℓ'
    -- RCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- RCommRing
    -_          : Carrier → Carrier
    -- RField
    _⁻¹         : (x : Carrier) → {{ x # 0f }} → Carrier
    isRField : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹

-- Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
record RLattice : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor rlattice
  field
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    isRLattice  : IsRLattice _<_ _≤_ _#_ min max

  open IsRLattice isRLattice public

  infixl 4 _<_
  infixl 4 _≤_
  infixl 4 _#_

-- ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
-- ring without additive inverse
record ROrderedCommSemiring : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- _-_         : (x y : Carrier) → (y ≤ x) → Carrier -- is that a good idea?
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_

  open IsROrderedCommSemiring isROrderedCommSemiring public


-- ℤ ℚ ℝ
record ROrderedCommRing : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedCommRing
    -_          : Carrier → Carrier
    isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_

  open IsROrderedCommRing isROrderedCommRing public

  abs : Carrier → Carrier
  abs x = max x (- x)

  field
    isAbsOrderedCommRing : IsAbsOrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ abs

  open IsAbsOrderedCommRing isAbsOrderedCommRing public

-- ℚ ℝ
record ROrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedCommRing
    -_          : Carrier → Carrier
    -- ROrderedField
    _⁻¹         : (x : Carrier) → {{ x # 0f }} → Carrier
    isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹

  open IsROrderedField isROrderedField public

  abs : Carrier → Carrier
  abs x = max x (- x)

  field
    isAbsOrderedCommRing : IsAbsOrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ abs

  open IsAbsOrderedCommRing isAbsOrderedCommRing public

{-

-- ℚ₀⁺ ℝ₀⁺
record ROrderedSemifield : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedSemifield
    _-_         : (x y : Carrier) → (y ≤ x) → Carrier -- is that a good idea?
    _⁻¹         : (x : Carrier) → {{ 0f < x }} → Carrier

-- ℚ⁺ ℝ⁺
record ROrderedSemifieldWithoutZero : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedSemifieldWithoutZero
    1f          : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    _-_         : (x y : Carrier) → (y < x) → Carrier -- is that a good idea?
    _⁻¹         : Carrier → Carrier

-}
