{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.Number.Structures where

private
  variable
    ℓ ℓ' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Data.Maybe.Base

import SyntheticReals.MoreAlgebra
open SyntheticReals.MoreAlgebra.Definitions

import Algebra.Structures

-- ℕ ℤ ℚ ℝ ℂ and ℚ₀⁺ ℝ₀⁺ ...
-- ring without additive inverse
-- see Algebra.Structures.IsCommutativeSemiring
record IsRCommSemiring {F : Type ℓ} (_#_ : Rel F F ℓ') (0f 1f : F) (_+_ _·_ : F → F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isApartnessRel : IsApartnessRel _#_
    -- TODO: properties

  open IsApartnessRel isApartnessRel public
    renaming
      ( isIrrefl  to #-irrefl
      ; isSym     to #-sym
      ; isCotrans to #-cotrans )

-- ℤ ℚ ℝ ℂ
-- see Algebra.Structures.IsCommutativeRing
record IsRCommRing {F : Type ℓ} (_#_ : Rel F F ℓ') (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRCommSemiring : IsRCommSemiring _#_ 0f 1f _+_ _·_

  open IsRCommSemiring isRCommSemiring public

-- ℚ ℝ ℂ
record IsRField {F : Type ℓ} (_#_ : Rel F F ℓ') (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ x # 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRCommRing : IsRCommRing _#_ 0f 1f _+_ _·_ -_
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y   →       x + y ≡ y + x
    distrib : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
    ⁻¹-preserves-#0 : ∀ x → (p : x # 0f) → _⁻¹ x {{p}} # 0f
    -preserves-#  : ∀ x y → x # y  → (- x) # (- y)
    -preserves-#0 : ∀ x   → x # 0f → (- x) #    0f
    ·-#0-#0-implies-#0 : ∀ a b → a  # 0f →  b # 0f → (a · b) #    0f
    1#0 : 1f # 0f
    -- TODO: properties

  open IsRCommRing isRCommRing public

-- Finₖ ℕ ℤ ℚ ℝ and ℚ₀⁺ ℚ⁺ ℝ₀⁺ ℝ⁺ ...
record IsRLattice {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isPartialOrder : IsPartialOrder _≤_
    glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
    glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
    lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
    lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z

    -- TODO: derived properties
    <-implies-# : ∀ x y → x < y → x # y
    ≤-#-implies-< : ∀ x y → x ≤ y → x # y → x < y
    #-sym : ∀ x y → x # y → y # x
    max-sym : ∀ x y → max x y ≡ max y x
    max-id : ∀ x → max x x ≡ x

  open IsPartialOrder isPartialOrder public

-- ℕ ℤ ℚ ℝ and ℚ₀⁺ ℚ⁺ ℝ₀⁺ ℝ⁺ ...
-- ring without additive inverse
record IsROrderedCommSemiring {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    isRCommSemiring : IsRCommSemiring _#_ 0f 1f _+_ _·_
    -- TODO: properties
    -- TODO: the following can be derived
    0<1 : 0f < 1f
    +-0<-0<-implies-0< : ∀ a b → 0f <  a → 0f <  b →    0f   < (a + b)
    +-0<-0≤-implies-0< : ∀ a b → 0f <  a → 0f ≤  b →    0f   < (a + b)
    +-0≤-0<-implies-0< : ∀ a b → 0f ≤  a → 0f <  b →    0f   < (a + b)
    +-0≤-0≤-implies-0≤ : ∀ a b → 0f ≤  a → 0f ≤  b →    0f   ≤ (a + b)
    +-<0-<0-implies-<0 : ∀ a b →  a < 0f →  b < 0f → (a + b) <    0f
    +-<0-≤0-implies-<0 : ∀ a b →  a < 0f →  b ≤ 0f → (a + b) <    0f
    +-≤0-<0-implies-<0 : ∀ a b →  a ≤ 0f →  b < 0f → (a + b) <    0f
    +-≤0-≤0-implies-≤0 : ∀ a b →  a ≤ 0f →  b ≤ 0f → (a + b) ≤    0f

    ·-#0-#0-implies-#0 : ∀ a b → a  # 0f →  b # 0f → (a · b) #    0f
    ·-#0-0<-implies-#0 : ∀ a b → a  # 0f → 0f < b  → (a · b) #    0f
    ·-#0-<0-implies-#0 : ∀ a b → a  # 0f →  b < 0f → (a · b) #    0f
    ·-0≤-0≤-implies-0≤ : ∀ a b → 0f ≤  a → 0f ≤ b  →    0f   ≤ (a · b)
    ·-0≤-0<-implies-0≤ : ∀ a b → 0f ≤  a → 0f < b  →    0f   ≤ (a · b)
    ·-0≤-<0-implies-≤0 : ∀ a b → 0f ≤  a →  b < 0f → (a · b) ≤    0f
    ·-0≤-≤0-implies-≤0 : ∀ a b → 0f ≤  a →  b ≤ 0f → (a · b) ≤    0f
    ·-0<-#0-implies-#0 : ∀ a b → 0f <  a →  b # 0f → (a · b) #    0f
    ·-0<-0≤-implies-0≤ : ∀ a b → 0f <  a → 0f ≤ b  →    0f   ≤ (a · b)
    ·-0<-0<-implies-0< : ∀ a b → 0f <  a → 0f < b  →    0f   < (a · b)
    ·-0<-<0-implies-<0 : ∀ a b → 0f <  a →  b < 0f → (a · b) <    0f
    ·-0<-≤0-implies-≤0 : ∀ a b → 0f <  a →  b ≤ 0f → (a · b) ≤    0f
    ·-<0-#0-implies-#0 : ∀ a b → a  < 0f →  b # 0f → (a · b) #    0f
    ·-<0-0≤-implies-≤0 : ∀ a b → a  < 0f → 0f ≤ b  → (a · b) ≤    0f
    ·-<0-0<-implies-<0 : ∀ a b → a  < 0f → 0f < b  → (a · b) <    0f
    ·-<0-<0-implies-0< : ∀ a b → a  < 0f →  b < 0f →    0f   < (a · b)
    ·-<0-≤0-implies-0≤ : ∀ a b → a  < 0f →  b ≤ 0f →    0f   ≤ (a · b)
    ·-≤0-0≤-implies-≤0 : ∀ a b → a  ≤ 0f → 0f ≤ b  → (a · b) ≤    0f
    ·-≤0-0<-implies-≤0 : ∀ a b → a  ≤ 0f → 0f < b  → (a · b) ≤    0f
    ·-≤0-<0-implies-0≤ : ∀ a b → a  ≤ 0f →  b < 0f →    0f   ≤ (a · b)
    ·-≤0-≤0-implies-0≤ : ∀ a b → a  ≤ 0f →  b ≤ 0f →    0f   ≤ (a · b)

    0≤-#0-implies-0< : ∀ x → 0f ≤ x → x # 0f → 0f < x

    {-
    ·-#0-#0-implies-#0 : ∀ a b → a  # 0f → b  # 0f → (a · b) #    0f
    ·-#0-0<-implies-#0 : ∀ a b → a  # 0f → 0f < b  → (a · b) #    0f
    ·-0≤-0≤-implies-0≤ : ∀ a b → 0f ≤ a  → 0f ≤ b  →    0f   ≤ (a · b)
    ·-0≤-0<-implies-0≤ : ∀ a b → 0f ≤ a  → 0f < b  →    0f   ≤ (a · b)
    ·-0≤-≤0-implies-≤0 : ∀ a b → 0f ≤ a  → b  ≤ 0f → (a · b) ≤    0f
    ·-0<-#0-implies-#0 : ∀ a b → 0f < a  → b  # 0f → (a · b) #    0f
    ·-0<-0≤-implies-0≤ : ∀ a b → 0f < a  → 0f ≤ b  →    0f   ≤ (a · b)
    ·-0<-0<-implies-0< : ∀ a b → 0f < a  → 0f < b  →    0f   < (a · b)
    ·-0<-≤0-implies-≤0 : ∀ a b → 0f < a  → b  ≤ 0f → (a · b) ≤    0f
    ·-≤0-0≤-implies-≤0 : ∀ a b → a  ≤ 0f → 0f ≤ b  → (a · b) ≤    0f
    ·-≤0-0<-implies-≤0 : ∀ a b → a  ≤ 0f → 0f < b  → (a · b) ≤    0f
    ·-≤0-≤0-implies-0≤ : ∀ a b → a  ≤ 0f → b  ≤ 0f →    0f   ≤ (a · b)
    -}

  open IsRLattice isRLattice public

-- ℤ ℚ ℝ
record IsROrderedCommRing {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    isRCommRing : IsRCommRing _#_ 0f 1f _+_ _·_ -_
    0≡-0 : 0f ≡ - 0f
    -flips-<  : ∀ x y → x  < y  → (- y) < (- x)
    -flips-<0 : ∀ x   → x  < 0f →    0f < (- x)
    -flips-0< : ∀ x   → 0f < x  → (- x) <    0f
    -flips-≤  : ∀ x y → x  ≤ y  → (- y) ≤ (- x)
    -flips-≤0 : ∀ x   → x  ≤ 0f →    0f ≤ (- x)
    -flips-0≤ : ∀ x   → 0f ≤ x  → (- x) ≤    0f
    -preserves-#  : ∀ x y → x # y  → (- x) # (- y)
    -preserves-#0 : ∀ x   → x # 0f → (- x) #    0f
    -- TODO: properties

  open IsROrderedCommSemiring isROrderedCommSemiring public

-- Remark 6.7.7. As we define absolute values by | x | = max(x, -x), as is common in constructive analysis,
-- if x has a locator, then so does | x |, and we use this fact in the proof of the above theorem.

-- Remark 4.1.9.
--
-- 1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that
-- for every x and y,
--
--   max(x, y) = x  ∨  max(x, y) = y,
--
-- which would hold in a linear order.
-- However, in Lemma 6.7.1 we characterize max as
--
--   z < max(x, y) ⇔ z < x ∨ z < y,
--
-- and similarly for min.

{- from: https://isabelle.in.tum.de/doc/tutorial.pdf "8.4.5 The Numeric Type Classes"

  Absolute Value.

  The absolute value function `abs` is available for all ordered rings, including types int, rat and real.
  It satisfies many properties, such as the following:

    | x * y | ≡ | x | * | y |         (abs_mult)

    | a | ≤ b ⇔ (a ≤ b) ∧ (- a) ≤ b   (abs_le_iff)

    | a + b | ≤ | a | + | b |         (abs_triangle_ineq)
-}

-- also see https://en.wikipedia.org/wiki/Ordered_ring#Basic_properties

record IsAbsOrderedCommRing {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (abs : F → F) : Type (ℓ-max ℓ ℓ') where
  field
    abs0≡0          :         abs 0f ≡ 0f
    abs-preserves-· : ∀ x y → abs (x · y) ≡ abs x · abs y
    triangle-ineq   : ∀ x y → abs (x + y) ≤ (abs x + abs y)
    -- -trichotomy     : ∀ x → (x ≡ 0f) ⊎ (0f < x) ⊎ (0f < (- x))
    abs-≤           : ∀ x y → abs x ≤ y → (x ≤ y) × ((- x) ≤ y)
    abs-≤-back      : ∀ x y → (x ≤ y) × ((- x) ≤ y) → abs x ≤ y
    0≤abs           : ∀ x   → 0f ≤ abs x


-- ℚ ℝ
record IsROrderedField {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ x # 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
    isRField           : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹
    -- TODO: properties

  open IsROrderedCommRing isROrderedCommRing hiding
    ( -preserves-#
    ; -preserves-#0
    ) public
  open IsRField isRField hiding
    ( ·-#0-#0-implies-#0
    ) public

  field
    ⁻¹-preserves-<0 : ∀ x → (x < 0f) → (p : x # 0f) → _⁻¹ x {{p}} < 0f
    ⁻¹-preserves-0< : ∀ x → (0f < x) → (p : x # 0f) → 0f < _⁻¹ x {{p}}

-- ℚ₀⁺ ℚ₀⁻ ℝ₀⁺ ℝ₀⁻
{-
record IsROrderedSemifield {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → {{ x < 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    -- TODO: properties
    #0-implies-0< : ∀ x → 0f # x → 0f < x
    positivity : ∀ x → 0f ≤ x
  open IsROrderedCommSemiring isROrderedCommSemiring public
-}

-- ℚ⁺ ℚ⁻ ℝ⁺ ℝ⁻
{-
record IsROrderedSemifieldWithoutZero {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    -- isGroup : IsGroup 1f _·_ _⁻¹
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y → x + y ≡ y + x
    distrib : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
    -- TODO: properties
  open IsRLattice isRLattice public

-}
