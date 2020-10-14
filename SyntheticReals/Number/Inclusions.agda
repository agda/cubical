{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module SyntheticReals.Number.Inclusions where

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

-- open import Number.Structures ℝℓ ℝℓ'
open import SyntheticReals.Number.Bundles

-- Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
record IsRLatticeInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RLattice {ℓ} {ℓₚ}) (G : RLattice {ℓ'} {ℓₚ'})
  (f : (RLattice.Carrier F) → (RLattice.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RLattice F
    module G = RLattice G
  field
    -- injectivity? might follow from preserves-#?
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    -- lattice
    preserves-<   : ∀ x y →   x F.<   y → f x G.< f y
    preserves-≤   : ∀ x y →   x F.≤   y → f x G.≤ f y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-<    : ∀ x y → f x G.< f y →   x F.<   y
    reflects-≤    : ∀ x y → f x G.≤ f y →   x F.≤   y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    preserves-min : ∀ x y → f (F.min x y) ≡ G.min (f x) (f y)
    preserves-max : ∀ x y → f (F.max x y) ≡ G.max (f x) (f y)

-- ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
-- ring without additive inverse
record IsROrderedCommSemiringInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedCommSemiring {ℓ} {ℓₚ}) (G : ROrderedCommSemiring {ℓ'} {ℓₚ'})
  (f : (ROrderedCommSemiring.Carrier F) → (ROrderedCommSemiring.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedCommSemiring F
    module G = ROrderedCommSemiring G
  field
    isRLatticeInclusion : IsRLatticeInclusion (record {F}) (record {G}) f
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
  open IsRLatticeInclusion isRLatticeInclusion public

  preserves-#0 : ∀ x →   x  F.# F.0f → f x  G.# G.0f
  preserves-0≤ : ∀ x → F.0f F.≤   x  → G.0f G.≤ f x
  preserves-0< : ∀ x → F.0f F.<   x  → G.0f G.< f x
  preserves-<0 : ∀ x →   x  F.< F.0f → f x  G.< G.0f
  preserves-≤0 : ∀ x →   x  F.≤ F.0f → f x  G.≤ G.0f

  preserves-#0 x q = transport (λ i → f x G.# preserves-0 i) (preserves-# _ _ q)
  preserves-0≤ x q = transport (λ i → preserves-0 i G.≤ f x) (preserves-≤ _ _ q)
  preserves-0< x q = transport (λ i → preserves-0 i G.< f x) (preserves-< _ _ q)
  preserves-<0 x q = transport (λ i → f x G.< preserves-0 i) (preserves-< _ _ q)
  preserves-≤0 x q = transport (λ i → f x G.≤ preserves-0 i) (preserves-≤ _ _ q)

-- ℤ ℚ ℝ
record IsROrderedCommRingInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedCommRing {ℓ} {ℓₚ}) (G : ROrderedCommRing {ℓ'} {ℓₚ'})
  (f : (ROrderedCommRing.Carrier F) → (ROrderedCommRing.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedCommRing F
    module G = ROrderedCommRing G
  field
    isROrderedCommSemiringInclusion : IsROrderedCommSemiringInclusion (record {F}) (record {G}) f
    preserves-    : ∀ x   → f (  F.- x)   ≡     G.- (f x)
  open IsROrderedCommSemiringInclusion isROrderedCommSemiringInclusion public

-- ℚ ℝ
record IsROrderedFieldInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedField {ℓ} {ℓₚ}) (G : ROrderedField {ℓ'} {ℓₚ'})
  (f : (ROrderedField.Carrier F) → (ROrderedField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedField F
    module G = ROrderedField G
  field
    isROrderedCommRingInclusion : IsROrderedCommRingInclusion (record {F}) (record {G}) f
    preserves-⁻¹  : ∀ x → (p : x F.# F.0f) → (q : f x G.# G.0f) → f (F._⁻¹ x {{p}}) ≡ G._⁻¹ (f x) {{q}}
  open IsROrderedCommRingInclusion isROrderedCommRingInclusion public

-- ℚ ℝ ℂ
record IsRFieldInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RField {ℓ} {ℓₚ}) (G : RField {ℓ'} {ℓₚ'})
  (f : (RField.Carrier F) → (RField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RField F
    module G = RField G
  field
    -- CommSemiringInclusion
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
    -- other
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    -- TODO: properties

  preserves-#0 : ∀ x →   x  F.# F.0f → f x  G.# G.0f
  preserves-#0 x q = transport (λ i → f x G.# preserves-0 i) (preserves-# _ _ q)

-- ℕ ℤ ℚ ℝ ℂ
record IsRCommSemiringInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RCommSemiring {ℓ} {ℓₚ}) (G : RCommSemiring {ℓ'} {ℓₚ'})
  (f : (RCommSemiring.Carrier F) → (RCommSemiring.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RCommSemiring F
    module G = RCommSemiring G
  field
    -- CommSemiringInclusion
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
    -- other
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    -- TODO: properties

-- ℤ ℚ ℝ ℂ
record IsRCommRingInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RCommRing {ℓ} {ℓₚ}) (G : RCommRing {ℓ'} {ℓₚ'})
  (f : (RCommRing.Carrier F) → (RCommRing.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RCommRing F
    module G = RCommRing G
  field
    -- CommSemiringInclusion
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
    -- other
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    -- TODO: properties
