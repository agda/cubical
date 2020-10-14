{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Structures2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Foundations.Logic
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.MorePropAlgebra.Structures


{-
| name | struct              | apart | abs | order | cauchy | sqrt₀⁺  | exp | final name                                                             |
|------|---------------------|-------|-----|-------|--------|---------|-----|------------------------------------------------------------------------|
| ℕ    | CommSemiring        |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedCommSemiring                                            |
| ℤ    | CommRing            |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedCommRing                                                |
| ℚ    | Field               |  (✓)  | (✓) | lin.  |        | (on x²) | (✓) | LinearlyOrderedField                                                   |
| ℝ    | Field               |  (✓)  | (✓) | part. |   ✓    |    ✓    | (✓) | CompletePartiallyOrderedFieldWithSqrt                                  |
| ℂ    | euclidean 2-Product |  (✓)  | (✓) |       |  (✓)   |         |  ?  | EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt             |
| R    | Ring                |   ✓   |  ✓  |       |        |         |  ?  | ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt          |
| G    | Group               |   ✓   |  ✓  |       |        |         |  ?  | ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt         |
| K    | Field               |   ✓   |  ✓  |       |   ✓    |         |  ?  | CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt |

-- NOTE: what about conjugation `conj`?
-}

-- we usually mean "CommRing" when writing just "Ring" ⇒ TODO: rename this where applicable

-- this is ℕ
record IsLinearlyOrderedCommSemiring {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  constructor islinearlyorderedcommsemiring

  infixl 4 _#_
  infixl 4 _≤_

  -- ≤, as in Lemma 4.1.7
  _≤_ : hPropRel F F ℓ'
  x ≤ y = ¬ (y < x)

  field
    is-CommSemiring     : [ isCommSemiring 0f 1f _+_ _·_ ]
    <-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
    ≤-Lattice           : [ isLattice _≤_ min max ]
    +-<-ext             : ∀ w x y z → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
    ·-preserves-<       : ∀ x y z   → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]

  open IsCommSemiring is-CommSemiring public
  open IsStrictLinearOrder <-StrictLinearOrder public
    renaming
      ( is-irrefl  to <-irrefl
      ; is-trans   to <-trans
      ; is-tricho  to <-trichoᵗ )

  abstract
    <-asym : ∀ a b → [ a < b ] → [ ¬ b < a ] -- [ isAsym _<_ ]
    <-asym = irrefl+trans⇒asym _<_ <-irrefl <-trans

    <-irrefl'' : ∀ a b → ([ a < b ] ⊎ [ b < a ]) → [ ¬(a ≡ₚ b) ]
    <-irrefl'' = isIrrefl'⇔isIrrefl'' _<_ <-asym .fst (isIrrefl⇔isIrrefl' _<_ .fst <-irrefl)

    <-irreflˢ'' : ∀ a b → ([ a < b ] ⊎ [ b < a ]) → ¬ᵗ(a ≡ b)
    <-irreflˢ'' = isIrreflˢ''⇔isIrrefl'' _<_ is-set <-asym .snd <-irrefl''

    <-tricho : ∀ a b → ([ a < b ] ⊎ [ b < a ]) ⊎ (a ≡ b)
    <-tricho = isTrichotomousˢ⇔isTrichotomous _<_ is-set <-irrefl'' <-irreflˢ'' <-asym .snd <-trichoᵗ

    <-StrictPartialOrder : [ isStrictPartialOrder _<_ ]
    <-StrictPartialOrder = strictlinearorder⇒strictpartialorder _<_ <-StrictLinearOrder

    -- ≤-PartialOrder : [ isPartialOrder _≤_ ]
    -- ≤-PartialOrder = {! linearorder⇒partialorder !}

    ≤-LinearOrder : [ isLinearOrder _≤_ ]
    ≤-LinearOrder = ≤'-isLinearOrder <-StrictLinearOrder

    ≤-Preorder : [ isPreorder _≤_ ]
    ≤-Preorder = ≤'-isPreorder <-StrictPartialOrder

  -- # is defined as in Lemma 4.1.7
  _#_ : hPropRel F F ℓ'
  x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  #-ApartnessRel : [ isApartnessRel _#_ ]
  #-ApartnessRel = #''-isApartnessRel <-StrictPartialOrder <-asym

  open IsApartnessRel #-ApartnessRel public renaming
    ( is-irrefl  to #-irrefl
    ; is-sym     to #-sym
    ; is-cotrans to #-cotrans
    )

  _ : [ isCommSemiring 0f 1f _+_ _·_             ]; _ = is-CommSemiring
  _ : [ isStrictLinearOrder _<_                  ]; _ = <-StrictLinearOrder
  _ : [ isLattice _≤_ min max                    ]; _ = ≤-Lattice

  open IsLattice ≤-Lattice renaming (≤-antisym to ≤-antisymᵗ) public

  ≤-antisym : [ isAntisymˢ _≤_ is-set ]
  ≤-antisym = isAntisymˢ⇔isAntisym _≤_ is-set .snd ≤-antisymᵗ

isLinearlyOrderedCommSemiring : ∀{ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) → hProp (ℓ-max ℓ ℓ')
isLinearlyOrderedCommSemiring 0f 1f _+_ _·_ _<_ min max .fst = IsLinearlyOrderedCommSemiring 0f 1f _+_ _·_ _<_ min max
isLinearlyOrderedCommSemiring 0f 1f _+_ _·_ _<_ min max .snd = φ where
  abstract φ = {!   !}

-- this is ℤ
record IsLinearlyOrderedCommRing {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  constructor islinearlyorderedcommring
  field
    is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0f 1f _+_ _·_ _<_ min max ]
    +-inverse : ∀ x → (x + (- x) ≡ 0f) × ((- x) + x ≡ 0f)

  infixl 6 _-_

  _-_ : F → F → F
  x - y = x + (- y)

  +-linv : (x : F) → (- x) + x ≡ 0f
  +-linv x = +-inverse x .snd

  +-rinv : (x : F) → x + (- x) ≡ 0f
  +-rinv x = +-inverse x .fst

  open IsLinearlyOrderedCommSemiring is-LinearlyOrderedCommSemiring public

isLinearlyOrderedCommRing : ∀{ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) → hProp (ℓ-max ℓ ℓ')
isLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max .fst = IsLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max
isLinearlyOrderedCommRing 0f 1f _+_ _·_ -_ _<_ min max .snd = φ where
  abstract φ = {!   !}

-- this is ℚ
record IsLinearlyOrderedField {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  constructor islinearlyorderedfield
  field
    is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0f 1f _+_ _·_ (-_) _<_ min max ]
  open IsLinearlyOrderedCommRing is-LinearlyOrderedCommRing public
  field
    ·-inv'' : ∀ x → [ (∃[ y ] ([ is-set ] (x · y) ≡ˢ 1f)) ⇔ (x # 0f) ]

isLinearlyOrderedField : ∀{ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) → hProp (ℓ-max ℓ ℓ')
isLinearlyOrderedField 0f 1f _+_ _·_ -_ _<_ min max .fst = IsLinearlyOrderedField 0f 1f _+_ _·_ -_ _<_ min max
isLinearlyOrderedField 0f 1f _+_ _·_ -_ _<_ min max .snd = φ where
  abstract φ = {!   !}

-- this is ℝ
record IsCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) (sqrt : (x : F) → {{ ! [ ¬(x < 0f) ] }} → F) : Type (ℓ-max ℓ ℓ') where
  constructor iscompletepartiallyorderedfield
  field
    -- 1. 2. 3. 4. 5. 6. (†) and (∗)
    is-PartiallyOrderedField : [ isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max ]
