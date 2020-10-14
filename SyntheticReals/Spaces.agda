{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Spaces where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Structures.Poset
open import Cubical.Foundations.Function
open import Cubical.Structures.Ring
open import Cubical.Structures.AbGroup
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_)

open import Function.Base using (_∋_)
-- open import Function.Reasoning using (∋-syntax)
open import Function.Base using (it) -- instance search


{-
| name                                    | carrier | module | metric | norm | inner | basis | cauchy |
|-----------------------------------------|---------|--------|--------|------|-------|-------|--------|
| VectorSpace                             |   any   |   K    |        |      |       |       |        |
| FiniteDimVectorSpace                    |   any   |   K    |        |      |       |   ✓   |        |
| NormedVectorSpace                       |   any   |   K    |   (✓)  |   ✓  |       |       |        |
| FiniteDimNormedVectorSpace              |   any   |   K    |   (✓)  |   ✓  |       |   ✓   |        |
| CompleteNormedVectorSpace               |   any   |   K    |   (✓)  |   ✓  |       |       |   ✓    |
| FiniteDimCompleteNormedVectorSpace      |   any   |   K    |   (✓)  |   ✓  |       |   ✓   |   ✓    |
| InnerProductSpace                       |   any   |   K    |   (✓)  |  (✓) |   ✓   |       |        |
| FiniteDimInnerProductSpace              |   any   |   K    |   (✓)  |  (✓) |   ✓   |   ✓   |        |
| CompleteInnerProductSpace               |   any   |   K    |   (✓)  |  (✓) |   ✓   |       |   ✓    |
| FiniteDimCompleteInnerProductSpace      |   any   |   K    |   (✓)  |  (✓) |   ✓   |   ✓   |   ✓    |
| FiniteDimCompleteInnerProductSpaceOverℝ |    ℝ    |   ℝ    |   (✓)  |  (✓) |   ✓   |   ✓   |   ✓    |
-}
