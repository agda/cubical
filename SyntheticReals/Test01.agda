{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module Test01 where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

open import Number.Postulates
open import Number.Inclusions
open import Number.Base
open import MoreNatProperties

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

open PatternsProp














lemma : ∀(N : ℤ) → ℤ↪ℝ (absᶻ N) ≡ absᶜ (ℤ↪ℂ N)
lemma N = ?
