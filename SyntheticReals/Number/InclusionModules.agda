{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.InclusionModules where

import SyntheticReals.Number.Postulates
import SyntheticReals.Number.Inclusions

-- NOTE: the following takes a very long time to typecheck
-- see https://lists.chalmers.se/pipermail/agda-dev/2015-September/000201.html
-- see https://github.com/agda/agda/issues/1646
--     Exponential module chain leads to infeasible scope checking

module Isℕ↪ℤ = Number.Inclusions.IsROrderedCommSemiringInclusion Number.Postulates.ℕ↪ℤinc
module Isℕ↪ℚ = Number.Inclusions.IsROrderedCommSemiringInclusion Number.Postulates.ℕ↪ℚinc
module Isℕ↪ℂ = Number.Inclusions.Isℕ↪ℂ                           Number.Postulates.ℕ↪ℂinc
module Isℕ↪ℝ = Number.Inclusions.IsROrderedCommSemiringInclusion Number.Postulates.ℕ↪ℝinc
module Isℤ↪ℚ = Number.Inclusions.IsROrderedCommRingInclusion     Number.Postulates.ℤ↪ℚinc
module Isℤ↪ℝ = Number.Inclusions.IsROrderedCommRingInclusion     Number.Postulates.ℤ↪ℝinc
module Isℤ↪ℂ = Number.Inclusions.Isℤ↪ℂ                           Number.Postulates.ℤ↪ℂinc
module Isℚ↪ℝ = Number.Inclusions.IsROrderedFieldInclusion        Number.Postulates.ℚ↪ℝinc
module Isℚ↪ℂ = Number.Inclusions.IsRFieldInclusion               Number.Postulates.ℚ↪ℂinc
module Isℝ↪ℂ = Number.Inclusions.IsRFieldInclusion               Number.Postulates.ℝ↪ℂinc

{-
-- NOTE: the following is a little faster but does not help us

module Isℕ↪ℤ = Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℕ↪ℚ = Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℕ↪ℂ = Number.Inclusions.Isℕ↪ℂ
module Isℕ↪ℝ = Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℤ↪ℚ = Number.Inclusions.IsROrderedCommRingInclusion
module Isℤ↪ℝ = Number.Inclusions.IsROrderedCommRingInclusion
module Isℤ↪ℂ = Number.Inclusions.Isℤ↪ℂ
module Isℚ↪ℝ = Number.Inclusions.IsROrderedFieldInclusion
module Isℚ↪ℂ = Number.Inclusions.IsRFieldInclusion
module Isℝ↪ℂ = Number.Inclusions.IsRFieldInclusion
-}
