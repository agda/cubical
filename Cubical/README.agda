{-# OPTIONS --cubical #-}
module Cubical.README where

------------------------------------------------------------------------
-- An experimental library for Cubical Agda
-----------------------------------------------------------------------

-- The library comes with a .agda-lib file, for use with the library
-- management system.

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- The core library for Cubical Agda.
-- It contains basic primitives, equivalences, glue types.
import Cubical.Core.Everything

-- The foundations for Cubical Agda.
-- The Prelude module is self-explanatory.
import Cubical.Foundations.Prelude
import Cubical.Foundations.Everything

-- Kinds and properties of functions
import Cubical.Functions.Everything

-- Data types and properties
import Cubical.Data.Everything

-- Higher-inductive types
import Cubical.HITs.Everything

-- Coinductive data types and properties
import Cubical.Codata.Everything

-- Properties and proofs about relations
import Cubical.Relation.Everything

-- Category theory
import Cubical.Categories.Everything

-- Homotopy theory
import Cubical.Homotopy.Everything

-- Properties and kinds of Modalities
import Cubical.Modalities.Everything

-- Various experiments using Cubical Agda
import Cubical.Experiments.Everything

-- Other modules (TODO: add descriptions)
import Cubical.Induction.Everything
import Cubical.Structures.Everything
import Cubical.ZCohomology.Everything

-- Algebra library (in development)
import Cubical.Algebra.Everything
