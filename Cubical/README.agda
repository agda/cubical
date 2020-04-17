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

-- Data types and properties
import Cubical.Data.Everything

-- Properties and proofs about relations
import Cubical.Relation.Everything

-- Higher-inductive types
import Cubical.HITs.Everything

-- Coinductive data types and properties
import Cubical.Codata.Everything

-- Various experiments using Cubical Agda
import Cubical.Experiments.Everything

-- Algebra library (in development)
import Cubical.Algebra.Everything
