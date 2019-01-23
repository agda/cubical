{-# OPTIONS --cubical --safe #-}
module Cubical.Basics.Unit where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

-- Obtain Unit
open import Agda.Builtin.Unit public
  renaming ( ⊤ to Unit )
