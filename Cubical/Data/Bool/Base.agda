{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Bool.Base where

open import Cubical.Core.Everything

-- Obtain the booleans
open import Agda.Builtin.Bool public

not : Bool → Bool
not true = false
not false = true
