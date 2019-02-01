{-# OPTIONS --cubical #-}
module Cubical.Data.Everything where

open import Cubical.Data.EverythingSafe public

--- Modules making assumptions that might be incompatible with other
--  flags or make use of potentially unsafe features.

-- Uses --rewriting
open import Cubical.Data.Int.Rewrite public
