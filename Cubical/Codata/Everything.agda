{-# OPTIONS --cubical #-}
module Cubical.Codata.Everything where

open import Cubical.Codata.EverythingSafe public

--- Modules making assumptions that might be incompatible with other
--  flags or make use of potentially unsafe features.

-- Assumes --guardedness
open import Cubical.Codata.Stream public

open import Cubical.Codata.Conat public

open import Cubical.Codata.M public

-- Also uses {-# TERMINATING #-}.
open import Cubical.Codata.M.Bisimilarity public

{-
-- Alternative M type implemetation, based on
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti
-}

open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.Coalg
open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.itree
open import Cubical.Codata.M.AsLimit.stream
