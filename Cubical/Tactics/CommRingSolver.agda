{-# OPTIONS --safe #-}
{-
  See CommRingSolver/Examples.agda for usage.

  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/RingSolver.agda
  and the 1lab.

  Boilerplate code for calling the ring solver is constructed automatically
  with agda's reflection features.
-}
module Cubical.Tactics.CommRingSolver where

open import Cubical.Tactics.CommRingSolver.Reflection public
