{-# OPTIONS --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
  and the 1lab.

  Boilerplate code for calling the ring solver is constructed automatically
  with agda's reflection features.
-}
module Cubical.Tactics.NatSolver where

open import Cubical.Tactics.NatSolver.Reflection public
