{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group
open import Cubical.Tactics.GroupSolver.Solver

private
  variable
    ℓ : Level


module example (G : Group ℓ) where
 open GroupStr (snd G)
 
 module _  (p p' q q' r s : ⟨ G ⟩) where


  pA pB pC : ⟨ G ⟩
  pA = (p · (1g · q)) · inv r
  pB = (p · ((q · (inv ((q' · inv q') ·
          inv r · ((s · inv s) · r)) · inv q)) · (q · 1g))) · (inv r · 1g)
  pC = (1g · p') · (((q · inv q) · (inv p' · p)) · (q · (inv q · (q · inv r))))


  pA=pB : pA ≡ pB
  pA=pB = solveGroup G

  pA=pC : pA ≡ pC
  pA=pC = solveGroup G

  pB=pC : pB ≡ pC
  pB=pC = solveGroup G
