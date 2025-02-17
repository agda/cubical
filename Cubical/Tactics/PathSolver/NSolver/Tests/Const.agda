{-# OPTIONS --safe -v 0 #-}

module Cubical.Tactics.PathSolver.NSolver.Tests.Const where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.Reflection.Error

private
 variable
  ℓ ℓ' : Level

module Var {A : Type ℓ} (a : A) where

 _ : ResultIs ✓-pass
 _ = solvePathsTest
        refl {x = a} ∙ refl ≡ refl

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       refl ∙ (refl {x = a} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl
 _ : ResultIs ✓-pass
 _ = solvePathsTest
       Square
       (((((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
       refl
       (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
       ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))


 _ : ResultIs ✓-pass
 _ = solvePathsTest
      Cube
         refl (assoc (refl {x = a}) refl refl)
         (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
         refl refl


 module Def where
  abstract
   a' : A
   a' = a

  _ : ResultIs ✓-pass
  _ = solvePathsTest
       refl {x = a'} ∙ refl ≡ refl


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       refl ∙ (refl {x = a'} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl

  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Square
        (((((refl {x = a'} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
        refl
        (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
        ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Cube
         refl (assoc (refl {x = a'}) refl refl)
         (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
         refl refl



module DataType {ℓ} where

 data A : Type ℓ where
  a : A

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       refl {x = a} ∙ refl ≡ refl

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       refl ∙ (refl {x = a} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       Square
       (((((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
       refl
       (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
       ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))


 _ : ResultIs ✓-pass
 _ = solvePathsTest
       Cube
        refl (assoc (refl {x = a}) refl refl)
        (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
        refl refl

