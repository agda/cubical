{-# OPTIONS --safe -v 0 #-}

module Cubical.Tactics.PathSolver.NSolver.Tests.Cong where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.PathSolver.Path
open import Cubical.Tactics.Reflection.Error


private
 variable
  ℓ ℓ' : Level



module Refl {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) where

 _ : ResultIs ✓-pass
 _ = solvePathsTest
      cong f (refl {x = a} ∙ refl) ≡ refl

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       cong f (refl ∙ (refl {x = a} ∙ refl) ∙ refl) ∙ cong f ((refl ∙ refl) ∙ refl) ≡ refl

 _ : ResultIs ✓-pass
 _ = solvePathsTest
      Square
       ((cong f (((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
       refl
       (refl ∙ cong f (refl ∙ refl ∙ refl) ∙ cong f (refl ∙ refl))
       (cong f ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl )))

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       Cube
        refl (congP (λ _ → cong f) (assoc (refl {x = a}) refl refl))
        (cong (refl ∙_) (lUnit refl) ∙ solvePaths)
        (cong (_∙ refl) (rUnit refl) ∙ solvePaths)
        refl refl

module CongCoherent {A : Type ℓ} {B : Type ℓ'} (f : A → B) (SA : NPath 4 A) where
 open NPath SA

 LHS RHS : 𝑣₀ ≡ 𝑣₄
 LHS = (𝑝₀ ∙ refl ∙ 𝑝₁) ∙ (𝑝₂ ∙ refl ∙ 𝑝₃)
 RHS = 𝑝₀ ∙∙ (𝑝₁ ∙∙ refl ∙∙ 𝑝₂) ∙∙ 𝑝₃

 solve[cong] cong[solve] : cong f LHS ≡ cong f RHS

 solve[cong] = solvePaths

 cong[solve] = cong (cong f) solvePaths

 _ : ResultIs ✓-pass
 _ = solvePathsTest
       cong[solve] ≡ solve[cong]
