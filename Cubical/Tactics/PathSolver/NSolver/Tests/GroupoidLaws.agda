{-# OPTIONS --safe -v 0 #-}

module Cubical.Tactics.PathSolver.NSolver.Tests.GroupoidLaws where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.Reflection.Error


private
 variable
  ℓ ℓ' : Level

module Ω-Tests where
 module Var (A : Type ℓ) (a : A) (p : a ≡ a) where
  _ : ResultIs ✓-pass
  _ = solvePathsTest
       p ∙ p ∙ p ∙ p ∙ p ≡ ((((p ∙ p) ∙ p) ∙ p) ∙ p)


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       p ∙ refl ∙ p ∙ refl ∙ p ∙ refl ∙ refl ∙ p ∙ refl ∙ refl ∙ p ∙ refl
         ≡ p ∙ p ∙ p ∙ p ∙ p


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       p ∙ p ⁻¹ ∙ p ∙' p ∙ p ⁻¹ ∙ p ∙ p ∙ p ⁻¹ ∙ p ⁻¹ ∙ p ⁻¹  ≡ refl



  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Cube
         refl (assoc p refl p)
         (cong (p ∙_) (lUnit p)) (cong (_∙ p) (rUnit p))
         refl refl



  _ : ResultIs ✓-pass
  _ = solvePathsTest
        Cube
          (λ i j → p (i ∨ ~ i ∨ j ∨ ~ j)) (λ _ _ → a)
          (λ _ _ → a) (λ _ _ → a)
          (λ _ _ → a) (λ _ _ → a)



 module HIT where
  open import Cubical.HITs.S1.Base

  _ : ResultIs ✓-pass
  _ = solvePathsTest
       loop ∙ loop ∙ loop ∙ loop ∙ loop ≡ ((((loop ∙ loop) ∙ loop) ∙ loop) ∙ loop)


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       loop ∙ refl ∙ loop ∙ refl ∙ loop ∙ refl ∙ refl ∙ loop ∙ refl ∙ refl ∙ loop ∙ refl
         ≡ loop ∙ loop ∙ loop ∙ loop ∙ loop


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       loop ∙ loop ⁻¹ ∙ loop ∙' loop ∙ loop ⁻¹ ∙ loop ∙ loop ∙ loop ⁻¹ ∙ loop ⁻¹ ∙ loop ⁻¹  ≡ refl


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Cube
         refl (assoc loop refl loop)
         (cong (loop ∙_) (lUnit loop)) (cong (_∙ loop) (rUnit loop))
         refl refl




module NoCong where
 module Var (A : Type ℓ) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A)
             (𝑝₀ : a₀ ≡ a₁)
             (𝑝₁ : a₁ ≡ a₂)
             (𝑝₂ : a₂ ≡ a₃)
             (𝑝₃ : a₃ ≡ a₄)
             (𝑝₄ : a₄ ≡ a₅)
             (𝑝₅ : a₅ ≡ a₆)
             (𝑝₆ : a₆ ≡ a₇) where

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths

  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths

  _ : ResultIs ✓-pass
  _ = solvePathsTest
        Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

module HIT {ℓ} where


  data A : Type ℓ where
    a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A
    𝑝₀ : a₀ ≡ a₁
    𝑝₁ : a₁ ≡ a₂
    𝑝₂ : a₂ ≡ a₃
    𝑝₃ : a₃ ≡ a₄
    𝑝₄ : a₄ ≡ a₅
    𝑝₅ : a₅ ≡ a₆
    𝑝₆ : a₆ ≡ a₇

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths

  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths

  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

module Edges&Diags {ℓ} (A : Type ℓ)
         (a⁵ : I → I → I → I → I → A)  where

  𝑝₀ : _  ≡ _
  𝑝₀ i = a⁵ i0 i i0 i (~ i)

  𝑝₁ : _ ≡ _
  𝑝₁ i = a⁵ i i1 i i1 i0

  𝑝₂ : _ ≡ _
  𝑝₂ i = a⁵ i1 (~ i) i1 i1 i0

  𝑝₃ : _ ≡ _
  𝑝₃ i =  a⁵ (~ i) i (~ i) (~ i) i

  𝑝₄ : _ ≡ _
  𝑝₄ _ = a⁵ i0 i1 i0 i0 i1

  𝑝₅ : _ ≡ _
  𝑝₅ i = a⁵ (i ∧ ~ i) i1 i0 i0 (i ∨  ~ i)

  𝑝₆ : _ ≡ _
  𝑝₆ i = a⁵ i0 i1 i0 i0 (~ i)

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths

  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths


  _ : ResultIs ✓-pass
  _ = solvePathsTest
       Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁


module InSubTerms {ℓ} (A : Type ℓ)
         (a₀ a₁ a₂ a₃ : A)
         (p₀₁ : a₀ ≡ a₁)
         (p₁₂ : a₁ ≡ a₂)

         (f : A → I → A)
         (g : A → A → A → A)
         (h : g a₀ a₁ ≡ g (f a₂ i0) a₃)
         (l : g (f a₂ i1) a₃ (f a₀ i1) ≡ a₀) where


  𝑝₀ : _  ≡ _
  𝑝₀ i = g (p₀₁ i) a₀ (f a₁ i)

  𝑝₁ : _ ≡ _
  𝑝₁ i = g (p₀₁ (~ i)) (p₀₁ i) (f (p₀₁ (~ i)) i1)

  𝑝₂ : _ ≡ _
  𝑝₂ i = h i (f a₀ i1)

  𝑝₃ : _ ≡ _
  𝑝₃ i = g (f a₂ i) a₃ (f a₀ i1)

  𝑝₄ : _ ≡ _
  𝑝₄ = l

  𝑝₅ : _ ≡ _
  𝑝₅ = p₀₁

  𝑝₆ : _ ≡ _
  𝑝₆ = p₁₂


  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths

  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths


  _ : ResultIs ✓-pass
  _ = solvePathsTest
        Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

