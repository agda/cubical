{-# OPTIONS --safe -v 0 #-}

module Cubical.Tactics.PathSolver.NSolver.Tests.Coherence where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.PathSolver.Path
open import Cubical.Tactics.Reflection.Error


private
 variable
  ℓ ℓ' : Level


module CompCoherence {A : Type ℓ} (SA : NPath 7 A) where
  open NPath SA

  -- module Basic where
  --  LHS₀ RHS₀ : 𝑣₀ ≡ 𝑣₂
  --  LHS₀ = 𝑝₀ ∙∙ 𝑝₁ ∙∙ refl
  --  RHS₀ = 𝑝₀ ∙∙ refl ∙∙ 𝑝₁

  --  LHS₁ RHS₁ : 𝑣₂ ≡ 𝑣₃
  --  LHS₁ = 𝑝₂
  --  RHS₁ = 𝑝₂

  --  LHS₀≡RHS₀ : LHS₀ ≡ RHS₀
  --  LHS₀≡RHS₀ = solvePaths

  --  LHS₁≡RHS₁ : LHS₁ ≡ RHS₁
  --  LHS₁≡RHS₁ = solvePaths

  --  LHS₀∙LHS₁≡RHS₀∙RHS₁ : LHS₀ ∙ LHS₁ ≡ RHS₀ ∙ RHS₁
  --  LHS₀∙LHS₁≡RHS₀∙RHS₁ = solvePaths


  --  _ : ResultIs ✓-pass
  --  _ = solvePathsTest
  --        cong₂ _∙_ LHS₀≡RHS₀ LHS₁≡RHS₁ ≡ LHS₀∙LHS₁≡RHS₀∙RHS₁

  --  LHS₀⁻¹≡RHS₀⁻¹ : LHS₀ ⁻¹ ≡ RHS₀ ⁻¹
  --  LHS₀⁻¹≡RHS₀⁻¹ = solvePaths

  --  _ : ResultIs ✓-pass
  --  _ = solvePathsTest
  --        cong (_⁻¹) LHS₀≡RHS₀ ≡ LHS₀⁻¹≡RHS₀⁻¹

  -- module WithDegens where
  --  LHS₀ RHS₀ : 𝑣₀ ≡ 𝑣₄
  --  LHS₀ = 𝑝₀ ∙∙ 𝑝₁ ∙ (𝑝₂ ∙ (𝑝₁ ∙ 𝑝₂) ⁻¹) ∙ 𝑝₁ ∙∙ 𝑝₂ ∙ 𝑝₃
  --  RHS₀ = 𝑝₀ ∙ (λ i → 𝑝₁ (i ∧ ~ i)) ∙ 𝑝₁ ∙ 𝑝₂ ∙ (λ i → 𝑝₂ (i ∨ ~ i)) ∙  𝑝₃

  --  LHS₁ RHS₁ : 𝑣₄ ≡ 𝑣₇
  --  LHS₁ = 𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆
  --  RHS₁ = 𝑝₄ ∙ refl ∙ 𝑝₅ ∙ refl ∙ refl ∙ 𝑝₆

  --  LHS₀≡RHS₀ : LHS₀ ≡ RHS₀
  --  LHS₀≡RHS₀ = solvePaths

  --  LHS₁≡RHS₁ : LHS₁ ≡ RHS₁
  --  LHS₁≡RHS₁ = solvePaths

  --  LHS₀∙LHS₁≡RHS₀∙RHS₁ : LHS₀ ∙ LHS₁ ≡ RHS₀ ∙ RHS₁
  --  LHS₀∙LHS₁≡RHS₀∙RHS₁ = solvePaths

  --  _ : ResultIs ✓-pass
  --  _ = solvePathsTest
  --       cong₂ _∙_ LHS₀≡RHS₀ LHS₁≡RHS₁ ≡ LHS₀∙LHS₁≡RHS₀∙RHS₁
  --  LHS₀⁻¹≡RHS₀⁻¹ : LHS₀ ⁻¹ ≡ RHS₀ ⁻¹
  --  LHS₀⁻¹≡RHS₀⁻¹ = solvePaths

  --  _ : ResultIs ✓-pass
  --  _ = solvePathsTest
  --       cong (_⁻¹) LHS₀≡RHS₀ ≡ LHS₀⁻¹≡RHS₀⁻¹
