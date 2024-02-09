{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

open import Cubical.Algebra.Group
open import Cubical.Tactics.GroupSolver.Solver

private
  variable
    ℓ : Level

module TestGeneric (G : Group ℓ) (A : Type ℓ) (f : A → ⟨ G ⟩)
        (g1 g2 g3 : ⟨ G ⟩) (a1 a2 : A) where

 open GroupStr (snd G)

 test : inv (g1 · (g2 · (inv (inv (inv (inv (f a1 · 1g)))) · f a2))) ≡
         1g · ((inv (f a2) · (inv (f a1) · (inv g2 · inv g1))))
 test = solveGroup G

 -- failTest : inv (g1 · (g2 · (inv (inv (inv (inv (f a1 · 1g)))) · f a2))) ≡
 --         1g · ((inv (g1) · (inv (f a1) · (inv g2 · inv g1))))
 -- failTest = solveGroup G

-- fail test will show  info in AgdaInfo buffer:

-- LHS ≠ RHS ‼
-- LHS: ((x₀)⁻¹·((x₁)⁻¹·((x₂)⁻¹·(x₃)⁻¹)))
-- RHS: ((x₃)⁻¹·((x₁)⁻¹·((x₂)⁻¹·(x₃)⁻¹)))

-- x₀ = f a2
-- x₁ = f a1
-- x₂ = g2
-- x₃ = g1





module TestGroupoidπ1 (A : hGroupoid ℓ) (a : ⟨ A ⟩) (p q r s : a ≡ a) where
  open import Cubical.Homotopy.Group.Base


  test : ((p ∙∙ refl ∙∙ q) ∙ sym s) ∙ sym r ≡
         (p ∙ (q ∙ sym (r ∙ s) ∙ p) ∙∙ refl ∙∙ refl) ∙∙ sym p ∙∙ refl
  test =  π₁solveGroup ⟨ A ⟩ (snd A) a


  -- testBad : r ∙ q ∙ refl ∙ q ∙ (p ∙ p ∙ (refl ∙ refl)) ∙ (q ∙ r) ∙ q ≡
  --        q ∙ sym (p ∙ (p ∙  q ∙ refl)) ∙ (refl) ∙ (refl ∙ refl) ∙ (sym q) ∙ r ∙ s
  -- testBad = π₁solveGroup ⟨ A ⟩ (snd A) a

  -- prints error msg :
  -- -- LHS ≢ RHS

  -- -- LHS: (𝒙₀∙(𝒙₁∙(refl∙(𝒙₁∙((𝒙₂∙(𝒙₂∙(refl∙refl)))∙((𝒙₁∙𝒙₀)∙𝒙₁))))))
  -- -- RHS: (𝒙₁∙((((𝒙₁⁻¹∙refl)∙'𝒙₂⁻¹)∙'𝒙₂⁻¹)∙(refl∙((refl∙refl)∙(𝒙₁⁻¹∙(𝒙₀∙𝒙₃))))))
  -- -- 𝒙₀ = λ i → r i
  -- -- 𝒙₁ = λ i → q i
  -- -- 𝒙₂ = λ i → p i
  -- -- 𝒙₃ = λ i → s i
