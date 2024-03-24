{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure

open import Cubical.Tactics.PathSolver.Solver

private
  variable
    ℓ ℓ' : Level

module Examples (A : Type ℓ) (x y z w : A) (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ z) where

  pA pB pC : x ≡ w
  pA = (p ∙∙ refl ∙∙ q) ∙ sym r
  pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl
  pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r

  pA=pB : pA ≡ pB
  pA=pB = solveGroupoidDebug

  pB=pC : pB ≡ pC
  pB=pC = solveGroupoidDebug

  pA=pC : pA ≡ pC
  pA=pC = solveGroupoidDebug

  pA=pB∙pB=pC-≡-pA=pC : pA=pB ∙ pB=pC ≡ pA=pC
  pA=pB∙pB=pC-≡-pA=pC = midCancel _ _ _


  sqTest : Square p (sym r ∙ refl) (p ∙ q) (q ∙ sym r)
  sqTest = solveSquareDebug

module _ {A : Type ℓ} {x y z : A} (p q : x ≡ x) where

 open import Cubical.Foundations.Equiv

 SqCompEquiv : (Square p p q q) ≃ (p ∙ q ≡ q ∙ p)
 SqCompEquiv = 2-cylinder-from-square.Sq≃Sq' refl solveSquareDebug



open import Cubical.Algebra.Group

-- module EM₁-Example (G : Group ℓ) (a b c : fst G) where
--   open GroupStr (snd G)

--   data EM₁ : Type ℓ where
--       embase : EM₁
--       emloop : ⟨ G ⟩ → embase ≡ embase
--       emcomp : (g h : ⟨ G ⟩ ) → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g · h))

--   double-emcomp :  Square {A = EM₁}
--                     (emloop b) (emloop ((a · b) · c))
--                     (sym (emloop a)) (emloop c)

--   double-emcomp = zzz
    
--    where
--     zz : (λ i →
--               hcomp
--               (doubleComp-faces (λ i₁ → emloop ((a · b) · c) (~ i₁))
--                (emloop ((a · b) · c)) i)
--               (hcomp
--                (doubleComp-faces
--                 (λ i₁ →
--                    hcomp (doubleComp-faces (λ _ → embase) (λ i₂ → embase) (~ i₁))
--                    embase)
--                 (λ i₁ → emloop a (~ i₁)) i)
--                (emloop a i)))
--            ≡
--            (λ i →
--               hcomp
--               (doubleComp-faces
--                (λ i₁ →
--                   hcomp (doubleComp-faces (λ _ → embase) (λ i₂ → emloop c i₂) (~ i₁))
--                   (emloop b (~ i₁)))
--                (λ i₁ → emloop c i₁) i)
--               (hcomp (doubleComp-faces (λ i₁ → emloop a (~ i₁)) (emloop b) i)
--                (emloop a i)))
--     zz = solveGroupoidDebug
   
--     zzz = fst (2-cylinder-from-square.Sq≃Sq'
--       (emloop a)
--       zz) (emcomp a b ∙v emcomp (a · b) c)
