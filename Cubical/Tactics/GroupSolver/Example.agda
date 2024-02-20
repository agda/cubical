module Cubical.Tactics.GroupSolver.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure

open import Cubical.Tactics.GroupSolver.Groupoid

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

module _ {A : Type ℓ} where
 compSq' :   {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
             {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₀₀' a₀₁' : A} {a₀₋' : a₀₀' ≡ a₀₁'}
             {a₁₀' a₁₁' : A} {a₁₋' : a₁₀' ≡ a₁₁'} {a₋₀' : a₀₀' ≡ a₁₀'} {a₋₁' : a₀₁' ≡ a₁₁'}
         → Square a₀₋ a₁₋ a₋₀ a₋₁
         → (t : a₀₀ ≡ a₀₀')
         → (a₁₋ ⁻¹ ∙∙ a₋₀ ⁻¹ ∙∙ t ∙∙ a₋₀' ∙∙ a₁₋') ≡ (a₋₁ ⁻¹ ∙∙ a₀₋ ⁻¹ ∙∙ t ∙∙ a₀₋' ∙∙ a₋₁')
         → Square a₀₋' a₁₋' a₋₀' a₋₁'
 compSq' {a₀₋' = a₀₋'} {a₁₋' = a₁₋'} {a₋₀' = a₋₀'}  {a₋₁' =  a₋₁'} s t c i j =
  hcomp
    (λ k → λ {  (i = i0) → doubleCompPath-filler (sym (s i0)) t a₀₋' j k
              ; (i = i1) → doubleCompPath-filler (sym (s  i1))
                             ((λ i → s (~ i) i0) ∙∙ t ∙∙  a₋₀')  a₁₋' j k
              ; (j = i0) → doubleCompPath-filler (λ i → s (~ i) i0) t a₋₀' i k
              ; (j = i1) → compPathR→PathP∙∙ c (~ i) k
              }) (s i j)

open import Cubical.Algebra.Group



module EM₁-Example (G : Group ℓ) (a b c : fst G) where
  open GroupStr (snd G)

  data EM₁ : Type ℓ where
      embase : EM₁
      emloop : ⟨ G ⟩ → embase ≡ embase
      emcomp : (g h : ⟨ G ⟩ ) → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g · h))

  double-emcomp :  Square {A = EM₁}
                    (emloop b) (emloop ((a · b) · c))
                    (sym (emloop a)) (emloop c)

  double-emcomp =
    compSq'
      (emcomp a b ∙v emcomp (a · b) c)
      (emloop a)
      solveGroupoidDebug

