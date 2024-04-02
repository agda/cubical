{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function


open import Cubical.Tactics.PathSolver.Solver

private
  variable
    ℓ  : Level
    A B C : Type ℓ

module Examples (x y z w : A) (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ z) where

  pA pB pC : x ≡ w
  pA = (p ∙∙ refl ∙∙ q) ∙' sym r
  pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl
  pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r

  pA=pB : pA ≡ pB
  pA=pB = ≡!

  pB=pC : pB ≡ pC
  pB=pC = ≡!

  pA=pC : pA ≡ pC
  pA=pC = ≡!

  sqTest : Square p (sym r ∙ refl) (p ∙ q) (q ∙ sym r)
  sqTest = sq!


module Examples2 (x y z : B) (w : A) (f g : B → A)
  (p p' : x ≡ y) (q : y ≡ z) (r : w ≡ f z) where

  pA pB : f x ≡ w
  pA = cong f (p' ∙ sym p') ∙' cong f (p ∙∙ refl ∙∙ q) ∙ sym r
  pB = (cong f p ∙ (cong f q ∙ (sym (sym r ∙ (refl ∙ refl) ∙ refl ∙  r)) ∙ cong f (sym q)) ∙∙ cong f q ∙∙ refl) ∙∙ sym r ∙∙ refl


  pA=pB : pA ≡ pB
  pA=pB = ≡!cong f



module Examples3 (x y z : B) (w : A) (f : B → A)
  (p p' : x ≡ y) (q q' : y ≡ z) (r r' : f z ≡ w) where

  squares≃Example :   (Square (cong f p') (cong f q ∙ r) (cong f p) (cong f q' ∙ r'))
                        ≃ (cong f (sym (p ∙ q) ∙∙ p' ∙∙ q') ≡ r ∙ sym r')

  squares≃Example =
    2-cylinder-from-square.Sq≃Sq'
       (cong f ((p ∙ q)))
     (≡!cong f)


module Examples4 (f : B → A) (g : C → B)
                 (x y : B) (z w v : C)
                 (p : x ≡ y) (q : y ≡ g z) (r : z ≡ w) (u : w ≡ v) where


  sqE :  (cong f p ∙∙ cong f q ∙∙ cong (f ∘ g) r) ∙ (cong (f ∘ g) u)
          ≡ (cong f (p ∙ q)) ∙ (cong f (cong g r ∙ cong g u ))
  sqE = ≡!cong (f ∷ g ∷ [fn])


  sqE' : Square (cong f p ∙∙ cong f q ∙∙ cong (f ∘ g) r)
               (cong f (cong g r ∙ cong g u ))
               (cong f (p ∙ q))
               (cong (f ∘ g) u)
  sqE' = sq!cong (f ∷ g ∷ [fn])


module _ {A : Type ℓ} {x y z : A} (p q : x ≡ x) where

 SqCompEquiv : (Square p p q q) ≃ (p ∙ q ≡ q ∙ p)
 SqCompEquiv = 2-cylinder-from-square.Sq≃Sq' refl ≡!
