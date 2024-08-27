{-

This file serves as a demonstration of the NSolver module, showcasing practical examples of its usage. It provides concrete cases for computing fillings of n-dimensional cubes under the assumption that boundary cells are expressible as paths (potentialy applied to arbitrary complex interval expressions).

Unlike the `Tests` folder, which focuses on verifying correctness through unit tests, this file emphasizes illustration and practical application.

Limitations of this solver, are best exemplified in the `Cubical.Tactics.PathSolver.MonoidalSolver.Examples`,
containing examples of complementary solver usage, capable of applying monoidal groupoid laws.

-}

{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.NSolver.Examples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sum

open import Cubical.Data.Sigma

open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.PathSolver.Path


private
  variable
    ℓ : Level
    A B : Type ℓ



module Coherence (SA : NPath 7 A) where
  open NPath SA



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

  -- this works but is slow (~2 min)
  -- but resulting term is managable, and can be evaluated end typechecked quickly if imported in other module

  -- coh : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
  -- coh =  solvePaths

module CompCoherence (SA : NPath 7 A) where
   open NPath SA

   LHS₀ RHS₀ : 𝑣₀ ≡ 𝑣₄
   LHS₀ = 𝑝₀ ∙∙ 𝑝₁ ∙ (𝑝₂ ∙ (𝑝₁ ∙ 𝑝₂) ⁻¹) ∙ 𝑝₁ ∙∙ 𝑝₂ ∙ 𝑝₃
   RHS₀ = 𝑝₀ ∙ (λ i → 𝑝₁ (i ∧ ~ i)) ∙ 𝑝₁ ∙ 𝑝₂ ∙ (λ i → 𝑝₂ (i ∨ ~ i)) ∙  𝑝₃

   LHS₁ RHS₁ : 𝑣₄ ≡ 𝑣₇
   LHS₁ = 𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆
   RHS₁ = 𝑝₄ ∙ refl ∙ 𝑝₅ ∙ refl ∙ refl ∙ 𝑝₆

   LHS₀≡RHS₀ : LHS₀ ≡ RHS₀
   LHS₀≡RHS₀ = solvePaths

   LHS₁≡RHS₁ : LHS₁ ≡ RHS₁
   LHS₁≡RHS₁ = solvePaths

   LHS₀∙LHS₁≡RHS₀∙RHS₁ : LHS₀ ∙ LHS₁ ≡ RHS₀ ∙ RHS₁
   LHS₀∙LHS₁≡RHS₀∙RHS₁ = solvePaths

   _ : cong₂ _∙_ LHS₀≡RHS₀ LHS₁≡RHS₁ ≡ LHS₀∙LHS₁≡RHS₀∙RHS₁
   _ = solvePaths

   LHS₀⁻¹≡RHS₀⁻¹ : LHS₀ ⁻¹ ≡ RHS₀ ⁻¹
   LHS₀⁻¹≡RHS₀⁻¹ = solvePaths

   _ :  cong (_⁻¹) LHS₀≡RHS₀ ≡ LHS₀⁻¹≡RHS₀⁻¹
   _ = solvePaths



module GroupoidLaws (SA : NPath 6 A) where
 open NPath SA

 symDist₅ : sym (𝑝₀ ∙ 𝑝₁ ∙ 𝑝₂ ∙ 𝑝₃ ∙ 𝑝₄ ∙ 𝑝₅)
          ≡ sym 𝑝₅ ∙ sym 𝑝₄ ∙ sym 𝑝₃ ∙ sym 𝑝₂ ∙ sym 𝑝₁ ∙ sym 𝑝₀
 symDist₅ = solvePaths


 module E₁ where
  pa₀ pa₁ pa₂ pa₃ : 𝑣₀ ≡ 𝑣₆
  pa₀ = 𝑝₀ ∙ 𝑝₁ ∙ 𝑝₂ ∙ 𝑝₃ ∙ 𝑝₄ ∙ 𝑝₅
  pa₁ = ((((𝑝₀ ∙ 𝑝₁) ∙ 𝑝₂) ∙ 𝑝₃) ∙ 𝑝₄) ∙ 𝑝₅
  pa₂ = 𝑝₀ ∙ 𝑝₁ ∙' (refl ∙∙ 𝑝₂ ∙∙ (𝑝₃ ∙∙ 𝑝₄ ∙∙ 𝑝₅))
  pa₃ = 𝑝₀ ∙∙ 𝑝₁ ∙∙ (refl ∙' 𝑝₂ ∙ (𝑝₃ ∙' 𝑝₄ ∙ 𝑝₅))

  assoc₅ : pa₀ ≡ pa₁
  assoc₅ = solvePaths

  pa₂≡pa₃ : pa₂ ≡ pa₃
  pa₂≡pa₃ = solvePaths

  pa₃≡pa₂ : pa₃ ≡ pa₂
  pa₃≡pa₂ = solvePaths

  sym[pa₃≡pa₂]≡pa₂≡pa₃ : sym (pa₃≡pa₂) ≡ pa₂≡pa₃
  sym[pa₃≡pa₂]≡pa₂≡pa₃ = refl

  pa₀≡pa₂ : pa₀ ≡ pa₂
  pa₀≡pa₂ = solvePaths

  pa₁≡pa₃ : pa₁ ≡ pa₃
  pa₁≡pa₃ = solvePaths

  pa₀≡pa₃ : pa₀ ≡ pa₃
  pa₀≡pa₃ = solvePaths


  coherence : Square
     assoc₅ pa₂≡pa₃
     pa₀≡pa₂ pa₁≡pa₃
  coherence = coh₃helper

  coh∙ :  assoc₅ ∙ pa₁≡pa₃ ≡ pa₀≡pa₃
  coh∙ = comp-coh-helper







module 2GroupoidLaws where

 module Triangle (SA : NPath 2 A) (X : A)  where
  open NPath SA


  triangleIdentity : Cube
            refl (assoc 𝑝₀ refl 𝑝₁)
            (cong (𝑝₀ ∙_) (lUnit 𝑝₁)) (cong (_∙ 𝑝₁) (rUnit 𝑝₀))
            refl refl
  triangleIdentity = solvePaths

 module Pentagon (SA : NPath 4 A)  where
  open NPath SA


  pentagonIdentity' : assoc 𝑝₀ 𝑝₁ (𝑝₂ ∙ 𝑝₃) ∙ assoc (𝑝₀ ∙ 𝑝₁) 𝑝₂ 𝑝₃
                          ≡
                   cong (𝑝₀ ∙_) (assoc 𝑝₁ 𝑝₂ 𝑝₃) ∙∙ assoc 𝑝₀ (𝑝₁ ∙ 𝑝₂) 𝑝₃ ∙∙ cong (_∙ 𝑝₃) (assoc 𝑝₀ 𝑝₁ 𝑝₂)
  pentagonIdentity' = solvePaths


  -- solving this 4-cube commented code bellow takes
  -- ~8 min (but memory spikes to more than 100GiB !)

  -- pentagonIdentity'≡pentagonIdentity : pentagonIdentity' ≡ pentagonIdentity 𝑝₀ 𝑝₁ 𝑝₂ 𝑝₃
  -- pentagonIdentity'≡pentagonIdentity = solvePaths

  module _ (f : A → B) where

   cf : ∀ {x y} → (p : x ≡ y) → f x ≡ f y
   cf = cong f

   pentagonIdentityCong :
       Square
        (assoc (cf 𝑝₀) (cf 𝑝₁) ((cf 𝑝₂) ∙ (cf 𝑝₃)) ∙ assoc ((cf 𝑝₀) ∙ (cf 𝑝₁)) (cf 𝑝₂) (cf 𝑝₃))
        (sym (cong-∙ f _ _) ∙∙ cong cf (assoc 𝑝₀ (𝑝₁ ∙ 𝑝₂) 𝑝₃) ∙∙ cong-∙ f _ _)
        ((cong (cf 𝑝₀ ∙_) (cong (cf 𝑝₁ ∙_) (sym (cong-∙ f _ _))
                           ∙∙ sym (cong-∙ f _ _)
                           ∙∙ cong cf (assoc 𝑝₁ 𝑝₂ 𝑝₃))))
        ((cong (_∙ cf 𝑝₃) (cong (_∙ cf 𝑝₂) (sym (cong-∙ f _ _))
                           ∙∙ sym (cong-∙ f _ _)
                           ∙∙ cong cf (sym (assoc 𝑝₀ 𝑝₁ 𝑝₂)))))
   pentagonIdentityCong = solvePaths


module Glue (A B C D E : Type ℓ)
  (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) (p : D ≡ E) where

 e0 : Square (ua e₀ ∙ ua e₁) (ua e₀ ∙∙ (ua e₁ ∙ ua e₂) ∙∙ p) refl (ua e₂ ∙ p)
 e0 = solvePaths

 e0L : Square (cong List (cong List (ua e₀) ∙ cong List (ua e₁)))
              (cong (List ∘S List) (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂))
              refl (cong (List ∘S List) (ua e₂))
 e0L = solvePaths


module funTypes {x y z : A} (f : A → A → B)
 (p : x ≡ y)
 (q : y ≡ z) where


 P Q : _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y)
 P = (λ i x' → f x' (p i)) ∙∙ (λ i x' → f x' (q i)) ∙∙ (λ i x' → f x' (q (~ i)))
 Q = refl ∙ (λ i x' → f x' (p i))




module compPathR-PathP∙∙
        {x y : A} {p : x ≡ y}
    where

 invSides-filler-rot' : (invSides-filler p p) ≡ (symP (invSides-filler (sym p) (sym p)))

 invSides-filler-rot' = solvePaths

 _ : invSides-filler-rot p ≡ invSides-filler-rot'
 _ = solvePaths




module _ {A : Type} {x y z w v : A} (p' p'' : x ≡ y) (xr xr' : x ≡ x) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v)
           (sq : Square xr (sym p'') p'' xr') where

 _ : refl ≡ λ i → p' (i ∨ ~ i)
 _ = solvePaths

 _ : Cube
        (λ i j → p' (i ∨ ~ i ∨ j ∨ ~ j)) (λ _ _ → y)
        (λ _ _ → y) (λ _ _ → y)
        (λ _ _ → y) (λ _ _ → y)
 _ = solvePaths

 _ : (λ i → sq i (~ i)) ∙ refl ∙ ((λ i → sq (~ i) i) ∙ (λ i → sq i (~ i)) ∙' q ∙ sym (~r) ∙
         (~r  ∙ (λ i → r (i ∧ ~ i)) ∙
              (r ∙ ((λ i → r (i ∨  ~ i))) ∙  s )))
      ≡ (λ i → sq i (~ i)) ∙ (q ∙ refl ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


 _ = solvePaths



module _ {ℓ} where

 data D : Type ℓ where
  x y z w : D
  p : x ≡ y
  q : y ≡ z
  f : D → D
  r : f z ≡ f w


 _ : Square
         (cong f (p ∙ q)) (cong f q ∙ r)
         (cong f p) r
 _ = solvePaths



module CongCoherent (f : A → B) (SA : NPath 4 A) where
 open NPath SA

 LHS RHS : 𝑣₀ ≡ 𝑣₄
 LHS = (𝑝₀ ∙ refl ∙ 𝑝₁) ∙ (𝑝₂ ∙ refl ∙ 𝑝₃)
 RHS = 𝑝₀ ∙∙ (𝑝₁ ∙∙ refl ∙∙ 𝑝₂) ∙∙ 𝑝₃

 solve[cong] cong[solve] : cong f LHS ≡ cong f RHS

 solve[cong] = solvePaths

 cong[solve] = cong (cong f) solvePaths

 _ : cong[solve] ≡ solve[cong]
 _ = solvePaths
