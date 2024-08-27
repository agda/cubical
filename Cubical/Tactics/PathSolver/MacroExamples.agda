{-
This module provides usage examples for the macros defined in `Cubical.Tactics.PathSolver.Macro`.
Usage of macros is documented in `Cubical.Tactics.PathSolver.Macro` module.
-}

{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.MacroExamples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.Path

open import Cubical.Tactics.PathSolver.Macro
open import Cubical.Tactics.Reflection.QuoteCubical


private
  variable
    ℓ : Level
    A B : Type ℓ



module _ (SA : NPath 3 A) (f : A → B) where
  open NPath SA

  f[assoc] : cong f 𝑝₀ ∙ cong f 𝑝₁ ∙ cong f 𝑝₂
              ≡ (cong f 𝑝₀ ∙ cong f 𝑝₁) ∙ cong f 𝑝₂
  f[assoc] i j = cong$ (f (assoc 𝑝₀ 𝑝₁ 𝑝₂ i j))


module _ (SA : NPath 6 A) (f : A → {A} → A → A) (g : A → A) (𝑝ₓ : g (NPath.𝑣₀ SA) ≡ g (NPath.𝑣₀ SA)) where
  open NPath SA

  p : f 𝑣₀ 𝑣₁ ≡ f 𝑣₃ 𝑣₆
  p i =  (f ((𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) i) {g ((𝑝₁ ∙' 𝑝₂) i)} ((𝑝₁ ∙∙ 𝑝₂ ∙∙ (𝑝₃ ∙∙ 𝑝₄ ∙∙ 𝑝₅)) i))


  _ :  (λ i → cong$ (p i))
        ≡
          (λ i → f (𝑝₀ i) {g (𝑝₁ i)} (𝑝₁ i))
      ∙∙  (λ i → f (𝑝₁ i) {g (𝑝₂ i)} (𝑝₂ i))
      ∙∙ ((λ i → f  𝑣₂    {g 𝑣₃}     (𝑝₃ i))
      ∙∙  (λ i → f (𝑝₂ i) {g 𝑣₃}     (𝑝₄ i))
      ∙∙   λ i → f  𝑣₃    {g 𝑣₃}     (𝑝₅ i))
  _ = refl

  cg² : ∀ {x y : A} → (x ≡ y) → g (g x) ≡ g (g y)
  cg² = congS (g ∘S g)

  cpf : Square (cong g 𝑝₀) (cong g (𝑝₀ ∙ 𝑝₁))
                refl          (cong g 𝑝₁)
  cpf i j = g (compPath-filler 𝑝₀ 𝑝₁ i j)

  cpf' : Square (cong g 𝑝₀) (cong g 𝑝₀ ∙ cong g 𝑝₁)
                 refl        (cong g 𝑝₁)
  cpf' i j = cong$ (cpf i j)


  cpf≡cpf' : Cube
              cpf cpf'
              _ _
              _ _
  cpf≡cpf' _ i j = cong$-fill (cpf i j)



  cpf2 : Square (cong g (𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)))
               (cong g ((𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)) ∙ cong g (𝑝₂ ∙ 𝑝₃)))
               refl (cg² (𝑝₂ ∙ 𝑝₃))
  cpf2 i j = g (compPath-filler (𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)) (cong g (𝑝₂ ∙ 𝑝₃)) i j)

  cpf2' : Square
              (cong g 𝑝ₓ ∙ cg² 𝑝₀ ∙ cg² 𝑝₁)
               ((cong g 𝑝ₓ ∙ cg² 𝑝₀ ∙ cg² 𝑝₁) ∙ cg² 𝑝₂ ∙ cg² 𝑝₃)
                refl
               (cg² 𝑝₂ ∙ cg² 𝑝₃)
  cpf2' i j = cong$ (cpf2 i j)


  cpf2≡cpf2' : Cube
              cpf2 cpf2'
              _ _
              _ _
  cpf2≡cpf2' _ i j = cong$-fill (cpf2 i j)



module _ (A : Type) (a : A) (p : a ≡ a)
         (s : Square p p p p)  where


 {-
  Examples below can be recreated by replacing the body of the definition with a hole,
  then placing the example macro call in that hole and executing `C-c C-m` in Emacs.
  (for h?' macro, result needs to be manually coppied from AgdaInfo buffer)

  results including holes are commented out to allow compilation of module
 -}


 -- -- h?' 1 ⁇
 -- c₀ : I → I → I → A
 -- c₀ i j k =
 --          hcomp (λ 𝒛₀ → λ {
 --            (j = i0)(i = i0) → {!!}
 --            ;(j = i0)(i = i1) → {!!}
 --            ;(j = i1)(i = i0) → {!!}
 --            ;(j = i1)(i = i1) → {!!}
 --            ;(k = i0)(i = i0) → {!!}
 --            ;(k = i0)(i = i1) → {!!}
 --            ;(k = i0)(j = i0) → {!!}
 --            ;(k = i0)(j = i1) → {!!}
 --            ;(k = i1)(i = i0) → {!!}
 --            ;(k = i1)(i = i1) → {!!}
 --            ;(k = i1)(j = i0) → {!!}
 --            ;(k = i1)(j = i1) → {!!}
 --             })
 --         (  {!!})


 -- h? 2 (s i (j ∧ k))
 c₁ : I → I → I → A
 c₁ i j k = hcomp
              (λ { 𝒛₀ (i = i0) → s i0 (j ∧ k)
                 ; 𝒛₀ (i = i1) → s i1 (j ∧ k)
                 ; 𝒛₀ (j = i0) → s i (i0 ∧ k)
                 ; 𝒛₀ (j = i1) → s i (i1 ∧ k)
                 ; 𝒛₀ (k = i0) → s i (j ∧ i0)
                 ; 𝒛₀ (k = i1) → s i (j ∧ i1)
                 })
              (s i (j ∧ k))

 -- -- h? (i ∨ ~ j ∨ (~ i ∧ j)) ⁇
 -- c₂ : I → I → I → A
 -- c₂ i j k = hcomp
 --              (λ { 𝒛₀ (i = i1) → _
 --                 ; 𝒛₀ (j = i0) → _
 --                 ; 𝒛₀ (i = i0) (j = i1) → _
 --                 })
 --              {!!}

 --  h?' (i ∨ ~ j ∨ (~ i ∧ j)) (s i (j ∧ k))
 c₃ : I → I → I → A
 c₃ i j k =
       hcomp (λ 𝒛₀ → λ {
            (i = i1)         → s i (j ∧ k)
            ;(j = i0)         → s i (j ∧ k)
            ;(j = i1)(i = i0) → s i (j ∧ k)
             })
         (  s i (j ∧ k))

