{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Tactics.CategorySolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.Category.Base
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.UnderlyingGraph

private
  variable
    ℓ ℓ' : Level
open Category
open Functor

module Eval (𝓒 : Category ℓ ℓ') where
  -- Semantics in 𝓒 itself, tautologically
  open FreeCategory (Cat→Graph 𝓒)
  sem𝓒 = ε {𝓒 = 𝓒}
  ⟦_⟧c = sem𝓒 .F-hom
  𝓟 = PowerCategory (𝓒 .ob) (SET (ℓ-max ℓ ℓ'))
  𝓘 : Functor FreeCat 𝓟
  𝓘 = PseudoYoneda {C = FreeCat}

  -- Semantics in 𝓟 (𝓒 .ob), interpreting fun symbols using Yoneda
  module YoSem = Semantics 𝓟 (𝓘 ∘Interp η)
  ⟦_⟧yo = YoSem.sem .F-hom

  -- | Evaluate by taking the semantics in 𝓟 (𝓒 .ob)
  eval : ∀ {A B} → FreeCat [ A , B ] → _
  eval {A}{B} e = ⟦ e ⟧yo

  -- Evaluation agrees with the Yoneda embedding, and so is fully faithful
  Yo-YoSem-agree : 𝓘 ≡ YoSem.sem
  Yo-YoSem-agree = YoSem.sem-uniq refl

  -- If two expressions in the free category are equal when evaluated
  -- in 𝓟 (𝓒 .ob), then they are equal, and so are equal when
  -- evaluated in 𝓒.
  solve : ∀ {A B} → (e₁ e₂ : FreeCat [ A , B ])
        → eval e₁ ≡ eval e₂
        → ⟦ e₁ ⟧c ≡ ⟦ e₂ ⟧c
  solve {A}{B} e₁ e₂ p = cong ⟦_⟧c (isFaithfulPseudoYoneda _ _ _ _ lem) where
    lem : 𝓘 ⟪ e₁ ⟫ ≡ 𝓘 ⟪ e₂ ⟫
    lem = transport
            (λ i → Yo-YoSem-agree (~ i) ⟪ e₁ ⟫ ≡ Yo-YoSem-agree (~ i) ⟪ e₂ ⟫)
            p

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : FreeCategory.FreeCat (Cat→Graph 𝓒) [ A , B ])
      → (p : Eval.eval 𝓒 e₁ ≡ Eval.eval 𝓒 e₂)
      → _
solve = Eval.solve
