{-# OPTIONS --lossy-unification #-}
module Cubical.Tactics.CategorySolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Quiver.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
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
  private
    W𝓒 = FreeCat (Cat→Quiver 𝓒)
  sem𝓒 = ε {𝓒 = 𝓒}
  ⟦_⟧c = sem𝓒 .F-hom
  𝓟 = PowerCategory (W𝓒 .ob) (SET (ℓ-max ℓ ℓ'))
  𝓘 : Functor W𝓒 𝓟
  𝓘 = PseudoYoneda {C = W𝓒}

  -- Semantics in 𝓟 (𝓒 .ob), interpreting fun symbols using Yoneda
  semYo : Functor W𝓒 𝓟
  semYo = rec _ (record {
    _$g_ = 𝓘 .F-ob
    ; _<$g>_ = λ e → 𝓘 .F-hom (FreeCat.η (Cat→Quiver 𝓒) <$g> e)
    })

  -- | Evaluate by taking the semantics in 𝓟 (𝓒 .ob)
  eval : ∀ {A B} → W𝓒 [ A , B ] → _
  eval {A}{B} e = semYo .F-hom e

--   -- Evaluation agrees with the Yoneda embedding, and so is fully faithful
  Yo-YoSem-agree : 𝓘 ≡ semYo
  Yo-YoSem-agree = FreeCatFunctor≡ _ _ _ (record
    { _$gᴰ_ = λ _ → refl
    ; _<$g>ᴰ_ = λ _ → refl
    })

  -- If two expressions in the free category are equal when evaluated
  -- in 𝓟 (𝓒 .ob), then they are equal, and so are equal when
  -- evaluated in 𝓒.
  solve : ∀ {A B} → (e₁ e₂ : W𝓒 [ A , B ])
        → eval e₁ ≡ eval e₂
        → ⟦ e₁ ⟧c ≡ ⟦ e₂ ⟧c
  solve {A}{B} e₁ e₂ p = cong ⟦_⟧c (isFaithfulPseudoYoneda {C = W𝓒} _ _ _ _ lem) where
    lem : 𝓘 ⟪ e₁ ⟫ ≡ 𝓘 ⟪ e₂ ⟫
    lem = transport
            (λ i → Yo-YoSem-agree (~ i) ⟪ e₁ ⟫ ≡ Yo-YoSem-agree (~ i) ⟪ e₂ ⟫)
            p

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : FreeCat (Cat→Quiver 𝓒) [ A , B ])
      → (p : Eval.eval 𝓒 e₁ ≡ Eval.eval 𝓒 e₂)
      → _
solve = Eval.solve
