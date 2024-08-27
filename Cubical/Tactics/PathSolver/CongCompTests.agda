{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.CongCompTests where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Tactics.PathSolver.Macro
open import Cubical.Tactics.PathSolver.Path
open import Cubical.Data.Nat



module _ {ℓ} {A : Type ℓ} (SA : NPath 5 A) (f : A → A → A) where

 open NPath SA

 p : f (f (𝑣 0) (𝑣 3)) (f (𝑣 3) (𝑣 1)) ≡
       f (f (𝑣 2) (𝑣 5)) (f (𝑣 5) (𝑣 3))
 p = (cong₂ f (cong₂ f (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ 𝑝₄)) (cong₂ f (𝑝₃ ∙ 𝑝₄) (𝑝₁ ∙ 𝑝₂)))



 _ : {!!}
 _ = cong! p
