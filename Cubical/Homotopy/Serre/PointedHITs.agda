{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.PointedHITs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.HITs.Susp
open import Cubical.HITs.S1

private
  variable
    ℓ : Level

-- Generalities

-- Σ and Σ∙ are taken
S∙ : Pointed ℓ → Pointed ℓ
S∙ A = Susp∙ (typ A)

S∙→ : {X Y : Pointed ℓ} → (X →∙ Y) → (S∙ X →∙ S∙ Y)
S∙→ f = suspFun (fst f) , refl

S¹∙ : Pointed _
S¹∙ = ( S¹ , base )
