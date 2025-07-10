{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.FinitePresentation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup

private
  variable
    ℓ : Level

record FinitePresentation (A : AbGroup ℓ) : Type ℓ where
  field
    nGens : ℕ
    nRels : ℕ
    rels : AbGroupHom ℤ[Fin nRels ] ℤ[Fin nGens ]
    fpiso : GroupIso (AbGroup→Group A)
                     (AbGroup→Group ℤ[Fin nGens ]
                       / imNormalSubgroup rels
                          (λ f g → funExt (λ x → +Comm (f x) (g x))))

isFinitelyPresented : AbGroup ℓ → Type ℓ
isFinitelyPresented G = ∥ FinitePresentation G ∥₁
