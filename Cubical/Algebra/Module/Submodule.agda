{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Submodule where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Module
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ ℓ' : Level

module _ (R : Ring ℓ) (M : LeftModule R ℓ') where
  open ModuleTheory R M
  open LeftModuleStr (snd M)
  private
    module R = RingStr (snd R)

  record isSubmodule (N : ℙ (⟨ M ⟩)) : Type (ℓ-max ℓ ℓ') where
    field
      +-closed : {x y : ⟨ M ⟩} → x ∈ N → y ∈ N → x + y ∈ N
      0r-closed : 0m ∈ N
      ·-closedLeft :  {x : ⟨ M ⟩} (r : ⟨ R ⟩) → x ∈ N → r ⋆ x ∈ N

    -closed : {x : ⟨ M ⟩} → x ∈ N → - x ∈ N
    -closed {x = x} x∈N =
      subst (_∈ N)
            (((R.- R.1r) ⋆ x) ≡⟨ minusByMult x ⟩
              (- x) ∎)
            (·-closedLeft (R.- R.1r) x∈N)
