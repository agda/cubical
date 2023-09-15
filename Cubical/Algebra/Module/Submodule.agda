{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Submodule where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit

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

  record isSubmodule (N : ℙ ⟨ M ⟩) : Type (ℓ-max ℓ ℓ') where
    field
      +-closed : {x y : ⟨ M ⟩} → x ∈ N → y ∈ N → x + y ∈ N
      0r-closed : 0m ∈ N
      ⋆-closed :  {x : ⟨ M ⟩} (r : ⟨ R ⟩) → x ∈ N → r ⋆ x ∈ N

    -closed : {x : ⟨ M ⟩} → x ∈ N → - x ∈ N
    -closed {x = x} x∈N =
      subst (_∈ N)
            (((R.- R.1r) ⋆ x) ≡⟨ minusByMult x ⟩
              (- x) ∎)
            (⋆-closed (R.- R.1r) x∈N)

  Submodule : Type _
  Submodule = Σ[ N ∈ ℙ ⟨ M ⟩ ] isSubmodule N

  open isSubmodule

  zeroSubmodule : Submodule
  fst zeroSubmodule x = (x ≡ 0m) , is-set x 0m
  +-closed  (snd zeroSubmodule) x≡0 y≡0 = (λ i → x≡0 i + y≡0 i) ∙ +IdL 0m
  0r-closed (snd zeroSubmodule)         = refl
  ⋆-closed  (snd zeroSubmodule) r x≡0   = (λ i → r ⋆ x≡0 i) ∙ ⋆AnnihilR r

  allSubmodule : Submodule
  fst allSubmodule x = Unit* , isOfHLevelUnit* 1
  +-closed  (snd allSubmodule) _ _ = tt*
  0r-closed (snd allSubmodule)     = tt*
  ⋆-closed  (snd allSubmodule) _ _ = tt*
