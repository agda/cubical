module Cubical.Categories.Instances.Opposite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Isomorphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open isUnivalent

module _ {C : Category ℓC ℓC'} (isUnivC : isUnivalent C) where
  op-Iso-pathToIso : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p
  op-Iso-pathToIso =
    J (λ y p → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p)
      (CatIso≡ _ _ refl)

  op-Iso⁻-pathToIso : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso⁻ (pathToIso {C = C ^op} p) ≡ pathToIso {C = C} p
  op-Iso⁻-pathToIso =
    J (λ _ p → op-Iso⁻ (pathToIso p) ≡ pathToIso p) (CatIso≡ _ _ refl)

  isUnivalentOp : isUnivalent (C ^op)
  isUnivalentOp .univ x y = isIsoToIsEquiv
    ( (λ f^op → CatIsoToPath isUnivC (op-Iso⁻ f^op))
    , (λ f^op → CatIso≡ _ _
      (cong fst (cong op-Iso (secEq (univEquiv isUnivC _ _) (op-Iso⁻ f^op)))))
    , λ p →
        cong (CatIsoToPath isUnivC) (op-Iso⁻-pathToIso p)
        ∙ retEq (univEquiv isUnivC _ _) p)
