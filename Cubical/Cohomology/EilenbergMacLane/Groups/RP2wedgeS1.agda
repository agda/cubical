{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.RP2wedgeS1 where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.Groups.Wedge

open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.RPn
open import Cubical.HITs.Wedge

open AbGroupStr

{- Todo: fix type-checking (very slow right now) -}

H⁰[RP²∨S¹,ℤ/2]≅ℤ/2 :
  AbGroupEquiv (coHomGr zero ℤ/2 ((RP² , point) ⋁ S₊∙ 1))
               ℤ/2
H⁰[RP²∨S¹,ℤ/2]≅ℤ/2 =
  H⁰conn (∣ inl point ∣
        , TR.elim (λ x → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
           (PO.elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
             (elimPropRP² (λ _ → isOfHLevelTrunc 2 _ _) refl)
             (toPropElim (λ _ → isOfHLevelTrunc 2 _ _) (cong ∣_∣ₕ (push tt)))))
        ℤ/2

H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2 :
  AbGroupEquiv (coHomGr 1 ℤ/2 ((RP² , point) ⋁ S₊∙ 1))
               (dirProdAb ℤ/2 ℤ/2)
H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2 =
  compGroupEquiv (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 0)
    (GroupEquivDirProd
      H¹[RP²,ℤ/2]≅ℤ/2
      (H¹[S¹,G]≅G ℤ/2))

H²[RP²∨S¹,ℤ/2]≅ℤ/2 :
  AbGroupEquiv (coHomGr 2 ℤ/2 ((RP² , point) ⋁ S₊∙ 1))
               ℤ/2
H²[RP²∨S¹,ℤ/2]≅ℤ/2 =
  compGroupEquiv (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 1)
    (compGroupEquiv
      (GroupEquivDirProd
        H²[RP²,ℤ/2]≅ℤ/2
        (compGroupEquiv (Hᵐ⁺ⁿ[Sⁿ,G]≅0 ℤ/2 0 0)
          (contrGroupEquivUnit
           {G = AbGroup→Group (trivialAbGroup {ℓ-zero})} isContrUnit*)))
      (GroupIso→GroupEquiv (rUnitGroupIso {G = AbGroup→Group ℤ/2})))

H³⁺ⁿ[RP²∨S¹,ℤ/2]≅Unit : (n : ℕ)
  → AbGroupEquiv (coHomGr (3 +ℕ n) ℤ/2 ((RP² , point) ⋁ S₊∙ 1))
                  (UnitAbGroup {ℓ = ℓ-zero})
H³⁺ⁿ[RP²∨S¹,ℤ/2]≅Unit n =
  compGroupEquiv (Hⁿ-⋁≅Hⁿ×Hⁿ ℤ/2 (2 +ℕ n))
    (compGroupEquiv
      (GroupEquivDirProd
        (H³⁺ⁿ[RP²,G]≅G n ℤ/2)
        (compGroupEquiv
        (subst (GroupEquiv _)
          (cong (λ n → AbGroup→Group (coHomGr n ℤ/2 S¹))
            (cong (suc ∘ suc) (cong suc (+-comm 0 n) ∙ sym (+-suc n 0))))
          idGroupEquiv)
        (Hᵐ⁺ⁿ[Sⁿ,G]≅0 ℤ/2 0 (suc n))))
      (GroupIso→GroupEquiv
        ((iso (λ {(x , y) → tt*}) (λ x → (tt* , tt*))
          (λ { (lift lower₁) → refl })
         λ {(lift l , lift l2) → refl})
        , makeIsGroupHom λ _ _ → refl)))
