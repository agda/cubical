{-# OPTIONS --lossy-unification #-}
module Cubical.ZCohomology.Groups.RP2wedgeS1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.RPn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.RP2
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.RingStructure.CupProduct




RP²⋁S¹ : Type₀
RP²⋁S¹ = (RP² , point) ⋁ (S₊∙ 1)

------------- H⁰(RP²⋁S¹) ------------
H⁰-RP²⋁S¹≅ℤ : GroupIso (coHomGr 0 RP²⋁S¹) ℤGroup
H⁰-RP²⋁S¹≅ℤ = H⁰-connected (inl point) (wedgeConnected _ _ connectedRP¹ (Sn-connected 0))

------------- H¹(RP²⋁S¹) ------------
H¹-RP²⋁S¹≅ℤ : GroupIso (coHomGr 1 RP²⋁S¹) ℤGroup
H¹-RP²⋁S¹≅ℤ = (Hⁿ-⋁ _ _ 0)
              □ ((GroupIsoDirProd H¹-RP²≅0 (Hⁿ-Sᵐ 1 1))
              □ lUnitGroupIso)

-- ------------- H²(RP²⋁S¹) ------------
H²-RP²⋁S¹≅Bool : GroupIso (coHomGr 2 RP²⋁S¹) BoolGroup
H²-RP²⋁S¹≅Bool = (Hⁿ-⋁ _ _ 1)
                 □ ((GroupIsoDirProd H²-RP²≅Bool (Hⁿ-Sᵐ 2 1))
                 □ rUnitGroupIso)

------------- Hⁿ(RP²⋁S¹) for n ≥ 3 ------------
Hⁿ-RP²⋁S¹≅0 : (n : ℕ) → GroupIso (coHomGr (3 + n) RP²⋁S¹) UnitGroup₀
Hⁿ-RP²⋁S¹≅0 n = (Hⁿ-⋁ _ _ (2 + n))
               □ ((GroupIsoDirProd (Hⁿ-RP²≅0 n) (Hⁿ-Sᵐ (3 + n) 1))
               □ lUnitGroupIso)

------------- Cup product is null for H² ------------

open Iso
open IsGroupHom

α : coHom 1 RP²⋁S¹
α = ∣ (λ { (inl x) → ∣ base ∣
         ; (inr x) → ∣ x ∣
         ; (push a i) → ∣ base ∣ }) ∣₂

α↦1 : Iso.fun (fst H¹-RP²⋁S¹≅ℤ) α ≡ 1
α↦1 = refl

1↦α : Iso.inv (fst H¹-RP²⋁S¹≅ℤ) 1 ≡ α
1↦α = cong (Iso.inv (fst H¹-RP²⋁S¹≅ℤ)) (sym α↦1)
       ∙ leftInv (fst H¹-RP²⋁S¹≅ℤ) α

-- computes !
lem-α²≡0 : Iso.fun (fst H²-RP²⋁S¹≅Bool) (α ⌣ α) ≡ true
lem-α²≡0 = refl

α²≡0 : α ⌣ α ≡ 0ₕ 2
α²≡0 = sym (leftInv (fst H²-RP²⋁S¹≅Bool) (α ⌣ α))
       ∙ cong (Iso.inv (fst H²-RP²⋁S¹≅Bool)) lem-α²≡0
       ∙ pres1 (snd (invGroupIso H²-RP²⋁S¹≅Bool))

trivial-cup : Iso.inv (fst H¹-RP²⋁S¹≅ℤ) 1 ⌣ Iso.inv (fst H¹-RP²⋁S¹≅ℤ) 1 ≡ 0ₕ 2
trivial-cup = cong₂ _⌣_ 1↦α 1↦α ∙ α²≡0
