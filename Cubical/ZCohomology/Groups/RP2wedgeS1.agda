{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.RP2wedgeS1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
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

-- ------------- H¹(RP²⋁S¹) ------------
-- H¹-RP²⋁S¹≅0 : GroupIso (coHomGr 1 RP²⋁S¹) UnitGroup₀
-- H¹-RP²⋁S¹≅0 = (Hⁿ-⋁ _ _ 0)
--               □ ((GroupIsoDirProd (Hⁿ-Sᵐ 1 2) (Hⁿ-Sᵐ 1 4))
--               □ lUnitGroupIso)

-- ------------- H²(RP²⋁S¹) ------------
-- H²-RP²⋁S¹≅ℤ : GroupIso (coHomGr 2 RP²⋁S¹) ℤGroup
-- H²-RP²⋁S¹≅ℤ = (Hⁿ-⋁ _ _ 1)
--               □ ((GroupIsoDirProd (Hⁿ-Sᵐ 2 2) (Hⁿ-Sᵐ 2 4))
--               □ rUnitGroupIso)

-- ------------- H³(RP²⋁S¹) ------------
-- H³-RP²⋁S¹≅0 : GroupIso (coHomGr 3 RP²⋁S¹) UnitGroup₀
-- H³-RP²⋁S¹≅0 = (Hⁿ-⋁ _ _ 2)
--               □ ((GroupIsoDirProd (Hⁿ-Sᵐ 3 2) (Hⁿ-Sᵐ 3 4))
--               □ lUnitGroupIso)

-- ------------- H⁴(RP²⋁S¹) ------------
-- H⁴-RP²⋁S¹≅ℤ : GroupIso (coHomGr 4 RP²⋁S¹) ℤGroup
-- H⁴-RP²⋁S¹≅ℤ = (Hⁿ-⋁ _ _ 3)
--               □ ((GroupIsoDirProd (Hⁿ-Sᵐ 4 2) (Hⁿ-Sᵐ 4 4))
--               □ lUnitGroupIso)

-- ------------- Hⁿ(RP²⋁S¹) for n ≥ 5 ------------
-- Hⁿ-RP²⋁S¹≅0 : (n : ℕ) → GroupIso (coHomGr (5 + n) RP²⋁S¹) UnitGroup₀
-- Hⁿ-RP²⋁S¹≅0 n = (Hⁿ-⋁ _ _ (4 + n))
--                □ ((GroupIsoDirProd (Hⁿ-Sᵐ (5 + n) 2) (Hⁿ-Sᵐ (5 + n) 4))
--                □ lUnitGroupIso)

-- ------------- Hⁿ(RP²⋁S¹) for n ≠ 0, ≠ 2 and ≠ 4 ------------
-- Hⁿ-RP²⋁S¹≅0-bis : (n : ℕ) → (n ≡ 0 → ⊥) × ((n ≡ 2 → ⊥) × (n ≡ 4 → ⊥))
--                 → GroupIso (coHomGr n RP²⋁S¹) UnitGroup₀
-- Hⁿ-RP²⋁S¹≅0-bis zero (¬p , ¬q , ¬r) = ⊥.rec (¬p refl)
-- Hⁿ-RP²⋁S¹≅0-bis (suc zero) (¬p , ¬q , ¬r) = H¹-RP²⋁S¹≅0
-- Hⁿ-RP²⋁S¹≅0-bis (suc (suc zero)) (¬p , ¬q , ¬r) = ⊥.rec (¬q refl)
-- Hⁿ-RP²⋁S¹≅0-bis (suc (suc (suc zero))) (¬p , ¬q , ¬r) = H³-RP²⋁S¹≅0
-- Hⁿ-RP²⋁S¹≅0-bis (suc (suc (suc (suc zero)))) (¬p , ¬q , ¬r) = ⊥.rec (¬r refl)
-- Hⁿ-RP²⋁S¹≅0-bis (suc (suc (suc (suc (suc n))))) (¬p , ¬q , ¬r) = Hⁿ-RP²⋁S¹≅0 n


-- ------------- Cup product is null for H² ------------

-- open Iso
-- open IsGroupHom

-- null-H² : (a b : ℤ) → (inv (fst H²-RP²⋁S¹≅ℤ) a) ⌣ (inv (fst H²-RP²⋁S¹≅ℤ) b) ≡ 0ₕ 4
-- null-H² a b = sym (leftInv (fst H⁴-RP²⋁S¹≅ℤ) _)
--               ∙ cong (inv (fst H⁴-RP²⋁S¹≅ℤ)) refl
--               ∙ pres1 (snd (invGroupIso H⁴-RP²⋁S¹≅ℤ))
