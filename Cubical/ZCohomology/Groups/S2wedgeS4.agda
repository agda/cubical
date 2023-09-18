{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.S2wedgeS4 where

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
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.RingStructure.CupProduct




S²⋁S⁴ : Type₀
S²⋁S⁴ = (S₊∙ 2) ⋁ (S₊∙ 4)

------------- H⁰(S²⋁S⁴) ------------
H⁰-S²⋁S⁴≅ℤ : GroupIso (coHomGr 0 S²⋁S⁴) ℤGroup
H⁰-S²⋁S⁴≅ℤ = H⁰-connected (inl north) (wedgeConnected _ _ (Sn-connected 1) (Sn-connected 3))

------------- H¹(S²⋁S⁴) ------------
H¹-S²⋁S⁴≅0 : GroupIso (coHomGr 1 S²⋁S⁴) UnitGroup₀
H¹-S²⋁S⁴≅0 = (Hⁿ-⋁ _ _ 0)
              □ ((GroupIsoDirProd (Hⁿ-Sᵐ 1 2) (Hⁿ-Sᵐ 1 4))
              □ lUnitGroupIso)

------------- H²(S²⋁S⁴) ------------
H²-S²⋁S⁴≅ℤ : GroupIso (coHomGr 2 S²⋁S⁴) ℤGroup
H²-S²⋁S⁴≅ℤ = (Hⁿ-⋁ _ _ 1)
              □ ((GroupIsoDirProd (Hⁿ-Sᵐ 2 2) (Hⁿ-Sᵐ 2 4))
              □ rUnitGroupIso)

------------- H³(S²⋁S⁴) ------------
H³-S²⋁S⁴≅0 : GroupIso (coHomGr 3 S²⋁S⁴) UnitGroup₀
H³-S²⋁S⁴≅0 = (Hⁿ-⋁ _ _ 2)
              □ ((GroupIsoDirProd (Hⁿ-Sᵐ 3 2) (Hⁿ-Sᵐ 3 4))
              □ lUnitGroupIso)

------------- H⁴(S²⋁S⁴) ------------
H⁴-S²⋁S⁴≅ℤ : GroupIso (coHomGr 4 S²⋁S⁴) ℤGroup
H⁴-S²⋁S⁴≅ℤ = (Hⁿ-⋁ _ _ 3)
              □ ((GroupIsoDirProd (Hⁿ-Sᵐ 4 2) (Hⁿ-Sᵐ 4 4))
              □ lUnitGroupIso)

------------- Hⁿ(S²⋁S⁴) for n ≥ 5 ------------
Hⁿ-S²⋁S⁴≅0 : (n : ℕ) → GroupIso (coHomGr (5 + n) S²⋁S⁴) UnitGroup₀
Hⁿ-S²⋁S⁴≅0 n = (Hⁿ-⋁ _ _ (4 + n))
               □ ((GroupIsoDirProd (Hⁿ-Sᵐ (5 + n) 2) (Hⁿ-Sᵐ (5 + n) 4))
               □ lUnitGroupIso)

------------- Hⁿ(S²⋁S⁴) for n ≠ 0, ≠ 2 and ≠ 4 ------------
Hⁿ-S²⋁S⁴≅0-bis : (n : ℕ) → (n ≡ 0 → ⊥) × ((n ≡ 2 → ⊥) × (n ≡ 4 → ⊥))
                → GroupIso (coHomGr n S²⋁S⁴) UnitGroup₀
Hⁿ-S²⋁S⁴≅0-bis zero (¬p , ¬q , ¬r) = ⊥.rec (¬p refl)
Hⁿ-S²⋁S⁴≅0-bis (suc zero) (¬p , ¬q , ¬r) = H¹-S²⋁S⁴≅0
Hⁿ-S²⋁S⁴≅0-bis (suc (suc zero)) (¬p , ¬q , ¬r) = ⊥.rec (¬q refl)
Hⁿ-S²⋁S⁴≅0-bis (suc (suc (suc zero))) (¬p , ¬q , ¬r) = H³-S²⋁S⁴≅0
Hⁿ-S²⋁S⁴≅0-bis (suc (suc (suc (suc zero)))) (¬p , ¬q , ¬r) = ⊥.rec (¬r refl)
Hⁿ-S²⋁S⁴≅0-bis (suc (suc (suc (suc (suc n))))) (¬p , ¬q , ¬r) = Hⁿ-S²⋁S⁴≅0 n


------------- Cup product is null for H² ------------

open Iso
open IsGroupHom

null-H² : (a b : ℤ) → (inv (fst H²-S²⋁S⁴≅ℤ) a) ⌣ (inv (fst H²-S²⋁S⁴≅ℤ) b) ≡ 0ₕ 4
null-H² a b = sym (leftInv (fst H⁴-S²⋁S⁴≅ℤ) _)
              ∙ cong (inv (fst H⁴-S²⋁S⁴≅ℤ)) refl
              ∙ pres1 (snd (invGroupIso H⁴-S²⋁S⁴≅ℤ))
