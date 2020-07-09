{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Connected where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit
open import Cubical.Structures.Group

open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Equiv

private
  H⁰-connected-type : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom 0 A) Int
  Iso.fun (H⁰-connected-type a con) = sRec isSetInt λ f → f a
  Iso.inv (H⁰-connected-type a con) b = ∣ (λ x → b) ∣₂
  Iso.rightInv (H⁰-connected-type a con) b = refl
  Iso.leftInv (H⁰-connected-type a con) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ f → cong ∣_∣₂ (funExt λ x → trRec (isSetInt _ _) (cong f) (isConnectedPath 1 con a x .fst))

 
-- H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → GroupEquiv (coHomGr 0 A) intGroup
-- H⁰-connected {A = A} a con = invGroupEquiv invEq'
--   where
--   invEq' : GroupEquiv intGroup (coHomGr 0 A)
--   GroupEquiv.eq invEq' = invEquiv (isoToEquiv (H⁰-connected-type a con))
--   GroupEquiv.isHom invEq' c d  = cong ∣_∣₂ (funExt λ _ → sym (addLemma c d))


H⁰-connected' : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₋₁) → GroupIso (coHomGr 0 A) intGroup
H⁰-connected' a con = invGroupIso Iso⁻
  where
  Iso⁻ : GroupIso _ _
  GroupHom.fun (GroupIso.map Iso⁻) b = ∣ (λ _ → b) ∣₂
  GroupHom.isHom (GroupIso.map Iso⁻) c d  = cong ∣_∣₂ (funExt λ _ → sym (addLemma c d))
  GroupIso.inv Iso⁻ = sRec isSetInt (λ f → f a)
  GroupIso.rightInv Iso⁻ = (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                  λ f → cong ∣_∣₂ (funExt λ x → pRec (isSetInt _ _) (cong f) (con x)))
  GroupIso.leftInv Iso⁻ _ = refl

H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₋₁) → GroupEquiv (coHomGr 0 A) intGroup
H⁰-connected a con = GrIsoToGrEquiv (H⁰-connected' a con)
