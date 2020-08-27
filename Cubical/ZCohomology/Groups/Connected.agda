{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Connected where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (rec to trRec)
open import Cubical.Algebra.Group

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

private
  H⁰-connected' : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₁) → GroupIso (coHomGr 0 A) intGroup
  H⁰-connected' a con = invGroupIso Iso⁻
    where
    Iso⁻ : GroupIso _ _
    GroupHom.fun (GroupIso.map Iso⁻) b = ∣ (λ _ → b) ∣₂
    GroupHom.isHom (GroupIso.map Iso⁻) c d  = cong ∣_∣₂ (funExt λ _ → sym (addLemma c d))
    GroupIso.inv Iso⁻ = sRec isSetInt (λ f → f a)
    GroupIso.rightInv Iso⁻ = (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                    λ f → cong ∣_∣₂ (funExt λ x → pRec (isSetInt _ _) (cong f) (con x)))
    GroupIso.leftInv Iso⁻ _ = refl

H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₁) → GroupEquiv (coHomGr 0 A) intGroup
H⁰-connected a con = GrIsoToGrEquiv (H⁰-connected' a con)
