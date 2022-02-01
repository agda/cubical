{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.Connected where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Int hiding (ℤ) renaming (_+_ to _+ℤ_; +Comm to +ℤ-comm ; +Assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (rec₊ to trRec)
open import Cubical.Algebra.Group

open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Equiv

private
  H⁰-connected-type : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom 0 A) (fst ℤ)
  Iso.fun (H⁰-connected-type a con) = sRec isSetℤ λ f → f a
  Iso.inv (H⁰-connected-type a con) b = ∣ (λ x → b) ∣₂
  Iso.rightInv (H⁰-connected-type a con) b = refl
  Iso.leftInv (H⁰-connected-type a con) =
    sElim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
           λ f → cong ∣_∣₂ (funExt λ x → trRec (isSetℤ _ _) (cong f) (isConnectedPath 1 con a x .fst))

open IsGroupHom
open Iso

H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₁) → GroupIso (coHomGr 0 A) ℤ
fun (fst (H⁰-connected a con)) = sRec isSetℤ (λ f → f a)
inv (fst (H⁰-connected a con)) b = ∣ (λ _ → b) ∣₂
rightInv (fst (H⁰-connected a con)) _ = refl
leftInv (fst (H⁰-connected a con)) =
  sElim (λ _ → isProp→isSet (isSetSetTrunc _ _))
        (λ f → cong ∣_∣₂ (funExt λ x → pRec (isSetℤ _ _) (cong f) (con x)))
snd (H⁰-connected a con) = makeIsGroupHom (sElim2 (λ _ _ → isProp→isSet (isSetℤ _ _)) λ x y → refl)
