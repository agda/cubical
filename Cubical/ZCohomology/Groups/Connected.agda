module Cubical.ZCohomology.Groups.Connected where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +Comm to +ℤ-comm ; +Assoc to +ℤ-assoc)
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.Nullification

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Homotopy.Connected

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Unit

private
  H⁰-connected-type : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom 0 A) ℤ
  Iso.fun (H⁰-connected-type a con) = ST.rec isSetℤ λ f → f a
  Iso.inv (H⁰-connected-type a con) b = ∣ (λ x → b) ∣₂
  Iso.rightInv (H⁰-connected-type a con) b = refl
  Iso.leftInv (H⁰-connected-type a con) =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
           λ f → cong ∣_∣₂ (funExt λ x → T.rec₊ (isSetℤ _ _) (cong f) (isConnectedPath 1 con a x .fst))

open IsGroupHom
open Iso

H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → ((x : A) → ∥ a ≡ x ∥₁) → GroupIso (coHomGr 0 A) ℤGroup
fun (fst (H⁰-connected a con)) = ST.rec isSetℤ (λ f → f a)
inv (fst (H⁰-connected a con)) b = ∣ (λ _ → b) ∣₂
rightInv (fst (H⁰-connected a con)) _ = refl
leftInv (fst (H⁰-connected a con)) =
  ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _))
        (λ f → cong ∣_∣₂ (funExt λ x → PT.rec (isSetℤ _ _) (cong f) (con x)))
snd (H⁰-connected a con) = makeIsGroupHom (ST.elim2 (λ _ _ → isProp→isSet (isSetℤ _ _)) λ x y → refl)
