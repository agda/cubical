{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.pathComp.Groups2.Connected where

open import Cubical.ZCohomology.pathComp.Base
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.Groups2.Unit
open import Cubical.ZCohomology.pathComp.EilenbergIso

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

  H⁰-connected-type : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom' 0 A) Int
  H⁰-connected-type {A = A} a con = compIso helper IsoLoopK₀Int
    where
    helper : Iso (coHom' 0 A) (loopK 0)
    Iso.fun helper = sRec (isOfHLevelTrunc 3 _ _) λ f → f a
    Iso.inv helper b = ∣ (λ x → b) ∣₂
    Iso.rightInv helper _ = refl
    Iso.leftInv helper =
      sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
            λ f → cong ∣_∣₂ (funExt λ x → trRec (isOfHLevelTrunc 3 _ _ _ _) (cong f) (isConnectedPath 1 con a x .fst))

H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → GroupIso (coHomGr 0 A) intGroup
H⁰-connected a con = Iso+Hom→GrIso (H⁰-connected-type a con)
                     (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ f g → addLemma (f a) (g a))
