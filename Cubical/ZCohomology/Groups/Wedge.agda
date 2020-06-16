{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (elim to sElim)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₋₁)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.HITs.Pushout

--- This module contains a proof that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B), n ≥ 1

private
  variable
    ℓ : Level
    A B : Pointed ℓ

private
  Δ : (n : ℕ) → morph (×coHomGr n (typ A) (typ B)) (coHomGr n Unit)
  Δ {A = A} {B = B} = MV.Δ (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)
  d : (n : ℕ) → morph (coHomGr n Unit) (coHomGr (suc n) (A ⋁ B))
  d {A = A} {B = B} = MV.d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)
  i : (n : ℕ) → morph (coHomGr n (A ⋁ B)) (×coHomGr n (typ A) (typ B))
  i {A = A} {B = B} = MV.i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)



private
  H¹-⋁'' : Iso'' (coHomGr 1 (A ⋁ B)) (×coHomGr 1 (typ A) (typ B))
  Iso''.ϕ (H¹-⋁'' {A = A} {B = B}) = (MV.i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 1)
  Iso''.inj (H¹-⋁'' {A = A} {B = B}) = -- Requires a "useless" elimination to terminate
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ f inker → helper ∣ f ∣₀ (MV.Ker-i⊂Im-d _ _ Unit (λ _ → pt A) (λ _ → pt B) 0 ∣ f ∣₀ inker)
    where
    surj-helper : (x : coHom 0 Unit)
            → isInIm (×coHomGr 0 (typ A) (typ B)) (coHomGr 0 Unit) (Δ {A = A} {B = B} 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
            λ f → ∣ (∣ (λ _ → f tt) ∣₀ , 0ₕ) , cong ∣_∣₀ (funExt (λ _ → cong ((f tt) +ₖ_) -0ₖ ∙ rUnitₖ (f tt))) ∣₋₁

    helper : (x : coHom 1 (A ⋁ B)) → isInIm (coHomGr 0 Unit) (coHomGr 1 _) (d {A = A} {B = B} 0) x
                  → x ≡ 0ₕ
    helper x inim =
      pRec (setTruncIsSet _ _)
           (λ p → sym (snd p) ∙
                       MV.Im-Δ⊂Ker-d _ _ Unit (λ _ → pt A) (λ _ → pt B) 0 (fst p) (surj-helper (fst p)))
             inim
  Iso''.surj (H¹-⋁'' {A = A} {B = B}) x = MV.Ker-Δ⊂Im-i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 1 x
                                                        (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)

Hⁿ-⋁ : (n : ℕ) → grIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
Hⁿ-⋁ zero = Iso''→Iso H¹-⋁''
Hⁿ-⋁ {A = A} {B = B} (suc n) =
  SES→Iso (coHomGr (suc n) Unit)
           (coHomGr (suc (suc n)) Unit)
           (ses
             (isOfHLevelSuc 0 (isContrHⁿ-Unit n))
             (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)))
             (d (suc n))
             (Δ {A = A} {B = B} (suc (suc n)))
             (i {A = A} {B = B} (suc (suc n)))
             (MV.Ker-i⊂Im-d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) (suc n))
             (MV.Ker-Δ⊂Im-i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) (suc (suc n))))
