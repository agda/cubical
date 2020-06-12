{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Groups.Unit where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; +-comm)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.GroupLibrary
open import Cubical.ZCohomology.coHomZero-map

H⁰-Unit≃ℤ : grIso (coHomGr 0 Unit) intGroup
grIso.fun H⁰-Unit≃ℤ = mph (sRec isSetInt (λ f → f tt))
                             (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
                                     (λ a b → addLemma (a tt) (b tt)))
grIso.inv H⁰-Unit≃ℤ = mph (λ a → ∣ (λ _ → a) ∣₀) (λ a b i → ∣ (λ _ → addLemma a b (~ i)) ∣₀)
grIso.rightInv H⁰-Unit≃ℤ a = refl
grIso.leftInv H⁰-Unit≃ℤ = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl



isContrHⁿ-Unit : (n : ℕ) → isContr (coHom (suc n) Unit)
isContrHⁿ-Unit n = subst isContr (λ i → ∥ UnitToTypeId (coHomK (suc n)) (~ i) ∥₀) (helper' n)
  where
  helper' : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₀)
  helper' n =
    subst isContr
      ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n)))
         ∙ sym propTrunc≡Trunc0 ∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₀)
      (isConnectedSubtr 2 (helper2 n .fst)
        (subst (λ x → isHLevelConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
    where
    helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
    helper2 zero = 0 , refl
    helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)


{- Hⁿ(Unit) for n ≥ 1 -}
Hⁿ-Unit≃0 : (n : ℕ) → grIso (coHomGr (suc n) Unit) trivialGroup
grIso.fun (Hⁿ-Unit≃0 n) = mph (λ _ → tt)
                              (λ _ _ → refl)
grIso.inv (Hⁿ-Unit≃0 n) = mph (λ _ → ∣ (λ _ → ∣ north ∣) ∣₀)
                              (λ _ _ → sym (rUnitₕ 0ₕ))
grIso.rightInv (Hⁿ-Unit≃0 n) _ = refl
grIso.leftInv (Hⁿ-Unit≃0 n) _ = isOfHLevelSuc 0 (isContrHⁿ-Unit n) _ _


{- Hⁿ for arbitrary contractible types -}
Hⁿ-contrType≃0 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → grIso (coHomGr (suc n) A) trivialGroup
Hⁿ-contrType≃0 {A = A} n contr =
  Iso'→Iso
    (iso'
      (iso (λ _ → tt)
           (λ _ → 0ₕ)
           (λ _ → refl)
           λ a → isOfHLevelSuc 0 helper _ _)
      λ _ _ → refl)
  where
  helper1 : Iso (coHom (suc n) A) (coHom (suc n) Unit)
  helper1 = compIso (setTruncIso (ContrToTypeIso contr))
                    (setTruncIso (symIso (ContrToTypeIso isContrUnit)))

  helper : isContr (coHom (suc n) A)
  helper = (Iso.inv helper1 0ₕ)
          , λ y → cong (Iso.inv helper1) (isOfHLevelSuc 0 (isContrHⁿ-Unit n) 0ₕ (Iso.fun helper1 y) )
          ∙ Iso.leftInv helper1 y
