{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.pathComp.Groups2.Unit where

open import Cubical.ZCohomology.pathComp.Base
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.EilenbergIso
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation renaming (rec to tRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (+-comm) renaming (_+_ to _+ℤ_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Data.Unit
open import Cubical.Algebra.Group

-- H⁰(Unit)
open GroupHom
open GroupIso
H⁰-Unit≅ℤ : GroupIso (coHomGr 0 Unit) intGroup
fun (GroupIso.map H⁰-Unit≅ℤ) = sRec isSetInt λ f → Iso.fun IsoLoopK₀Int (f tt)
isHom (GroupIso.map H⁰-Unit≅ℤ) = sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ f g → addLemma (f tt) (g tt)
inv H⁰-Unit≅ℤ a = ∣ (λ _ → Iso.inv IsoLoopK₀Int a) ∣₂
rightInv H⁰-Unit≅ℤ a = Iso.rightInv IsoLoopK₀Int a
leftInv H⁰-Unit≅ℤ = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                          λ f → cong ∣_∣₂ (funExt λ _ → Iso.leftInv IsoLoopK₀Int (f tt))

{- Hⁿ(Unit) for n ≥ 1 -}
isContrHⁿ-Unit : (n : ℕ) → isContr (coHom' (suc n) Unit)
isContrHⁿ-Unit n = 
  isOfHLevelRetractFromIso 0
    (setTruncIso (UnitToTypeIso (loopK (suc n))))
    (is2ConnectedLoopK' n)

Hⁿ-Unit≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) Unit) trivialGroup
GroupHom.fun (GroupIso.map (Hⁿ-Unit≅0 n)) _ = _
GroupHom.isHom (GroupIso.map (Hⁿ-Unit≅0 n)) _ _ = refl
GroupIso.inv (Hⁿ-Unit≅0 n) _ = 0ₕ (suc n)
GroupIso.rightInv (Hⁿ-Unit≅0 n) _ = refl
GroupIso.leftInv (Hⁿ-Unit≅0 n) _ = isOfHLevelSuc 0 (isContrHⁿ-Unit n) _ _

{- Hⁿ for arbitrary contractible types -}
private
  Hⁿ-contrTypeIso : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
                   → Iso (coHom' (suc n) A) (coHom' (suc n) Unit)
  Hⁿ-contrTypeIso n contr = compIso (setTruncIso (isContr→Iso2 contr))
                                    (setTruncIso (invIso (isContr→Iso2 isContrUnit)))

Hⁿ-contrType≅0 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → GroupIso (coHomGr (suc n) A) trivialGroup
fun (GroupIso.map (Hⁿ-contrType≅0 _ _)) _ = _
isHom (GroupIso.map (Hⁿ-contrType≅0 _ _)) _ _ = refl
inv (Hⁿ-contrType≅0 n _) _ = 0ₕ (suc n)
rightInv (Hⁿ-contrType≅0 _ _) _ = refl
leftInv (Hⁿ-contrType≅0 {A = A} n contr) _ = isOfHLevelSuc 0 helper _ _
  where
  helper : isContr (coHom' (suc n) A)
  helper = Iso.inv (Hⁿ-contrTypeIso n contr) (0ₕ (suc n))
         , λ y →  cong (Iso.inv (Hⁿ-contrTypeIso n contr))
                         (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (0ₕ (suc n)) (Iso.fun (Hⁿ-contrTypeIso n contr) y))
                  ∙ Iso.leftInv (Hⁿ-contrTypeIso n contr) y
