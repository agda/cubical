{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.ZCohomologyOld.Groups.Unit where

open import Cubical.ZCohomology.Base
open import Cubical.Experiments.ZCohomologyOld.Properties
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
open import Cubical.Algebra.Group renaming (Unit to trivialGroup ; Int to IntGroup)

-- H⁰(Unit)
open GroupHom
open GroupIso
open Iso

H⁰-Unit≅ℤ : GroupIso (coHomGr 0 Unit) IntGroup
fun (isom H⁰-Unit≅ℤ) = sRec isSetInt (λ f → f tt)
inv (isom H⁰-Unit≅ℤ) a = ∣ (λ _ → a) ∣₂
rightInv (isom H⁰-Unit≅ℤ) _ = refl
leftInv (isom H⁰-Unit≅ℤ) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl
isHom H⁰-Unit≅ℤ = sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a tt) (b tt)

{- Hⁿ(Unit) for n ≥ 1 -}
isContrHⁿ-Unit : (n : ℕ) → isContr (coHom (suc n) Unit)
isContrHⁿ-Unit n = subst isContr (λ i → ∥ UnitToTypePath (coHomK (suc n)) (~ i) ∥₂) (helper' n)
  where
  helper' : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₂)
  helper' n =
    subst isContr
      ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n)))
         ∙∙ sym propTrunc≡Trunc2
         ∙∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₂)
      (isConnectedSubtr 2 (helper2 n .fst)
        (subst (λ x → isConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
    where
    helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
    helper2 zero = 0 , refl
    helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)

Hⁿ-Unit≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) Unit) trivialGroup
fun (isom (Hⁿ-Unit≅0 n)) _ = _
inv (isom (Hⁿ-Unit≅0 n)) _ = 0ₕ (suc n)
rightInv (isom (Hⁿ-Unit≅0 n)) _ = refl
leftInv (isom (Hⁿ-Unit≅0 n)) _ = isOfHLevelSuc 0 (isContrHⁿ-Unit n) _ _
isHom (Hⁿ-Unit≅0 n) _ _ = refl

{- Hⁿ for arbitrary contractible types -}
private
  Hⁿ-contrTypeIso : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
                   → Iso (coHom (suc n) A) (coHom (suc n) Unit)
  Hⁿ-contrTypeIso n contr = compIso (setTruncIso (isContr→Iso2 contr))
                                    (setTruncIso (invIso (isContr→Iso2 isContrUnit)))

Hⁿ-contrType≅0 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → GroupIso (coHomGr (suc n) A) trivialGroup
fun (isom (Hⁿ-contrType≅0 _ _)) _ = _
inv (isom (Hⁿ-contrType≅0 n _)) _ = 0ₕ (suc n)
rightInv (isom (Hⁿ-contrType≅0 _ _)) _ = refl
leftInv (isom (Hⁿ-contrType≅0 {A = A} n contr)) _ = isOfHLevelSuc 0 helper _ _
  where
  helper : isContr (coHom (suc n) A)
  helper = (Iso.inv (Hⁿ-contrTypeIso n contr) (0ₕ (suc n)))
          , λ y →  cong (Iso.inv (Hⁿ-contrTypeIso n contr))
                         (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (0ₕ (suc n)) (Iso.fun (Hⁿ-contrTypeIso n contr) y))
                  ∙ Iso.leftInv (Hⁿ-contrTypeIso n contr) y
isHom (Hⁿ-contrType≅0 _ _) _ _ = refl
