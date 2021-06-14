{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.Unit where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (ℤ ; _+_ ; +Comm)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group renaming (Unit to UnitGroup)

-- H⁰(Unit)
open IsGroupHom
open Iso

H⁰-Unit≅ℤ : GroupIso (coHomGr 0 Unit) ℤ
fun (fst H⁰-Unit≅ℤ) = sRec isSetℤ (λ f → f tt)
inv (fst H⁰-Unit≅ℤ) a = ∣ (λ _ → a) ∣₂
rightInv (fst H⁰-Unit≅ℤ) _ = refl
leftInv (fst H⁰-Unit≅ℤ) = sElim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _) λ a → refl
snd H⁰-Unit≅ℤ = makeIsGroupHom (sElim2 (λ _ _ → isOfHLevelPath 2 isSetℤ _ _) λ a b → refl)

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

Hⁿ-Unit≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) Unit) UnitGroup
fun (fst (Hⁿ-Unit≅0 n)) _ = _
inv (fst (Hⁿ-Unit≅0 n)) _ = 0ₕ (suc n)
rightInv (fst (Hⁿ-Unit≅0 n)) _ = refl
leftInv (fst (Hⁿ-Unit≅0 n)) _ = isOfHLevelSuc 0 (isContrHⁿ-Unit n) _ _
snd (Hⁿ-Unit≅0 n) = makeIsGroupHom λ _ _ → refl


{- Hⁿ for arbitrary contractible types -}
private
  Hⁿ-contrTypeIso : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
                   → Iso (coHom (suc n) A) (coHom (suc n) Unit)
  Hⁿ-contrTypeIso n contr = compIso (setTruncIso (isContr→Iso2 contr))
                                    (setTruncIso (invIso (isContr→Iso2 isContrUnit)))

Hⁿ-contrType≅0 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → GroupIso (coHomGr (suc n) A) UnitGroup
fun (fst (Hⁿ-contrType≅0 n contr)) _ = _
inv (fst (Hⁿ-contrType≅0 n contr)) _ = 0ₕ (suc n)
rightInv (fst (Hⁿ-contrType≅0 n contr)) _ = refl
leftInv (fst (Hⁿ-contrType≅0 {A = A} n contr)) _ = isOfHLevelSuc 0 helper _ _
  where
  helper : isContr (coHom (suc n) A)
  helper = (Iso.inv (Hⁿ-contrTypeIso n contr) (0ₕ (suc n)))
          , λ y →  cong (Iso.inv (Hⁿ-contrTypeIso n contr))
                         (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (0ₕ (suc n)) (Iso.fun (Hⁿ-contrTypeIso n contr) y))
                  ∙ Iso.leftInv (Hⁿ-contrTypeIso n contr) y
snd (Hⁿ-contrType≅0 n contr) = makeIsGroupHom λ _ _ → refl

isContr-HⁿRed-Unit : (n : ℕ) → isContr (coHomRed n (Unit , tt))
fst (isContr-HⁿRed-Unit n) = 0ₕ∙ _
snd (isContr-HⁿRed-Unit n) =
  sElim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
        λ {(f , p) → cong ∣_∣₂ (ΣPathP (funExt (λ _ → sym p)
                                     , λ i j → p (~ i ∨ j)))}
