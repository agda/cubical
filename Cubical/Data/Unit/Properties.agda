{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isOfHLevelUnit : (n : ℕ) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

UnitToTypeId : ∀ {ℓ} (A : Type ℓ) → (Unit → A) ≡ A
UnitToTypeId A = isoToPath (iso (λ f → f tt) (λ a _ → a) (λ _ → refl) λ _ → refl)

ContrToTypeIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isContr A → Iso (A → B) B
Iso.fun (ContrToTypeIso iscontr) f = f (fst iscontr)
Iso.inv (ContrToTypeIso iscontr) b _ = b
Iso.rightInv (ContrToTypeIso iscontr) _ = refl
Iso.leftInv (ContrToTypeIso iscontr) f = funExt λ x → cong f (snd iscontr x)

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

fibId : ∀ {ℓ} (A : Type ℓ) → (fiber (λ (x : A) → tt) tt) ≡ A
fibId A =
  isoToPath
    (iso fst
         (λ a → a , refl)
         (λ _ → refl)
         (λ a i → fst a
                 , isOfHLevelSuc 1 isPropUnit _ _ (snd a) refl i))

isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
isContr→≡Unit contr = isoToPath (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)
