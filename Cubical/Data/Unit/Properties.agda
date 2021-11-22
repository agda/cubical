{-# OPTIONS --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' : Level

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isSetUnit : isSet Unit
isSetUnit = isProp→isSet isPropUnit

isOfHLevelUnit : (n : HLevel) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

module _ (A : Type ℓ) where
  UnitToType≃ : (Unit → A) ≃ A
  unquoteDef UnitToType≃ = defStrictEquiv UnitToType≃ (λ f → f _) const

UnitToTypePath : ∀ {ℓ} (A : Type ℓ) → (Unit → A) ≡ A
UnitToTypePath A = ua (UnitToType≃ A)

module _ (A : Unit → Type ℓ) where

  open Iso

  ΠUnitIso : Iso ((x : Unit) → A x) (A tt)
  fun ΠUnitIso f = f tt
  inv ΠUnitIso a tt = a
  rightInv ΠUnitIso a = refl
  leftInv ΠUnitIso f = refl

  ΠUnit : ((x : Unit) → A x) ≃ A tt
  ΠUnit = isoToEquiv ΠUnitIso

isContr→Iso2 : {A : Type ℓ} {B : Type ℓ'} → isContr A → Iso (A → B) B
Iso.fun (isContr→Iso2 iscontr) f = f (fst iscontr)
Iso.inv (isContr→Iso2 iscontr) b _ = b
Iso.rightInv (isContr→Iso2 iscontr) _ = refl
Iso.leftInv (isContr→Iso2 iscontr) f = funExt λ x → cong f (snd iscontr x)

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

fibId : (A : Type ℓ) → (fiber (λ (x : A) → tt) tt) ≡ A
fibId A = ua e
  where
  unquoteDecl e = declStrictEquiv e fst (λ a → a , refl)

isContr→≃Unit : {A : Type ℓ} → isContr A → A ≃ Unit
isContr→≃Unit contr = isoToEquiv (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)

isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
isContr→≡Unit contr = ua (isContr→≃Unit contr)

isContrUnit* : ∀ {ℓ} → isContr (Unit* {ℓ})
isContrUnit* = tt* , λ _ → refl

isPropUnit* : ∀ {ℓ} → isProp (Unit* {ℓ})
isPropUnit* _ _ = refl

isOfHLevelUnit* : ∀ {ℓ} (n : HLevel) → isOfHLevel n (Unit* {ℓ})
isOfHLevelUnit* zero = tt* , λ _ → refl
isOfHLevelUnit* (suc zero) _ _ = refl
isOfHLevelUnit* (suc (suc zero)) _ _ _ _ _ _ = tt*
isOfHLevelUnit* (suc (suc (suc n))) = isOfHLevelPlus 3 (isOfHLevelUnit* n)

Unit≃Unit* : ∀ {ℓ} → Unit ≃ Unit* {ℓ}
Unit≃Unit* = invEquiv (isContr→≃Unit isContrUnit*)

isContr→≃Unit* : {A : Type ℓ} → isContr A → A ≃ Unit* {ℓ}
isContr→≃Unit* contr = compEquiv (isContr→≃Unit contr) Unit≃Unit*

isContr→≡Unit* : {A : Type ℓ} → isContr A → A ≡ Unit*
isContr→≡Unit* contr = ua (isContr→≃Unit* contr)
