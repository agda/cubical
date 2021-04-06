{-# OPTIONS --cubical --no-import-sorts --safe #-}
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
open import Cubical.Foundations.Univalence

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isSetUnit : isSet Unit
isSetUnit = isProp→isSet isPropUnit

isOfHLevelUnit : (n : HLevel) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

UnitToTypeIso : ∀ {ℓ} (A : Type ℓ) → Iso (Unit → A) A
Iso.fun (UnitToTypeIso A) f = f _
Iso.inv (UnitToTypeIso A) a _ = a
Iso.rightInv (UnitToTypeIso A) _ = refl
Iso.leftInv (UnitToTypeIso A) _ = refl

UnitToTypePath : ∀ {ℓ} (A : Type ℓ) → (Unit → A) ≡ A
UnitToTypePath A = isoToPath (UnitToTypeIso A)

isContr→Iso2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isContr A → Iso (A → B) B
Iso.fun (isContr→Iso2 iscontr) f = f (fst iscontr)
Iso.inv (isContr→Iso2 iscontr) b _ = b
Iso.rightInv (isContr→Iso2 iscontr) _ = refl
Iso.leftInv (isContr→Iso2 iscontr) f = funExt λ x → cong f (snd iscontr x)

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

isContr→≃Unit : ∀ {ℓ} {A : Type ℓ} → isContr A → A ≃ Unit
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
