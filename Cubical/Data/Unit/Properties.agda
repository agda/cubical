{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

private
  variable
    ℓ : Level

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isSetUnit : isSet Unit
isSetUnit = isProp→isSet isPropUnit

isOfHLevelUnit : (n : HLevel) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

fibId : ∀ {ℓ} (A : Type ℓ) → (fiber (λ (x : A) → tt) tt) ≡ A
fibId A = isoToPath
            (iso fst
                 (λ a → a , refl)
                 (λ _ → refl)
                 (λ a i → fst a
                         , isOfHLevelSuc 1 isPropUnit _ _ (snd a) refl i))

𝟙-universal : (X : Type ℓ) → Iso (Unit → X) X
𝟙-universal X = iso (λ f → f tt) (λ x _ → x) (λ _ → refl) λ _ → refl
