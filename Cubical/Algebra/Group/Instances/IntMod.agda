{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.IntMod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Algebra.Group.Instances.Unit
  renaming (Unit to UnitGroup)
open import Cubical.Algebra.Group.Instances.Bool
  renaming (Bool to BoolGroup)
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open GroupStr
open IsGroup
open IsMonoid

ℤ/_ : ℕ → Group₀
ℤ/ zero = UnitGroup
fst (ℤ/ suc n) = Fin (suc n)
1g (snd (ℤ/ suc n)) = 0
GroupStr._·_ (snd (ℤ/ suc n)) = _+ₘ_
inv (snd (ℤ/ suc n)) = -ₘ_
IsSemigroup.is-set (isSemigroup (isMonoid (isGroup (snd (ℤ/ suc n))))) =
  isSetFin
IsSemigroup.assoc (isSemigroup (isMonoid (isGroup (snd (ℤ/ suc n))))) =
  λ x y z → sym (+ₘ-assoc x y z)
fst (identity (isMonoid (isGroup (snd (ℤ/ suc n)))) x) = +ₘ-rUnit x
snd (identity (isMonoid (isGroup (snd (ℤ/ suc n)))) x) = +ₘ-lUnit x
fst (inverse (isGroup (snd (ℤ/ suc n))) x) = +ₘ-rCancel x
snd (inverse (isGroup (snd (ℤ/ suc n))) x) = +ₘ-lCancel x

ℤ/1≅Unit : GroupIso (ℤ/ 1) UnitGroup
ℤ/1≅Unit = contrGroupIsoUnit isContrFin1

Bool≅ℤ/2 : GroupIso BoolGroup (ℤ/ 2)
Iso.fun (fst Bool≅ℤ/2) false = 1
Iso.fun (fst Bool≅ℤ/2) true = 0
Iso.inv (fst Bool≅ℤ/2) (zero , p) = true
Iso.inv (fst Bool≅ℤ/2) (suc zero , p) = false
Iso.inv (fst Bool≅ℤ/2) (suc (suc x) , p) =
  ⊥-rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.rightInv (fst Bool≅ℤ/2) (zero , p) =
  Σ≡Prop (λ _ → m≤n-isProp) refl
Iso.rightInv (fst Bool≅ℤ/2) (suc zero , p) =
  Σ≡Prop (λ _ → m≤n-isProp) refl
Iso.rightInv (fst Bool≅ℤ/2) (suc (suc x) , p) =
  ⊥-rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.leftInv (fst Bool≅ℤ/2) false = refl
Iso.leftInv (fst Bool≅ℤ/2) true = refl
snd Bool≅ℤ/2 =
  makeIsGroupHom λ { false false → refl
                   ; false true → refl
                   ; true false → refl
                   ; true true → refl}

ℤ/2≅Bool : GroupIso (ℤ/ 2) BoolGroup
ℤ/2≅Bool = invGroupIso Bool≅ℤ/2
