{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A : Type ℓ

isPropPopulated : isProp (Populated A)
isPropPopulated = isPropΠ λ x → 2-Constant→isPropFixpoint (x .fst) (x .snd)

isPropHSeparated : isProp (HSeparated A)
isPropHSeparated f g i x y a = HSeparated→isSet f x y (f x y a) (g x y a) i

isPropCollapsible≡ : isProp (Collapsible≡ A)
isPropCollapsible≡ {A = A} f = (isPropΠ2 λ x y → isPropCollapsiblePointwise) f where
  sA : isSet A
  sA = Collapsible≡→isSet f
  gA : isGroupoid A
  gA = isSet→isGroupoid sA
  isPropCollapsiblePointwise : ∀ {x y} → isProp (Collapsible (x ≡ y))
  isPropCollapsiblePointwise {x} {y} (a , ca) (b , cb) = λ i → endoFunction i , endoFunctionIsConstant i where
    endoFunction : a ≡ b
    endoFunction = funExt λ p → sA _ _ (a p) (b p)
    isProp2-Constant : (k : I) → isProp (2-Constant (endoFunction k))
    isProp2-Constant k = isPropΠ2 λ r s → gA x y (endoFunction k r) (endoFunction k s)
    endoFunctionIsConstant : PathP (λ i → 2-Constant (endoFunction i)) ca cb
    endoFunctionIsConstant = isProp→PathP isProp2-Constant ca cb

isPropDiscrete : isProp (Discrete A)
isPropDiscrete p q = isPropΠ2 (λ x y → isPropDec (Discrete→isSet p x y)) p q
