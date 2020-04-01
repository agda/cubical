{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A : Type ℓ

isPropPopulated : isProp (Populated A)
isPropPopulated = isPropPi λ x → 2-Constant→isPropFixpoint (x .fst) (x .snd)

isPropHStable≡ : isProp (HStable≡ A)
isPropHStable≡ f g i x y a = HStable≡→isSet f x y (f x y a) (g x y a) i

isPropCollapsible≡ : isProp (Collapsible≡ A)
isPropCollapsible≡ {A = A} f g = (isPropPi λ x → isPropPi λ y → isPropCollapsiblePointwise) f g where
  sA : isSet A
  sA = Collapsible≡→isSet f
  gA : isGroupoid A
  gA = isOfHLevelSuc 2 sA
  isPropCollapsiblePointwise : ∀ {x y} → isProp (Collapsible (x ≡ y))
  isPropCollapsiblePointwise {x} {y} (a , ca) (b , cb) i =
    (λ p → sA _ _ (a p) (b p) i) ,
    (λ r s → isProp→PathP (λ k → gA x y (sA _ _ (a r) (b r) k) (sA _ _ (a s) (b s) k)) (ca r s) (cb r s) i)
