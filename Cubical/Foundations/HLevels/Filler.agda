{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Filler where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels.Base
open import Cubical.Foundations.HLevels.Extend

private
  variable
    ℓ : Level
    A : Type ℓ



-- Alternative (equivalent) definitions of hlevel n that give fillers for n-cubes instead of n-globes

isSet' : Type ℓ → Type ℓ
isSet' A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

isSet→isSet' : isSet A → isSet' A
isSet→isSet' Aset _ _ _ _ = toPathP (Aset _ _ _ _)

isSet'→isSet : isSet' A → isSet A
isSet'→isSet Aset' x y p q = Aset' p q refl refl

isGroupoid' : Type ℓ → Type ℓ
isGroupoid' A =
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

isProp→isSet' : isProp A → isSet' A
isProp→isSet' h {a} p q r s i j =
  extendProp (λ _ → h) (i ∨ ~ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j



-- Fillers for cubes from h-level

isSet→SquareP :
  {A : I → I → Type ℓ}
  (isSet : (i j : I) → isSet (A i j))
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
isSet→SquareP isset a₀₋ a₁₋ a₋₀ a₋₁ i j =
  extendSet isset i0 (λ i j → λ
    { (i = i0) → a₀₋ j ; (i = i1) → a₁₋ j
    ; (j = i0) → a₋₀ i ; (j = i1) → a₋₁ i }) i j

isGroupoid→isGroupoid' : isGroupoid A → isGroupoid' A
isGroupoid→isGroupoid' {A = A} isgrpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ i j k =
  extendGroupoid (λ _ _ _ → isgrpd) i0 (λ i j k → λ
    { (i = i0) → a₀₋₋ j k ; (i = i1) → a₁₋₋ j k
    ; (j = i0) → a₋₀₋ i k ; (j = i1) → a₋₁₋ i k
    ; (k = i0) → a₋₋₀ i j ; (k = i1) → a₋₋₁ i j }) i j k

isGroupoid'→isGroupoid : isGroupoid' A → isGroupoid A
isGroupoid'→isGroupoid Agpd' x y p q r s = Agpd' r s refl refl refl refl


isContrPartial→isContr : ∀ {ℓ} {A : Type ℓ}
                       → (extend : ∀ φ → Partial φ A → A)
                       → (∀ u → u ≡ (extend i1 λ { _ → u}))
                       → isContr A
isContrPartial→isContr {A = A} extend law
  = ex , λ y → law ex ∙ (λ i → Aux.v y i) ∙ sym (law y)
    where ex = extend i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial φ A
            u = λ { (i = i0) → ex ; (i = i1) → y }
            v = extend φ u
