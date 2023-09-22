{-

Cube Fillers for Truncated Types

These are essentially just packed-up versions of special cases of `extend`.
However, they offer some advantages:

- They appear to be more concise in specific situations;

- They are able to exploit Agda's implicit argument inference,
   potentially sparing you from writing out all of the boundaries.
   But don't have a high expectation, it's very likely to fail...

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Fillers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels.Base
open import Cubical.Foundations.HLevels.Extend

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    w x y z : A
    B : A → Type ℓ'


-- Cube fillers

fillSquare : Type ℓ → Type ℓ
fillSquare A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

fillSquareP : (A : I → I → Type ℓ) → Type ℓ
fillSquareP A =
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁

fillCube : Type ℓ → Type ℓ
fillCube A =
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


-- Types of hlevel n have cube fillers

-- h-propositions
-- you can find `isProp→PathP` in `Cubical.Foundations.Prelude`

isProp→Square : isProp A → fillSquare A
isProp→Square h p q r s i j =
  extendProp (λ _ → h) (∂ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j

isProp→SquareP :
  {A : I → I → Type ℓ} (h : (i j : I) → isProp (A i j)) → fillSquareP A
isProp→SquareP h p q r s i j =
  extendProp (λ j → h i j) (∂ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j

-- h-sets

isSet→Square : isSet A → fillSquare A
isSet→Square h a₀₋ a₁₋ a₋₀ a₋₁ i j =
  extendSet (λ _ _ → h) i0 (λ i j → λ
    { (i = i0) → a₀₋ j ; (i = i1) → a₁₋ j
    ; (j = i0) → a₋₀ i ; (j = i1) → a₋₁ i }) i j

isSet→SquareP :
  {A : I → I → Type ℓ} (h : (i j : I) → isSet (A i j)) → fillSquareP A
isSet→SquareP h a₀₋ a₁₋ a₋₀ a₋₁ i j =
  extendSet h i0 (λ i j → λ
    { (i = i0) → a₀₋ j ; (i = i1) → a₁₋ j
    ; (j = i0) → a₋₀ i ; (j = i1) → a₋₁ i }) i j

-- h-groupoids

isGroupoid→Cube : isGroupoid A → fillCube A
isGroupoid→Cube isgrpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ i j k =
  extendGroupoid (λ _ _ _ → isgrpd) i0 (λ i j k → λ
    { (i = i0) → a₀₋₋ j k ; (i = i1) → a₁₋₋ j k
    ; (j = i0) → a₋₀₋ i k ; (j = i1) → a₋₁₋ i k
    ; (k = i0) → a₋₋₀ i j ; (k = i1) → a₋₋₁ i j }) i j k


-- Cube fillers characterize hlevels

isContrPartial→isContr :
  (extend : ∀ φ → Partial φ A → A)
  (law : ∀ u → u ≡ (extend i1 λ { _ → u}))
  → isContr A
isContrPartial→isContr {A = A} extend law =
  ex , λ a → law ex ∙ (λ i → v a i) ∙ sym (law a)
  where
    ex = extend i0 empty
    module _ (a : A) (i : I) where
      v = extend _ λ { (i = i0) → ex ; (i = i1) → a }

fillSquare→isSet : fillSquare A → isSet A
fillSquare→isSet fsqr _ _ p q = fsqr p q refl refl

fillCube→isGroupoid : fillCube A → isGroupoid A
fillCube→isGroupoid fcube _ _ _ _ r s = fcube r s refl refl refl refl


-- Cube fillers from dependent hlevels

private
  toNonDep = isOfHLevelDep→isOfHLevel

isContrDep→isPropDep : isOfHLevelDep 0 B → isOfHLevelDep 1 B
isContrDep→isPropDep h x y p i =
  extendContr (toNonDep 0 h (p i)) _ λ
    { (i = i0) → x ; (i = i1) → y }

isPropDep→isSetDep : isOfHLevelDep 1 B → isOfHLevelDep 2 B
isPropDep→isSetDep h x y p q sq i j =
  extendProp (λ j → toNonDep 1 h (sq i j)) (∂ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → x   ; (j = i1) → y }) j

isPropDep→SquareP :
  (h : isOfHLevelDep 1 B)
  {p : w ≡ x} {q : y ≡ z} {r : w ≡ y} {s : x ≡ z}
  (sq : Square p q r s)
  → fillSquareP (λ i j → B (sq i j))
isPropDep→SquareP h sq p q r s i j =
  extendProp (λ j → toNonDep 1 h (sq i j)) (∂ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j
