{-

Cube Fillers for Truncated Types

These are essentially just packed-up versions of special cases of `extend`.
However, they offer some advantages:

- They appears to be concise in specific situations;

- They can exploit Agda's implicit argument inference,
   potentially sparing you from writing out all of the boundaries.
   But don't have a high expectation, it's very likely to fail...

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Filler where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels.Base
open import Cubical.Foundations.HLevels.Extend

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    w x y z : A
    B : A → Type ℓ'


-- cube fillers

fillSquare : Type ℓ → Type ℓ
fillSquare A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

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


-- type of hlevel n has cube fillers

-- h-proposition

isProp→Square : isProp A → fillSquare A
isProp→Square isprop p q r s i j =
  extendProp (λ _ → isprop) (∂ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j

isProp→SquareP :
  {B : I → I → Type ℓ} (h : (i j : I) → isProp (B i j))
  {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
  (r : PathP (λ j → B j i0) a c) (s : PathP (λ j → B j i1) b d)
  (p : PathP (λ j → B i0 j) a b) (q : PathP (λ j → B i1 j) c d)
  → SquareP B p q r s
isProp→SquareP isprop p q r s i j =
  extendProp (λ j → isprop i j) (∂ i) (λ j → λ
    { (i = i0) → r j ; (i = i1) → s j
    ; (j = i0) → p i ; (j = i1) → q i }) j

-- h-set

isSet→Square : isSet A → fillSquare A
isSet→Square isset a₀₋ a₁₋ a₋₀ a₋₁ i j =
  extendSet (λ _ _ → isset) i0 (λ i j → λ
    { (i = i0) → a₀₋ j ; (i = i1) → a₁₋ j
    ; (j = i0) → a₋₀ i ; (j = i1) → a₋₁ i }) i j

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

isGroupoid→Cube : isGroupoid A → fillCube A
isGroupoid→Cube isgrpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ i j k =
  extendGroupoid (λ _ _ _ → isgrpd) i0 (λ i j k → λ
    { (i = i0) → a₀₋₋ j k ; (i = i1) → a₁₋₋ j k
    ; (j = i0) → a₋₀₋ i k ; (j = i1) → a₋₁₋ i k
    ; (k = i0) → a₋₋₀ i j ; (k = i1) → a₋₋₁ i j }) i j k


-- cube fillers characterize hlevels

isContrPartial→isContr :
  {A : Type ℓ}
  (extend : ∀ φ → Partial φ A → A)
  (law : ∀ u → u ≡ (extend i1 λ { _ → u}))
  → isContr A
isContrPartial→isContr {A = A} extend law =
  ex , λ y → law ex ∙ (λ i → Aux.v y i) ∙ sym (law y)
  where
    ex = extend i0 empty
    module Aux (y : A) (i : I) where
      φ = ~ i ∨ i
      u : Partial φ A
      u = λ { (i = i0) → ex ; (i = i1) → y }
      v = extend φ u

fillSquare→isSet : fillSquare A → isSet A
fillSquare→isSet fsqr _ _ p q = fsqr p q refl refl

fillCube→isGroupoid : fillCube A → isGroupoid A
fillCube→isGroupoid fcube _ _ _ _ r s = fcube r s refl refl refl refl


-- cube fillers from dep hlevels

private
  toNonDep = isOfHLevelDep→isOfHLevel

isContrDep→isPropDep : isOfHLevelDep 0 B → isOfHLevelDep 1 B
isContrDep→isPropDep isctr b0 b1 p i =
  extendContr (toNonDep 0 isctr (p i)) _ λ
    { (i = i0) → b0 ; (i = i1) → b1 }

isPropDep→isSetDep : isOfHLevelDep 1 B → isOfHLevelDep 2 B
isPropDep→isSetDep isprop b0 b1 b2 b3 sq i j =
  extendProp (λ j → toNonDep 1 isprop (sq i j)) (∂ i) (λ j → λ
    { (i = i0) → b2 j ; (i = i1) → b3 j
    ; (j = i0) → b0   ; (j = i1) → b1 }) j

isPropDep→SquareP :
  (h : isOfHLevelDep 1 B)
  {p : w ≡ x} {q : y ≡ z} {r : w ≡ y} {s : x ≡ z}
  {tw : B w} {tx : B x} {ty : B y} {tz : B z} (sq : Square p q r s)
  (tp : PathP (λ i → B (p i)) tw tx) (tq : PathP (λ i → B (q i)) ty tz)
  (tr : PathP (λ i → B (r i)) tw ty) (ts : PathP (λ i → B (s i)) tx tz)
  → SquareP (λ i j → B (sq i j)) tp tq tr ts
isPropDep→SquareP isprop sq tp tq tr ts i j =
  extendProp (λ j → toNonDep 1 isprop (sq i j)) (∂ i) (λ j → λ
    { (i = i0) → tp j ; (i = i1) → tq j
    ; (j = i0) → tr i ; (j = i1) → ts i }) j
