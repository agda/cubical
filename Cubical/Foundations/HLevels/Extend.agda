{-

Kan Operations for n-Truncated Types

It provides an efficient way to construct cubes in truncated types.

A draft note on this can be found online at
https://kangrongji.github.io/files/extend-operations.pdf

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Extend where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level


-- For conveniently representing the boundary of cubes
∂ : I → I
∂ i = i ∨ ~ i


-- TODO: Write a macro to generate these stuff.

module _
  {X : Type ℓ}
  (h : isContr X)
  {ϕ : I} where

  extend₀ :
    (x : Partial _ X)
    → X [ ϕ ↦ x ]
  extend₀ = extend h _


module _
  {X : I → Type ℓ}
  (h : (i : I) → isProp (X i))
  {ϕ : I} where

  extend₁ :
    (x : (i : I) → Partial _ (X i))
    (i : I) → X i [ ϕ ∨ ∂ i ↦ x i ]
  extend₁ x i = inS (hcomp (λ j → λ
    { (ϕ = i1) → h i (bottom i) (x i 1=1) j
    ; (i = i0) → h i (bottom i) (x i 1=1) j
    ; (i = i1) → h i (bottom i) (x i 1=1) j })
    (bottom i))
    where
    bottom : (i : I) → X i
    bottom i = isProp→PathP h (x i0 1=1) (x i1 1=1) i


module _
  {X : I → I → Type}
  (h : (i j : I) → isSet (X i j))
  {ϕ : I} where

  extend₂ :
    (x : (i j : I) → Partial _ (X i j))
    (i j : I) → X i j [ ϕ ∨ ∂ i ∨ ∂ j ↦ x i j ]
  extend₂ x i j = inS (outS (extend₁PathP p i) j)
    where
    isOfHLevel₁PathP : (i : I) (a : X i i0) (b : X i i1)
      → isProp (PathP (λ j → X i j) a b)
    isOfHLevel₁PathP i = isOfHLevelPathP' 1 (h i i1)

    extend₁PathP :
      (p : (i : I) → Partial _ (PathP _ (x i i0 1=1) (x i i1 1=1)))
      (i : I) → PathP _ (x i i0 1=1) (x i i1 1=1) [ ϕ ∨ ∂ i ↦ p i ]
    extend₁PathP = extend₁ (λ i → isOfHLevel₁PathP i (x i i0 1=1) (x i i1 1=1)) {ϕ}

    p : (i : I) → Partial _ (PathP _ (x i i0 1=1) (x i i1 1=1))
    p i (i = i0) = λ j → x i j 1=1
    p i (i = i1) = λ j → x i j 1=1
    p i (ϕ = i1) = λ j → x i j 1=1


module _
  (X : I → I → I → Type)
  (h : (i j k : I) → isGroupoid (X i j k))
  {ϕ : I} where

  extend₃ :
    (x : (i j k : I) → Partial _ (X i j k))
    (i j k : I) → X i j k [ ϕ ∨ ∂ i ∨ ∂ j ∨ ∂ k ↦ x i j k ]
  extend₃ x i j k = inS (outS (extend₂PathP p i j) k)
    where
    isOfHLevel₂PathP : (i j : I) (a : X i j i0) (b : X i j i1)
      → isSet (PathP (λ k → X i j k) a b)
    isOfHLevel₂PathP i j = isOfHLevelPathP' 2 (h i j i1)

    extend₂PathP :
      (p : (i j : I) → Partial _ (PathP _ (x i j i0 1=1) (x i j i1 1=1)))
      (i j : I) → PathP _ (x i j i0 1=1) (x i j i1 1=1) [ ϕ ∨ ∂ i ∨ ∂ j ↦ p i j ]
    extend₂PathP = extend₂ (λ i j → isOfHLevel₂PathP i j (x i j i0 1=1) (x i j i1 1=1)) {ϕ}

    p : (i j : I) → Partial _ (PathP (λ k → X i j k) (x i j i0 1=1) (x i j i1 1=1))
    p i j (i = i0) = λ k → x i j k 1=1
    p i j (i = i1) = λ k → x i j k 1=1
    p i j (j = i0) = λ k → x i j k 1=1
    p i j (j = i1) = λ k → x i j k 1=1
    p i j (ϕ = i1) = λ k → x i j k 1=1


private
  -- An example showing how to directly fill 3-cubes in an h-proposition.
  -- It can help when one wants to pattern match certain HITs towards some n-types.

  isProp→Cube :
    {X : Type ℓ} (h : isProp X)
    (x : (i j k : I) → Partial _ X)
    (i j k : I) → X [ ∂ i ∨ ∂ j ∨ ∂ k ↦ x i j k ]
  isProp→Cube h x i j =
    extend₁ (λ _ → h) {∂ i ∨ ∂ j} (x i j)
