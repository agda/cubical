{-

Kan Operations for n-Truncated Types

This file contain the `extend` operation
that provides an efficient way to construct cubes in truncated types.
It is a meta-theorem of Cubical Agda's type theory.
The detail of construction is collected in
  `Cubical.Foundations.HLevels.ExtendConstruction`.

A draft note on this can be found online at
  https://kangrongji.github.io/files/extend-operations.pdf

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Extend where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels.ExtendConstruction
open import Cubical.Foundations.HLevels.ExtendConstruction using (∂) public
open import Agda.Builtin.Nat  renaming (Nat to ℕ)
open import Agda.Builtin.Unit renaming ( ⊤ to Unit )
open import Agda.Builtin.List
open import Agda.Builtin.Reflection as R hiding (Type)


private
  variable
    ℓ : Level


{-

-- to conveniently present the boundary of cubes

∂ : I → I
∂ i = i ∨ ~ i

-}


pattern varg t = R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) t
pattern _v∷_ a l = varg a ∷ l

-- Transform internal ℕural numbers to external ones
-- In fact it's impossible in Agda's 2LTT, so we could only use a macro.

ℕ→MetaℕTerm : ℕ → Term
ℕ→MetaℕTerm 0 = quoteTerm Metaℕ.zero
ℕ→MetaℕTerm (suc n) = con (quote Metaℕ.suc) (ℕ→MetaℕTerm n v∷ [])

macro
  ℕ→Metaℕ : ℕ → Term → TC Unit
  ℕ→Metaℕ n t = unify t (ℕ→MetaℕTerm n)



-- This `extend` operation "using internal natural number as index"

macro
  extend : (n : ℕ) → Term → TC Unit
  extend n t = unify t
    (def (quote extendCurried) (ℕ→MetaℕTerm n v∷ []))


{-

The type of `extend` operation could be understood as:

extend :
  (n : ℕ) {ℓ : Level}
  (X : (i₁ ... iₙ : I) → Type ℓ)
  (h : (i₁ ... iₙ : I) → isOfHLevel n (X i₁ ... iₙ))
  (ϕ : I)
  (x : (i₁ ... iₙ : I) → Partial (ϕ ∨ ∂ i₁ ∨ ... ∨ ∂ iₙ) (X i₁ ... iₙ))
  (i₁ ... iₙ : I) → X i₁ ... iₙ [ _ ↦ x i₁ ... iₙ ]

-}


-- `extendₙ` for small value of `n`


extendContr :
  {X : Type ℓ}
  (h : isContr X)
  (ϕ : I)
  (x : Partial _ X)
  → X -- [ ϕ ↦ x ]
extendContr h ϕ x = outS (extend 0 h ϕ x)

extendProp :
  {X : I → Type ℓ}
  (h : (i : I) → isProp (X i))
  (ϕ : I)
  (x : (i : I) → Partial _ (X i))
  (i : I) → X i -- [ ϕ ∨ ∂ i ↦ x i ]
extendProp h ϕ x i = outS (extend 1 h ϕ x i)

extendSet :
  {X : I → I → Type ℓ}
  (h : (i j : I) → isSet (X i j))
  (ϕ : I)
  (x : (i j : I) → Partial _ (X i j))
  (i j : I) → X i j -- [ ϕ ∨ ∂ i ∨ ∂ j ↦ x i j ]
extendSet h ϕ x i j = outS (extend 2 h ϕ x i j)

extendGroupoid :
  {X : I → I → I → Type ℓ}
  (h : (i j k : I) → isGroupoid (X i j k))
  (ϕ : I)
  (x : (i j k : I) → Partial _ (X i j k))
  (i j k : I) → X i j k -- [ ϕ ∨ ∂ i ∨ ∂ j ∨ ∂ k ↦ x i j k ]
extendGroupoid h ϕ x i j k = outS (extend 3 h ϕ x i j k)


private
  -- An example showing how to directly fill 3-cubes in an h-proposition.
  -- It can help when one wants to pattern match certain HITs towards some n-types.

  isProp→Cube :
    {X : Type ℓ} (h : isProp X)
    (x : (i j k : I) → Partial _ X)
    (i j k : I) → X -- [ ∂ i ∨ ∂ j ∨ ∂ k ↦ x i j k ]
  isProp→Cube h x i j =
    extendProp (λ _ → h) (∂ i ∨ ∂ j) (x i j)
