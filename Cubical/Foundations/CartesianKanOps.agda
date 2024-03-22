-- This file derives some of the Cartesian Kan operations using transp
{-# OPTIONS --safe #-}
module Cubical.Foundations.CartesianKanOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Erp

coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (\ i → A i) i0 a

-- "coe filler"
coe0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

-- Check the equations for the coe filler
coe0→i1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coe0→i A i1 a ≡ coe0→1 A a
coe0→i1 A a = refl

coe0→i0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coe0→i A i0 a ≡ a
coe0→i0 A a = refl

-- coe backwards
coe1→0 : ∀ {ℓ} (A : I → Type ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a

-- coe backwards filler
coe1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a

-- Check the equations for the coe backwards filler
coe1→i0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coe1→i A i0 a ≡ coe1→0 A a
coe1→i0 A a = refl

coe1→i1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coe1→i A i1 a ≡ a
coe1→i1 A a = refl

-- "squeezeNeg"
coei→0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

coei0→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→0 A i0 a ≡ a
coei0→0 A a = refl

coei1→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→0 A i1 a ≡ coe1→0 A a
coei1→0 A a = refl

-- "Equality" on the interval, chosen for the next definition:
-- erp k i j is constant in k on eqI i j. Note that eqI i i is not i1
-- but i ∨ ~ i.
private
  eqI : I → I → I
  eqI i j = (i ∧ j) ∨ (~ i ∧ ~ j)

-- "master coe"
-- unlike in cartesian cubes, we don't get coei→i = id definitionally
coei→j : ∀ {ℓ} (A : I → Type ℓ) (i j : I) → A i → A j
coei→j A i j a = transp (λ k → A (erp k i j)) (eqI i j) a

-- "squeeze"
-- this is just defined as the face of the master coe
coei→1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i1
coei→1 A i a = coei→j A i i1 a

coei0→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl

-- equations for "master coe"
coei→i0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i0) → coei→j A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

coei→i1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i1 a ≡ coei→1 A i a
coei→i1 A i a = refl

coei1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i1) → coei→j A i1 i a ≡ coe1→i A i a
coei1→i A i a = refl

-- only non-definitional equation, but definitional at the ends
coei→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i a ≡ a
coei→i A i a j = transp (λ _ → A i) (erp j (i ∨ ~ i) i1) a
  where
  -- note: coei→i is almost just transportRefl (but the φ for the
  -- transp is i ∨ ~ i, not i0)
  _ : Path (PathP (λ i → A i → A i) (λ a → a) (λ a → a))
           (λ i a → coei→j A i i a)
           (λ i a → transp (λ _ → A i) (i ∨ ~ i) a)
  _ = refl

coe0→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→i A i0 a ≡ refl
coe0→0 A a = refl

coe1→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→i A i1 a ≡ refl
coe1→1 A a = refl

-- coercion when there already exists a path
coePath : ∀ {ℓ} (A : I → Type ℓ) (p : (i : I) → A i) → (i j : I) → coei→j A i j (p i) ≡ p j
coePath A p i j k =
  transp (λ l → A (erp l (erp k i j) j)) (erp k (eqI i j) i1) (p (erp k i j))

coePathi0 : ∀ {ℓ} (A : I → Type ℓ) (p : (i : I) → A i) → coePath A p i0 i0 ≡ refl
coePathi0 A p = refl

coePathi1 : ∀ {ℓ} (A : I → Type ℓ) (p : (i : I) → A i) → coePath A p i1 i1 ≡ refl
coePathi1 A p = refl

-- do the same for fill

fill1→i : ∀ {ℓ} (A : ∀ i → Type ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u1 : A i1 [ φ ↦ u i1 ])
       ---------------------------
       (i : I) → A i
fill1→i A {φ = φ} u u1 i =
  comp (λ j → A (i ∨ ~ j))
       (λ j → λ { (φ = i1) → u (i ∨ ~ j) 1=1
                ; (i = i1) → outS u1 })
       (outS u1)

filli→0 : ∀ {ℓ} (A : ∀ i → Type ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (i : I)
       (ui : A i [ φ ↦ u i ])
       ---------------------------
       → A i0
filli→0 A {φ = φ} u i ui =
  comp (λ j → A (i ∧ ~ j))
       (λ j → λ { (φ = i1) → u (i ∧ ~ j) 1=1
                ; (i = i0) → outS ui })
       (outS ui)

filli→j : ∀ {ℓ} (A : ∀ i → Type ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (i : I)
       (ui : A i [ φ ↦ u i ])
       ---------------------------
       (j : I) → A j
filli→j A {φ = φ} u i ui j =
  fill (\ i → A i)
    (λ j → λ { (φ = i1) → u j 1=1
             ; (i = i0) → fill (\ i → A i) (\ i → u i) ui j
             ; (i = i1) → fill1→i A u ui j
             })
    (inS (filli→0 A u i ui))
    j

-- We can reconstruct fill from hfill, coei→j, and the path coei→i ≡ id.
-- The definition does not rely on the computational content of the coei→i path.
fill' : ∀ {ℓ} (A : I → Type ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
       ---------------------------
       (i : I) → A i [ φ ↦ u i ]
fill' A {φ = φ} u u0 i =
  inS (hcomp (λ j → λ {(φ = i1) → coei→i A i (u i 1=1) j; (i = i0) → coei→i A i (outS u0) j}) t)
  where
  t : A i
  t = hfill {φ = φ} (λ j v → coei→j A j i (u j v)) (inS (coe0→i A i (outS u0))) i

fill'-cap :  ∀ {ℓ} (A : I → Type ℓ)
             {φ : I}
             (u : ∀ i → Partial φ (A i))
             (u0 : A i0 [ φ ↦ u i0 ])
             ---------------------------
             → outS (fill' A u u0 i0) ≡ outS (u0)
fill'-cap A u u0 = refl
