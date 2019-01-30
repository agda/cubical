-- This file derives some of the Cartesian Kan operations using transp
{-# OPTIONS --cubical --safe #-}
module Cubical.Basics.CartesianKanOps where

open import Cubical.Core.Everything

coe0→1 : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1
coe0→1 A a = transp A i0 a

-- "coe filler"
coe0→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

-- Check the equations for the coe filler
coe0→i1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coe0→i A i1 a ≡ coe0→1 A a
coe0→i1 A a = refl

coe0→i0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coe0→i A i0 a ≡ a
coe0→i0 A a = refl


-- coe backwards
coe1→0 : ∀ {ℓ} (A : I → Set ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a

-- coe backwards filler
coe1→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a

-- Check the equations for the coe backwards filler
coe1→i0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coe1→i A i0 a ≡ coe1→0 A a
coe1→i0 A a = refl

coe1→i1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coe1→i A i1 a ≡ a
coe1→i1 A a = refl


-- "squeeze"
coei→1 : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i → A i1
coei→1 A i a = transp (λ j → A (i ∨ j)) i a

coei0→1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl


-- "squeezeNeg"
coei→0 : ∀ {ℓ} (A : I → Set ℓ) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

coei0→0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → coei→0 A i0 a ≡ a
coei0→0 A a = refl

coei1→0 : ∀ {ℓ} (A : I → Set ℓ) (a : A i1) → coei→0 A i1 a ≡ coe1→0 A a
coei1→0 A a = refl


-- "super coe"... Without boolean algebra structure it doesn't seem
-- possible to define. The problem is that interpolation is not
-- working properly as we don't have the boolean equations.
coei→j : ∀ {ℓ} (A : I → Set ℓ) (i j : I) → A i → A j
coei→j A i j a = transp (λ k → A ((i ∧ ~ k) ∨ (j ∧ k))) (~ i ∧ ~ j) a

-- We only get the two equations for i0:

coei→i0 : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i0) → coei→j A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

-- For i1 we don't get the equations definitionally:

-- coei→i1 : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j A i i1 a ≡ coei→1 A i a
-- coei→i1 A i a = {!!}

-- coei1→i : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i1) → coei→j A i1 i a ≡ coe1→i A i a
-- coei1→i A i a = {!!}


-- We can also get the equations for i1, but then not for i0

coei→j' : ∀ {ℓ} (A : I → Set ℓ) (i j : I) → A i → A j
coei→j' A i j a = transp (λ k → A ((i ∧ j) ∨ (j ∧ k) ∨ (~ k ∧ i))) (i ∧ j) a 

coei→i1' : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j' A i i1 a ≡ coei→1 A i a
coei→i1' A i a = refl

coei1→i' : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i1) → coei→j' A i1 i a ≡ coe1→i A i a
coei1→i' A i a = refl

-- coei→i0' : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i) → coei→j' A i i0 a ≡ coei→0 A i a
-- coei→i0' A i a = {!!}

-- coei0→i' : ∀ {ℓ} (A : I → Set ℓ) (i : I) (a : A i0) → coei→j' A i0 i a ≡ coe0→i A i a
-- coei0→i' A i a = {!!}
