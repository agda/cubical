{- Conatural numbers (Tesla Zhang, Feb. 2019)

This file defines:

- A coinductive natural number representation which is dual to
  the inductive version (zero | suc Nat → Nat) of natural numbers.

- Trivial operations (succ, pred) and the pattern synonyms on conaturals.

While this definition can be seen as a coinductive wrapper of an inductive
datatype, another way of definition is to define an inductive datatype that
wraps a coinductive thunk of Nat.
The standard library uses the second approach:

https://github.com/agda/agda-stdlib/blob/master/src/Codata/Conat.agda

The first approach is chosen to exploit guarded recursion and to avoid the use
of Sized Types.
-}

{-# OPTIONS --safe --guardedness #-}
module Cubical.Codata.Conat.Base where

open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Core.Everything

record Conat : Type₀
Conat′ = Unit ⊎ Conat
record Conat where
  coinductive
  field force : Conat′
open Conat public

pattern zero  = inl tt
pattern suc n = inr n

conat : Conat′ → Conat
force (conat a) = a

succ : Conat → Conat
force (succ a) = suc a

succ′ : Conat′ → Conat′
succ′ n = suc λ where .force → n

pred′ : Conat′ → Conat′
pred′  zero   = zero
pred′ (suc x) = force x

pred′′ : Conat′ → Conat
force (pred′′ zero) = zero
pred′′ (suc x) = x
