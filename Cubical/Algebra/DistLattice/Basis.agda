{-
 Definition of a basis of a distributive lattice as a generating sub-meet-semilattice
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.DistLattice.Basis where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData
open import Cubical.Data.Bool

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps

private
  variable
    ℓ : Level

module _ (L' : DistLattice ℓ) where
 private L = fst L'
 open DistLatticeStr (snd L')
 open Join L'

 record IsGenSublattice (M : Semilattice ℓ) (e : fst M → L) : Type ℓ where
  constructor
   isgensublattice
  open SemilatticeStr (snd M) renaming (ε to 0s ; _·_ to _∧s_)
  field
   isInj : ∀ x y → e x ≡ e y → x ≡ y
   pres0 : e 0s ≡ 0l
   resp∧ : ∀ x y → e (x ∧s y) ≡ e x ∧l e y
   ⋁Gen : ∀ (x : L) → ∃[ n ∈ ℕ ] Σ[ α ∈ FinVec (fst M) n ] (⋁ (e ∘ α) ≡ x)


 -- TODO: prove equivalence with the more set-theoretical definition
 record IsBasis (S : ℙ L) : Type ℓ where
  constructor
   isbasis
  field
   contains0 : 0l ∈ S
   ∧lClosed : ∀ (x y : L) → x ∈ S → y ∈ S → x ∧l y ∈ S
   ⋁Basis : ∀ (x : L) → ∃[ n ∈ ℕ ] Σ[ α ∈ FinVec L n ] (∀ i → α i ∈ S) × (⋁ α ≡ x)

