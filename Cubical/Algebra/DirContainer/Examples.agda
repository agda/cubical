{-# OPTIONS --safe #-}

module Cubical.Algebra.DirContainer.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.DirContainer.Base
open import Cubical.Data.Containers.Set.Base
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool hiding (_⊕_ ; ⊕-assoc)
open import Cubical.Data.Empty
open import Cubical.Data.Sum


private
  variable
    ℓs ℓp : Level

open DirContainer

-- Examples of directed containers

WriterC : (A : hSet ℓs) → DirContainer {ℓs} {ℓp} (fst A ◁ (const (Unit* {ℓp})) & snd A & isSetUnit*)
o (WriterC A) _ = tt* 
_↓_ (WriterC A) a tt* = a
_⊕_ (WriterC A) tt* tt* = tt*
unitl-↓ (WriterC A) a = refl
distr-↓-⊕ (WriterC A) a tt* tt* = refl
unitl-⊕ (WriterC A) a tt* = refl
unitr-⊕ (WriterC A) a tt* = refl
assoc-⊕ (WriterC A) a tt* tt* i tt* = tt*

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Semigroup
open MonoidStr
open IsMonoid
open IsSemigroup

ReaderC : (A : Type ℓp) (mon : MonoidStr A) →
          DirContainer {ℓs} {ℓp} ((Unit* {ℓs}) ◁ (const A) & isSetUnit* & mon .isMonoid .isSemigroup .is-set)
o (ReaderC A mon) tt* = mon .ε
_↓_ (ReaderC A mon) tt* a = tt*
_⊕_ (ReaderC A mon) = mon ._·_
unitl-↓ (ReaderC A mon) tt* = refl
distr-↓-⊕ (ReaderC A mon) tt* a a' = refl
unitl-⊕ (ReaderC A mon) tt* = mon .isMonoid .·IdL
unitr-⊕ (ReaderC A mon) tt* = mon .isMonoid .·IdR
assoc-⊕ (ReaderC A mon) tt* a a' i a'' = mon .isMonoid .·Assoc a a' a'' (~ i)

StreamC : DirContainer {ℓs} {ℓ-zero} ((Unit* {ℓs}) ◁ (const ℕ) & isSetUnit* & isSetℕ)
StreamC = ReaderC (fst NatMonoid) (snd NatMonoid)
