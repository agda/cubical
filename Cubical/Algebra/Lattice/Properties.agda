{-# OPTIONS --safe #-}
module Cubical.Algebra.Lattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice.Base

private
  variable
    ℓ : Level

module LatticeTheory (L' : Lattice ℓ) where
 private L = fst L'
 open LatticeStr (snd L')

 0lLeftAnnihilates∧l : ∀ (x : L) → 0l ∧l x ≡ 0l
 0lLeftAnnihilates∧l x = 0l ∧l x          ≡⟨ cong (0l ∧l_) (sym (∨lLid _)) ⟩
                          0l ∧l (0l ∨l x) ≡⟨ ∧lAbsorb∨l _ _ ⟩
                          0l ∎

 0lRightAnnihilates∧l : ∀ (x : L) → x ∧l 0l ≡ 0l
 0lRightAnnihilates∧l _ = ∧lComm _ _ ∙ 0lLeftAnnihilates∧l _

 1lLeftAnnihilates∨l : ∀ (x : L) → 1l ∨l x ≡ 1l
 1lLeftAnnihilates∨l x = 1l ∨l x          ≡⟨ cong (1l ∨l_) (sym (∧lLid _)) ⟩
                          1l ∨l (1l ∧l x) ≡⟨ ∨lAbsorb∧l _ _ ⟩
                          1l ∎

 1lRightAnnihilates∨l : ∀ (x : L) → x ∨l 1l ≡ 1l
 1lRightAnnihilates∨l _ = ∨lComm _ _ ∙ 1lLeftAnnihilates∨l _



module Order (L' : Lattice ℓ) where
 private L = fst L'
 open LatticeStr (snd L')
 open JoinSemilattice (Lattice→JoinSemilattice L') renaming (_≤_ to _≤j_)
 open MeetSemilattice (Lattice→MeetSemilattice L') renaming (_≤_ to _≤m_)

 ≤Equiv : ∀ (x y : L) → (x ≤j y) ≃ (x ≤m y)
 ≤Equiv x y = isEquivPropBiimpl→Equiv (isSetLattice L' _ _) (isSetLattice L' _ _) .fst
                                      (≤j→≤m , ≤m→≤j)
  where
  ≤j→≤m : (x ≤j y) → (x ≤m y)
  ≤j→≤m x∨ly≡y = x ∧l y         ≡⟨ cong (x ∧l_) (sym x∨ly≡y) ⟩
                  x ∧l (x ∨l y) ≡⟨ ∧lAbsorb∨l _ _ ⟩
                  x ∎

  ≤m→≤j : (x ≤m y) → (x ≤j y)
  ≤m→≤j x∧ly≡x = x ∨l y ≡⟨ ∨lComm _ _ ⟩
                  y ∨l x ≡⟨ cong (y ∨l_) (sym x∧ly≡x) ⟩
                  y ∨l (x ∧l y) ≡⟨ cong (y ∨l_) (∧lComm _ _) ⟩
                  y ∨l (y ∧l x) ≡⟨ ∨lAbsorb∧l _ _ ⟩
                  y ∎
