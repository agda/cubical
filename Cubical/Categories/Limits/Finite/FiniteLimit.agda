{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Finite.FiniteLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Data.Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.DistLattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Limits.Finite.FiniteSystem

open import Cubical.Relation.Binary.Poset

private
  variable
    ℓ ℓ' ℓ'' : Level


FinDiagram : (C : Category ℓ ℓ') (n : ℕ) → Type _
FinDiagram C n = Functor (FinSysCat n) C

-- do we need this?
-- isFinLimit : {C : Category ℓ ℓ'} {n : ℕ} → FinDiagram C n → C .Category.ob → Type _
-- isFinLimit diag head = isLimit diag head

-- FinLimit : {C : Category ℓ ℓ'} {n : ℕ} → FinDiagram C n → Type _
-- FinLimit diag = Limit diag


-- In distributive lattices finite limits are joins
module _ (L' : DistLattice ℓ) where
 private
  L = fst L'
  LCat = (DistLatticeCategory L') ^op

 open DistLatticeStr (snd L')
 open Join L'
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 open PosetStr (IndPoset .snd)
 open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L'))
      using (∧≤RCancel ; ∧≤LCancel)
 open Order (DistLattice→Lattice L')

 open Category LCat
 open Functor

 FinVec→FinDiagram : {n : ℕ} → FinVec L n → FinDiagram LCat n
 F-ob (FinVec→FinDiagram α) (sing i) = α i
 F-ob (FinVec→FinDiagram α) (pair i j) = α i ∧l α j
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = sing j} p =
       subst (λ k → Hom[ α i , α k ]) p id
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = pair j k} (inl p) =
       subst (λ l → Hom[ α i , α l ∧l α k ]) p (≤m→≤j _ _ (∧≤RCancel _ _))
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = pair j k} (inr p) =
       subst (λ l → Hom[ α i , α j ∧l α l ]) p (≤m→≤j _ _ (∧≤LCancel _ _))
 F-hom (FinVec→FinDiagram α) {x = pair i j} {y = pair k l} (p , q) =
       subst2 (λ m o → Hom[ α i ∧l α j , α m ∧l α o ]) p q id
 F-id (FinVec→FinDiagram α) = is-prop-valued _ _ _ _
 F-seq (FinVec→FinDiagram α) _ _ = is-prop-valued _ _ _ _

 open isLimit
 open NatTrans

 joinIsFinLim : {n : ℕ} (α : FinVec L n) → isLimit (FinVec→FinDiagram α) (⋁ α)
 N-ob (cone (joinIsFinLim α)) (sing i) = {!!} -- αᵢ≤⋁α
 N-ob (cone (joinIsFinLim α)) (pair i j) = {!!} -- αᵢ∧αⱼ≤⋁α
 N-hom (cone (joinIsFinLim α)) _ = is-prop-valued _ _ _ _
 fst (fst (up (joinIsFinLim α) ν)) = ⋁IsMax α _ (λ i → ν .N-ob (sing i))
 snd (fst (up (joinIsFinLim α) ν)) = {!!}
 snd (up (joinIsFinLim α) ν) (v≥⋁α , νComp) = {!!}
