-- define ⋁ and ⋀ as the bigOps of a DistLattice when interpreted
-- as a join/meet semilattice

module Cubical.Algebra.DistLattice.BigOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData
open import Cubical.Data.Bool hiding (_≤_)

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
open import Cubical.Relation.Binary.Order.Poset


private
  variable
    ℓ ℓ' : Level

module KroneckerDelta (L' : DistLattice ℓ) where
 private
  L = fst L'
 open DistLatticeStr (snd L')

 δ : {n : ℕ} (i j : Fin n) → L
 δ i j = if i == j then 1l else 0l



module Join (L' : DistLattice ℓ) where
 private
  L = fst L'
 open DistLatticeStr (snd L')
 open MonoidBigOp (Semilattice→Monoid (Lattice→JoinSemilattice (DistLattice→Lattice L')))
 open LatticeTheory (DistLattice→Lattice L')
 open KroneckerDelta L'

 ⋁ = bigOp
 ⋁Ext = bigOpExt
 ⋁0l = bigOpε
 ⋁Last = bigOpLast

 ⋁Split : ∀ {n} → (V W : FinVec L n) → ⋁ (λ i → V i ∨l W i) ≡ ⋁ V ∨l ⋁ W
 ⋁Split = bigOpSplit ∨lComm

 ⋁Split++ : ∀ {n m : ℕ} (V : FinVec L n) (W : FinVec L m)
           → ⋁ (V ++Fin W) ≡ ⋁ V ∨l ⋁ W
 ⋁Split++ = bigOpSplit++

 ⋁Meetrdist : ∀ {n} → (x : L) → (V : FinVec L n)
                → x ∧l ⋁ V ≡ ⋁ λ i → x ∧l V i
 ⋁Meetrdist {n = zero}  x _ = 0lRightAnnihilates∧l x
 ⋁Meetrdist {n = suc n} x V =
   x ∧l (V zero ∨l ⋁ (V ∘ suc))              ≡⟨ ∧lLdist∨l _ _ _ ⟩ --Ldist and Rdist wrong way around?
   (x ∧l V zero) ∨l (x ∧l ⋁ (V ∘ suc))       ≡⟨ (λ i → (x ∧l V zero) ∨l ⋁Meetrdist x (V ∘ suc) i) ⟩
   (x ∧l V zero) ∨l ⋁ (λ i → x ∧l V (suc i)) ∎

 ⋁Meetldist : ∀ {n} → (x : L) → (V : FinVec L n)
                → (⋁ V) ∧l x ≡ ⋁ λ i → V i ∧l x
 ⋁Meetldist {n = zero}  x _ = 0lLeftAnnihilates∧l x
 ⋁Meetldist {n = suc n} x V =
   (V zero ∨l ⋁ (V ∘ suc)) ∧l x              ≡⟨ ∧lRdist∨l _ _ _ ⟩
   (V zero ∧l x) ∨l ((⋁ (V ∘ suc)) ∧l x)     ≡⟨ (λ i → (V zero ∧l x) ∨l ⋁Meetldist x (V ∘ suc) i) ⟩
   (V zero ∧l x) ∨l ⋁ (λ i → V (suc i) ∧l x) ∎

 ⋁Meetr0 : ∀ {n} → (V : FinVec L n) → ⋁ (λ i → V i ∧l 0l) ≡ 0l
 ⋁Meetr0 V = sym (⋁Meetldist 0l V) ∙ 0lRightAnnihilates∧l _

 ⋁Meet0r : ∀ {n} → (V : FinVec L n) → ⋁ (λ i → 0l ∧l V i) ≡ 0l
 ⋁Meet0r V = sym (⋁Meetrdist 0l V) ∙ 0lLeftAnnihilates∧l _

 ⋁Meetr1 : (n : ℕ) (V : FinVec L n) → (j : Fin n) → ⋁ (λ i → V i ∧l δ i j) ≡ V j
 ⋁Meetr1 (suc n) V zero = (λ k → ∧lRid (V zero) k ∨l ⋁Meetr0 (V ∘ suc) k) ∙ ∨lRid (V zero)
 ⋁Meetr1 (suc n) V (suc j) =
    (λ i → 0lRightAnnihilates∧l (V zero) i ∨l ⋁ (λ x → V (suc x) ∧l δ x j))
    ∙∙ ∨lLid _ ∙∙ ⋁Meetr1 n (V ∘ suc) j

 ⋁Meet1r : (n : ℕ) (V : FinVec L n) → (j : Fin n) → ⋁ (λ i → (δ j i) ∧l V i) ≡ V j
 ⋁Meet1r (suc n) V zero = (λ k → ∧lLid (V zero) k ∨l ⋁Meet0r (V ∘ suc) k) ∙ ∨lRid (V zero)
 ⋁Meet1r (suc n) V (suc j) =
   (λ i → 0lLeftAnnihilates∧l (V zero) i ∨l ⋁ (λ i → (δ j i) ∧l V (suc i)))
   ∙∙ ∨lLid _ ∙∙ ⋁Meet1r n (V ∘ suc) j

 -- inequalities of big joins
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 ind≤⋁ = ind≤bigOp
 ⋁IsMax = bigOpIsMax
 ≤-⋁Ext = ≤-bigOpExt


module JoinMap {L : DistLattice ℓ} {L' : DistLattice ℓ'} (φ : DistLatticeHom L L') where
  private module L = Join L
  private module L' = Join L'
  open BigOpMap (LatticeHom→JoinSemilatticeHom φ)

  pres⋁ : {n : ℕ} (U : FinVec ⟨ L ⟩ n) → φ .fst (L.⋁ U) ≡ L'.⋁ (φ .fst ∘ U)
  pres⋁ = presBigOp


module Meet (L' : DistLattice ℓ) where
 private
  L = fst L'
 open DistLatticeStr (snd L')
 open MonoidBigOp (Semilattice→Monoid (Lattice→MeetSemilattice (DistLattice→Lattice L')))
 -- extra DistLattice→MeetMonoid?
 open LatticeTheory (DistLattice→Lattice L')
 open KroneckerDelta L'

 ⋀ = bigOp
 ⋀Ext = bigOpExt
 ⋀1l = bigOpε
 ⋀Last = bigOpLast

 ⋀Split : ∀ {n} → (V W : FinVec L n) → ⋀ (λ i → V i ∧l W i) ≡ ⋀ V ∧l ⋀ W
 ⋀Split = bigOpSplit ∧lComm

 ⋀Joinrdist : ∀ {n} → (x : L) → (V : FinVec L n)
                → x ∨l ⋀ V ≡ ⋀ λ i → x ∨l V i
 ⋀Joinrdist {n = zero}  x _ = 1lRightAnnihilates∨l x
 ⋀Joinrdist {n = suc n} x V =
   x ∨l (V zero ∧l ⋀ (V ∘ suc))              ≡⟨ ∨lLdist∧l _ _ _ ⟩ --Ldist and Rdist wrong way around?
   (x ∨l V zero) ∧l (x ∨l ⋀ (V ∘ suc))       ≡⟨ (λ i → (x ∨l V zero) ∧l ⋀Joinrdist x (V ∘ suc) i) ⟩
   (x ∨l V zero) ∧l ⋀ (λ i → x ∨l V (suc i)) ∎

 ⋀Joinldist : ∀ {n} → (x : L) → (V : FinVec L n)
                → (⋀ V) ∨l x ≡ ⋀ λ i → V i ∨l x
 ⋀Joinldist {n = zero}  x _ = 1lLeftAnnihilates∨l x
 ⋀Joinldist {n = suc n} x V =
   (V zero ∧l ⋀ (V ∘ suc)) ∨l x              ≡⟨ ∨lRdist∧l _ _ _ ⟩
   (V zero ∨l x) ∧l ((⋀ (V ∘ suc)) ∨l x)     ≡⟨ (λ i → (V zero ∨l x) ∧l ⋀Joinldist x (V ∘ suc) i) ⟩
   (V zero ∨l x) ∧l ⋀ (λ i → V (suc i) ∨l x) ∎

 ⋀Joinr1 : ∀ {n} → (V : FinVec L n) → ⋀ (λ i → V i ∨l 1l) ≡ 1l
 ⋀Joinr1 V = sym (⋀Joinldist 1l V) ∙ 1lRightAnnihilates∨l _

 ⋀Join1r : ∀ {n} → (V : FinVec L n) → ⋀ (λ i → 1l ∨l V i) ≡ 1l
 ⋀Join1r V = sym (⋀Joinrdist 1l V) ∙ 1lLeftAnnihilates∨l _


module MeetMap {L : DistLattice ℓ} {L' : DistLattice ℓ'} (φ : DistLatticeHom L L') where
  private module L = Meet L
  private module L' = Meet L'
  open BigOpMap (LatticeHom→MeetSemilatticeHom φ)

  pres⋀ : {n : ℕ} (U : FinVec ⟨ L ⟩ n) → φ .fst (L.⋀ U) ≡ L'.⋀ (φ .fst ∘ U)
  pres⋀ = presBigOp
