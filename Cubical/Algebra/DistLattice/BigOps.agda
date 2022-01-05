-- define ⋁ and ⋀ as the bigOps of a Ring when interpreted
-- as an additive/multiplicative monoid

{-# OPTIONS --safe #-}
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
open import Cubical.Relation.Binary.Poset


private
  variable
    ℓ : Level

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
 -- extra DistLattice→JoinMonoid?
 open LatticeTheory (DistLattice→Lattice L')
 open KroneckerDelta L'

 ⋁ = bigOp
 ⋁Ext = bigOpExt
 ⋁0l = bigOpε
 ⋁Last = bigOpLast

 ⋁Split : ∀ {n} → (V W : FinVec L n) → ⋁ (λ i → V i ∨l W i) ≡ ⋁ V ∨l ⋁ W
 ⋁Split = bigOpSplit ∨lComm

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
 open PosetReasoning IndPoset
 open PosetStr (IndPoset .snd) hiding (_≤_)

 ind≤⋁ : {n : ℕ} (U : FinVec L n) (i : Fin n) → U i ≤ ⋁ U
 ind≤⋁ {n = suc n} U zero = ∨≤RCancel _ _
 ind≤⋁ {n = suc n} U (suc i) = is-trans _ (⋁ (U ∘ suc)) _ (ind≤⋁ (U ∘ suc) i) (∨≤LCancel _ _)

 ⋁IsMax : {n : ℕ} (U : FinVec L n) (x : L) → (∀ i → U i ≤ x) → ⋁ U ≤ x
 ⋁IsMax {n = zero} _ _ _ = ∨lLid _
 ⋁IsMax {n = suc n} U x U≤x =
   ⋁ U                   ≤⟨ is-refl _ ⟩
   U zero ∨l ⋁ (U ∘ suc) ≤⟨ ≤-∨LPres _ _ _ (⋁IsMax _ _ (U≤x ∘ suc)) ⟩
   U zero ∨l x            ≤⟨ ∨lIsMax _ _ _ (U≤x zero) (is-refl x) ⟩
   x ◾

 ≤-⋁Ext : {n : ℕ} (U W : FinVec L n) → (∀ i → U i ≤ W i) → ⋁ U ≤ ⋁ W
 ≤-⋁Ext {n = zero} U W U≤W = is-refl 0l
 ≤-⋁Ext {n = suc n} U W U≤W =
   ⋁ U                   ≤⟨ is-refl _ ⟩
   U zero ∨l ⋁ (U ∘ suc) ≤⟨ ≤-∨Pres _ _ _ _ (U≤W zero) (≤-⋁Ext _ _ (U≤W ∘ suc)) ⟩
   W zero ∨l ⋁ (W ∘ suc) ≤⟨ is-refl _ ⟩
   ⋁ W ◾

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
