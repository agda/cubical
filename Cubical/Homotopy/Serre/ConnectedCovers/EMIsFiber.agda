-- containing a proof that the fibers in the Whitehead tower are K(πₙ₊₁X,n)
{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.EMIsFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.ConnectedCovers.Base
open import Cubical.Homotopy.Serre.ConnectedCovers.K-G-n-facts
open import Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts

open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.LongExactSequence
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.PuppeLemma

private
  variable
    ℓ : Level

πConnCov : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
  → AbGroupEquiv (πAb k (X < (suc n) >)) (πAb k X)
πConnCov X n k hnk =
  ExactSequenceEquiv (X < (suc n) >) X (hLevelTrunc∙ (3 + n) X) k
  ( AlternativeFiberSeq X n)
  ( πAbOfHLevelTrunc' X n k hnk)
  ( πAbOfHLevelTrunc X n k hnk)

πConnCovEq : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
  → (πAb k (X < (suc n) >)) ≡ (πAb k X)
πConnCovEq X n k hnk =
  equivFun (AbGroupPath (πAb k (X < (suc n) >)) (πAb k X)) (πConnCov X n k hnk)


ConnCovHLevelTruncIsConn : (X : Pointed ℓ) (m n : ℕ)
  → isConnected (2 + n) (typ (hLevelTrunc∙ m (X < n >)))
ConnCovHLevelTruncIsConn X m n =
  ConnToHLevelTruncConn (typ (X < n >)) m (2 + n) (ConnCovIsConn X n)


TruncConnCovEqEM∙ : (X : Pointed ℓ) (n : ℕ)
  → hLevelTrunc∙ (4 + n) (X < (suc n) >) ≡ (EM∙ (πAb n X) (2 + n))
TruncConnCovEqEM∙ X n =
  EMUniqueness (hLevelTrunc∙ (4 + n) (X < (suc n) >)) n
  ( ConnCovHLevelTruncIsConn X (4 + n) (suc n))
  ( isOfHLevelTrunc (4 + n))
    ∙ EMAbGrpEq (πAb n (hLevelTrunc∙ (4 + n) (X < (suc n) >)))
  ( πAb n (X < (suc n) >)) (2 + n)
  ( AbGrpTruncEq (X < (suc n) >) n)
  ∙ EMAbGrpEq (πAb n (X < suc n >)) (πAb n X) (2 + n)
  ( πConnCov X n n ≤-refl)


-- has trouble type-checking (> 1 hour) without lossy-unification
EM<->FibSeq : (X : Pointed ℓ) (n : ℕ)
  → FiberSeq (X < (2 + n) >) (X < (suc n) >) (EM∙ (πAb n X) (2 + n))
EM<->FibSeq X n =
  BaseEqFiberSeq
  ( TruncConnCovEqEM∙ X n)
  ( ConnCovFiberSeq X (suc n))


FibSeqEqEM∙ : (X : Pointed ℓ) (n : ℕ)
  → FiberSeq (Ω (EM∙ (πAb n X) (2 + n))) (X < (2 + n) >) (X < (suc n) >)
  ≡ FiberSeq (EM∙ (πAb n X) (suc n)) (X < (2 + n) >) (X < (suc n) >)
FibSeqEqEM∙ X n i =
  FiberSeq
  ( (EM≃ΩEM+1∙ {G = πAb n X} (suc n)) (~ i))
  ( X < (2 + n) >)
  ( X < (suc n) >)

<->EMFibSeq : (X : Pointed ℓ) (n : ℕ)
  → FiberSeq (EM∙ (πAb n X) (suc n)) (X < (2 + n) >) (X < (suc n) >)
<->EMFibSeq X n = transport (FibSeqEqEM∙ X n) (puppe (EM<->FibSeq X n))
