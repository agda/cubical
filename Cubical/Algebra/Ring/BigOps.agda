-- define ∑ and ∏ as the bigOps of a Ring when interpreted
-- as an additive/multiplicative monoid

module Cubical.Algebra.Ring.BigOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.Monoid.BigOp
import Cubical.Algebra.Semiring.BigOps as Semiring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

private
  variable
    ℓ ℓ' : Level

module KroneckerDelta (R : Ring ℓ) where
  δ = Semiring.KroneckerDelta.δ (Ring→Semiring R)

module Sum (R : Ring ℓ) where
  open Semiring.Sum (Ring→Semiring R) public
  open RingStr (snd R)
  open RingTheory R

  ∑Dist- : ∀ {n : ℕ} (V : FinVec (fst R) n) → ∑ (λ i → - V i) ≡ - ∑ V
  ∑Dist- V = ∑Ext (λ i → -IsMult-1 (V i)) ∙ sym (∑Mulrdist _ V) ∙ sym (-IsMult-1 _)

module SumMap
  (Ar@(A , Astr) : Ring ℓ)
  (Br@(B , Bstr) : Ring ℓ')
  (f'@(f , fstr) : RingHom Ar Br)
  where

  open IsRingHom fstr

  open RingStr Astr using ()
    renaming
    ( _+_ to _+A_ )

  open RingStr Bstr using ()
    renaming
    ( _+_ to _+B_ )

  ∑Map : {n : ℕ} → (V : FinVec A n) → f (Sum.∑ Ar V) ≡ Sum.∑ Br (λ k → f (V k))
  ∑Map {n = zero} V = pres0
  ∑Map {n = suc n} V =
                       f ((V zero) +A helper) ≡⟨ pres+ (V zero) helper ⟩
                       ((f (V zero)) +B (f helper)) ≡⟨ cong (λ X → f (V zero) +B X) (∑Map (λ k → (V ∘ suc) k)) ⟩
                       Sum.∑ Br (λ k → f (V k)) ∎
                     where
                     helper : _
                     helper = foldrFin _+A_ (RingStr.0r (snd Ar)) (λ x → V (suc x))

-- anything interesting to prove here?
module Product (R' : Ring ℓ) where
 private
  R = fst R'
 open RingStr (snd R')
 open RingTheory R'
 open MonoidBigOp (Ring→MultMonoid R')

 ∏ = bigOp
 ∏Ext = bigOpExt
 ∏0r = bigOpε
 ∏Last = bigOpLast
 ΠSplit++ = bigOpSplit++

-- only holds in CommRings!
-- ∏Split : ∀ {n} → (V W : FinVec R n) → ∏ (λ i → V i · W i) ≡ ∏ V · ∏ W
-- ∏Split = bigOpSplit MultR' ·-comm
