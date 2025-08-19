module Cubical.Data.Nat.Bijections.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open <-Reasoning

open import Cubical.Tactics.NatSolver
open import Cubical.Data.Nat.Bijections.IncreasingFunction

private
  2Sn=2n+2 : {n : ℕ} → doubleℕ (suc n) ≡ doubleℕ n + 2
  2Sn=2n+2 = +-comm 2 (doubleℕ _)

  doubleGrows : (n : ℕ) → doubleℕ n < doubleℕ (suc n)
  doubleGrows n = <-trans <-suc <-suc

  ¬2n+2+k<2n : (n : ℕ) → (k : ℕ) → ¬ ( suc (suc k) + doubleℕ n < doubleℕ (suc n))
  ¬2n+2+k<2n n k p = ex-falso (¬-<-zero k<0) where
      2n+k+2<2n+2 : doubleℕ n + suc (suc k) < doubleℕ n + 2
      2n+k+2<2n+2 = doubleℕ n + suc (suc k)
                      ≡<⟨ +-comm (doubleℕ n) (suc (suc k)) ⟩
                    suc (suc k) + doubleℕ n
                      <≡⟨ p ⟩
                    doubleℕ (suc n)
                      ≡⟨ 2Sn=2n+2 ⟩
                    doubleℕ n + 2 ∎
      k+2<2 : suc (suc k) < suc (suc 0)
      k+2<2 = <-k+-cancel 2n+k+2<2n+2
      k<0 : k < 0
      k<0 = pred-≤-pred (pred-≤-pred k+2<2)

doubleInc : isStrictlyIncreasing doubleℕ
doubleInc = sucIncreasing→StrictlyIncreasing doubleℕ doubleGrows

private
  partitionDoubleℕ≅ℕ⊎ℕ : Iso (partition doubleℕ refl doubleInc) (ℕ ⊎ ℕ)
  Iso.fun partitionDoubleℕ≅ℕ⊎ℕ (n , zero        , p) = inl n
  Iso.fun partitionDoubleℕ≅ℕ⊎ℕ (n , suc zero    , p) = inr n
  Iso.fun partitionDoubleℕ≅ℕ⊎ℕ (n , suc (suc k) , p) = ex-falso (¬2n+2+k<2n n k p)
  Iso.inv partitionDoubleℕ≅ℕ⊎ℕ (inl n) = n , zero , doubleGrows n
  Iso.inv partitionDoubleℕ≅ℕ⊎ℕ (inr n) = n , 1 , <-suc
  Iso.rightInv partitionDoubleℕ≅ℕ⊎ℕ (inl n) = refl
  Iso.rightInv partitionDoubleℕ≅ℕ⊎ℕ (inr n) = refl
  Iso.leftInv partitionDoubleℕ≅ℕ⊎ℕ (k , zero        , p) = ΣPathP (refl , ΣPathPProp (λ a → isProp≤) refl)
  Iso.leftInv partitionDoubleℕ≅ℕ⊎ℕ (k , suc zero    , p) = ΣPathP (refl , ΣPathPProp (λ a → isProp≤) refl)
  Iso.leftInv partitionDoubleℕ≅ℕ⊎ℕ (k , suc (suc i) , p) = ex-falso $ ¬2n+2+k<2n k i p

  partitionDoubleℕ≅ℕ : Iso (partition doubleℕ refl doubleInc) ℕ
  partitionDoubleℕ≅ℕ = partition≅ℕ doubleℕ refl doubleInc

ℕ⊎ℕ≅ℕ : Iso (ℕ ⊎ ℕ) ℕ
ℕ⊎ℕ≅ℕ = compIso (invIso partitionDoubleℕ≅ℕ⊎ℕ) partitionDoubleℕ≅ℕ
