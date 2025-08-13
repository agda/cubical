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
open import Cubical.Data.Nat.MoreOrderProperties

double : ℕ → ℕ
double n = n + n

private
  2Sn=2n+2 : {n : ℕ} → double (suc n) ≡ double n + 2
  2Sn=2n+2 =  solveℕ!

  doubleGrows : (n : ℕ) → double n < double (suc n)
  doubleGrows n = double n
                    ≡<⟨ refl ⟩
                  n + n
                    <≡⟨ <SumLeft ⟩
                  n + n + 2
                    ≡⟨ sym 2Sn=2n+2 ⟩
                  double (suc n) ∎

  ¬2n+2+k<2n : (n : ℕ) → (k : ℕ) → ¬ ( suc (suc k) + double n < double (suc n))
  ¬2n+2+k<2n n k p = ex-falso (¬-<-zero k<0) where
      2n+k+2<2n+2 : double n + suc (suc k) < double n + 2
      2n+k+2<2n+2 = double n + suc (suc k)
                      ≡<⟨ +-comm (n + n) (suc (suc k)) ⟩
                    suc (suc k) + double n
                      <≡⟨ p ⟩
                    double (suc n)
                      ≡⟨ 2Sn=2n+2 ⟩
                    double n + 2 ∎
      k+2<2 : suc (suc k) < suc (suc 0)
      k+2<2 = <-k+-cancel 2n+k+2<2n+2
      k<0 : k < 0
      k<0 = pred-≤-pred (pred-≤-pred k+2<2)

doubleInc : isIncreasing double
doubleInc = strengthenIncreasing double doubleGrows

private
  partitionDouble≅ℕ⊎ℕ : Iso (partition double refl doubleInc) (ℕ ⊎ ℕ)
  Iso.fun partitionDouble≅ℕ⊎ℕ (n , zero        , p) = inl n
  Iso.fun partitionDouble≅ℕ⊎ℕ (n , suc zero    , p) = inr n
  Iso.fun partitionDouble≅ℕ⊎ℕ (n , suc (suc k) , p) = ex-falso (¬2n+2+k<2n n k p)
  Iso.inv partitionDouble≅ℕ⊎ℕ (inl n) = n , zero , doubleGrows n
  Iso.inv partitionDouble≅ℕ⊎ℕ (inr n) = n , 1 , (
                 1 + n + n <≡⟨ <SumRight {k = 0} ⟩
                 2 + n + n  ≡⟨ +-comm 2 (n + n)  ⟩
                 n + n + 2  ≡⟨ sym 2Sn=2n+2      ⟩
                 double (suc n) ∎         )
  Iso.rightInv partitionDouble≅ℕ⊎ℕ (inl n) = refl
  Iso.rightInv partitionDouble≅ℕ⊎ℕ (inr n) = refl
  Iso.leftInv partitionDouble≅ℕ⊎ℕ (k , zero        , p) = ΣPathP (refl , ΣPathPProp (λ a → isProp≤) refl)
  Iso.leftInv partitionDouble≅ℕ⊎ℕ (k , suc zero    , p) = ΣPathP (refl , ΣPathPProp (λ a → isProp≤) refl)
  Iso.leftInv partitionDouble≅ℕ⊎ℕ (k , suc (suc i) , p) = ex-falso $ ¬2n+2+k<2n k i p

  partitionDouble≅ℕ : Iso (partition double refl doubleInc) ℕ
  partitionDouble≅ℕ = partition≅ℕ double refl doubleInc

ℕ≅ℕ⊎ℕ : Iso (ℕ ⊎ ℕ) ℕ
ℕ≅ℕ⊎ℕ = compIso (invIso partitionDouble≅ℕ⊎ℕ) partitionDouble≅ℕ
