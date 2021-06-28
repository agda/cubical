{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.RadicalIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_ ; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order

open import Cubical.HITs.PropositionalTruncation renaming (elim to PTelim)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

module _ (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'
 open BinomialThm R'
 open isCommIdeal


 √ : ℙ R → ℙ R --\surd
 √ I x = (∃[ n ∈ ℕ ] x ^ n ∈ I) , isPropPropTrunc

 ^∈√→∈√ : ∀ (I : ℙ R) (x : R) (n : ℕ) → x ^ n ∈ √ I → x ∈ √ I
 ^∈√→∈√ I x n =
         map (λ { (m , [xⁿ]ᵐ∈I) → (n ·ℕ m) , subst (_∈ I) (sym (^-rdist-·ℕ x n m)) [xⁿ]ᵐ∈I })

 ∈→∈√ : ∀ (I : ℙ R) (x : R) → x ∈ I → x ∈ √ I
 ∈→∈√ I _ x∈I = ∣ 1 , subst (_∈ I) (sym (·Rid _)) x∈I ∣

 √OfIdealIsIdeal : ∀ (I : ℙ R) → isCommIdeal R' I → isCommIdeal R' (√ I)
 +Closed (√OfIdealIsIdeal I ici) {x = x} {y = y} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ n ∈ ℕ ] x ^ n ∈ I → Σ[ n ∈ ℕ ] y ^ n ∈ I → Σ[ n ∈ ℕ ] (x + y) ^ n ∈ I
  +ClosedΣ (n , xⁿ∈I) (m , yᵐ∈I) = (n +ℕ m)
                                  , subst (_∈ I) (sym (BinomialThm (n +ℕ m) _ _)) ∑Binomial∈I
   where
   binomialCoeff∈I : ∀ i → ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i) ∈ I
   binomialCoeff∈I i with ≤-+-split n m (toℕ i) (pred-≤-pred (toℕ<n i))
   ... | inl n≤i = subst (_∈ I) (sym path) (·Closed ici _ xⁿ∈I)
    where
    useSolver : ∀ a b c d → a · (b · c) · d ≡ a · b · d · c
    useSolver = solve R'
    path : ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡ ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n
    path = ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ k → ((n +ℕ m) choose toℕ i) · x ^ k · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (≤-∸-+-cancel n≤i)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ ((toℕ i ∸ n) +ℕ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ z → ((n +ℕ m) choose toℕ i) · z · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (·-of-^-is-^-of-+ x (toℕ i ∸ n) n)) ⟩
           ((n +ℕ m) choose toℕ i) · (x ^ (toℕ i ∸ n) · x ^ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ useSolver _ _ _ _ ⟩
           ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n ∎

   ... | inr m≤n+m-i = subst (_∈ I) (sym path) (·Closed ici _ yᵐ∈I)
    where
    path : ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡ ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m
    path = ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ k → ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ k)
                 (sym (≤-∸-+-cancel m≤n+m-i)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (((n +ℕ m ∸ toℕ i) ∸ m) +ℕ m)
         ≡⟨ cong (((n +ℕ m) choose toℕ i) · x ^ toℕ i ·_)
                 (sym (·-of-^-is-^-of-+ y ((n +ℕ m ∸ toℕ i) ∸ m) m)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · (y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m)
         ≡⟨ ·Assoc _ _ _ ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m ∎

   ∑Binomial∈I : ∑ (BinomialVec (n +ℕ m) x y) ∈ I
   ∑Binomial∈I = ∑Closed R' (I , ici) (BinomialVec (n +ℕ m) _ _) binomialCoeff∈I
 contains0 (√OfIdealIsIdeal I ici) =
   ∣ 1 , subst (_∈ I) (sym (0LeftAnnihilates 1r)) (ici .contains0) ∣
 ·Closed (√OfIdealIsIdeal I ici) r =
   map λ { (n , xⁿ∈I) → n , subst (_∈ I) (sym (^-ldist-· r _ n)) (ici .·Closed (r ^ n) xⁿ∈I) }


 -- important lemma for characterization of th Zariski lattice
 √FGIdealChar : {n : ℕ} (𝔞 : FinVec R n) (I : CommIdeal R')
                → √ (fst (R' -⟨ 𝔞 ⟩)) ⊆ √ (fst I) ≃ (∀ i → 𝔞 i ∈ √ (fst I))
 √FGIdealChar 𝔞 I = isEquivPropBiimpl→Equiv (⊆-isProp (√ (fst (R' -⟨ 𝔞 ⟩))) (√ (fst I)))
                                              (isPropΠ (λ _ → √ (fst I) _ .snd)) .fst
                                              (ltrImpl , rtlImpl)
  where
  open KroneckerDelta (CommRing→Ring R')
  ltrImpl : √ (fst (R' -⟨ 𝔞 ⟩)) ⊆ √ (fst I) → (∀ i → 𝔞 i ∈ √ (fst I))
  ltrImpl √⟨𝔞⟩⊆√I i = √⟨𝔞⟩⊆√I _ (∈→∈√ (fst (R' -⟨ 𝔞 ⟩)) (𝔞 i)
                                        ∣ (λ j → δ i j) , sym (∑Mul1r _ _ i) ∣)

  rtlImpl : (∀ i → 𝔞 i ∈ √ (fst I)) → √ (fst (R' -⟨ 𝔞 ⟩)) ⊆ √ (fst I)
  rtlImpl ∀i→𝔞i∈√I x = PTelim (λ _ → √ (fst I) x .snd)
                                λ { (n , xⁿ∈⟨𝔞⟩) → ^∈√→∈√ (fst I) x n (elimHelper _ xⁿ∈⟨𝔞⟩) }
   where
   isCommIdeal√I = √OfIdealIsIdeal (fst I) (snd I)
   elimHelper : ∀ (y : R) → y ∈ (fst (R' -⟨ 𝔞 ⟩)) → y ∈ √ (fst I)
   elimHelper y = PTelim (λ _ → √ (fst I) y .snd)
                   λ { (α , y≡∑α𝔞) → subst (_∈ √ (fst I)) (sym y≡∑α𝔞)
                                           (∑Closed R' (√ (fst I) , isCommIdeal√I)
                                           (λ i → α i · 𝔞 i)
                                           (λ i → isCommIdeal√I .·Closed (α i) (∀i→𝔞i∈√I i))) }
