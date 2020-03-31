{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11 where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude

open import Cubical.Data.HomotopyGroup
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

Lemma7-5-11 : ∀{ℓ} {A : Type ℓ} {a : A} → (n : ℕ₋₂) → (is- (suc₋₂ n) -ConnectedType A) → is- n -Connected (λ (x : Unit) → a)
Lemma7-5-11 {A = A} {a = a} n isCon = conInd-iii→i (λ _ → a) _ λ P → ((λ g → fst (helper P (g tt)))) ,
                                                                          (λ g  → funExt (λ x → snd (helper P (g x))))
  where
  helper : ∀ {ℓ} (P : (A → HLevel ℓ (2+ n) )) → (u : fst (P a)) → Σ ((a : A) → fst (P a)) λ f → f a ≡ u
  helper {ℓ} P u = ((λ x → transport (λ i → Bs3 x (~ i)) (transport (λ i → Bs3 a i) u))) ,
                   λ j → hcomp ((λ k → λ{(j = i0) → refl {x = ((transport (λ i → Bs3 a (~ i))
                                                                          (transport (λ i → Bs3 a i) u)))} k
                                       ; (j = i1) → transportRefl (transportRefl u k) k}))
                               (transport (λ i → Bs3 a (~ i ∧ ~ j))
                                          (transport (λ i → Bs3 a (i ∧ (~ j))) u))
    where
    Cor759 : ∀ {ℓ'} (n : ℕ₋₂) → is- n -ConnectedType A → (B : HLevel ℓ' (2+ n)) → isEquiv (λ (b : (fst B)) → λ (a : A) → b)
    Cor759 n isCon B = isEquivLemma (conInd-i→ii (λ (x : A) → tt) n (conTyp→conTyp2 n A isCon) (λ _ → B))
      where

      isEquivLemma : isEquiv (indConFun {A = A} {B = Unit} (λ x → tt) (λ _ → B)) → isEquiv (λ (b : (fst B)) → λ (a : A) → b)
      isEquivLemma record { equiv-proof = eq } = record { equiv-proof = λ y → ((eq y .fst .fst tt) , (eq y .fst .snd)) ,
                                                                              λ z i → ((cong (λ y → (fst y) tt) ((eq y .snd) ((λ x → fst z) , snd z))) i) ,
                                                                                       (cong (λ y → (snd y)) ((eq y .snd) ((λ x → fst z) , snd z))) i}

    Bs2 : Σ (HLevel ℓ (2+ n)) λ B → P ≡ λ (a : A) → B
    Bs2 = (equiv-proof (Cor759 (suc₋₂ n) isCon (HLevel ℓ (2+ n) , isOfHLevelHLevel _ )))
          P .fst .fst ,
          sym ((equiv-proof (Cor759 (suc₋₂ n) isCon (HLevel ℓ (2+ n) , isOfHLevelHLevel _ ))) P .fst .snd)

    B* : Type ℓ
    B* = fst (fst Bs2)

    Bs3 : (a : A) → fst (P a) ≡ B*
    Bs3 a = cong (λ x → fst (x a)) (snd Bs2)
