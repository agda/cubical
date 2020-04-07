{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11 where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.HomotopyGroup
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

private

    Cor759 : ∀ {ℓ ℓ'} {A : Type ℓ} (n : ℕ₋₂) → is- n -ConnectedType A → (B : HLevel ℓ' (2+ n)) → isEquiv (λ (b : (fst B)) → λ (a : A) → b)
    Cor759 {A = A} n isCon B = isEquivLemma (conInd-i→ii (λ (x : A) → tt) n (conTyp→conTyp2 n A isCon) (λ _ → B))
      where

      isEquivLemma : isEquiv (indConFun {A = A} {B = Unit} (λ x → tt) (λ _ → B)) → isEquiv (λ (b : (fst B)) → λ (a : A) → b)
      isEquivLemma record { equiv-proof = eq } = record { equiv-proof = λ y → ((eq y .fst .fst tt) , (eq y .fst .snd)) ,
                                                                              λ z i → ((cong (λ y → (fst y) tt) ((eq y .snd) ((λ x → fst z) , snd z))) i) ,
                                                                                       (cong (λ y → (snd y)) ((eq y .snd) ((λ x → fst z) , snd z))) i}

    Cor759← : ∀ {ℓ} {A : Type ℓ} (n : ℕ₋₂) → (∀ {ℓ'} (B : HLevel ℓ' (2+ n)) → isEquiv (λ (b : (fst B)) → λ (a : A) → b)) → is- n -ConnectedType A
    Cor759← {A = A} n BEq = conTyp2→conTyp n A (conInd-iii→i (λ x → tt) n λ {ℓ'} P → conInd-ii→iii (λ x → tt) n P (compEquiv ((λ Q → Q tt) , helper P) (_ , BEq (P tt)) .snd))
      where
      helper : ∀ {ℓ'} → (P : Unit → HLevel ℓ' (2+ n)) → isEquiv {A = ((b : Unit) → fst (P b))} λ Q → Q tt -- ∀ {ℓ'} P (ℓ'' : Unit) → fst (P₁ ℓ'')
      helper P = isoToIsEquiv (iso (λ Q → Q tt) invFun (λ b → refl) λ b → refl)
        where
        invFun : fst (P tt) → (b : Unit) → fst (P b)
        invFun Q tt = Q

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
    Bs2 : Σ (HLevel ℓ (2+ n)) λ B → P ≡ λ (a : A) → B
    Bs2 = (equiv-proof (Cor759 (suc₋₂ n) isCon (HLevel ℓ (2+ n) , isOfHLevelHLevel _ )))
          P .fst .fst ,
          sym ((equiv-proof (Cor759 (suc₋₂ n) isCon (HLevel ℓ (2+ n) , isOfHLevelHLevel _ ))) P .fst .snd)

    B* : Type ℓ
    B* = fst (fst Bs2)

    Bs3 : (a : A) → fst (P a) ≡ B*
    Bs3 a = cong (λ x → fst (x a)) (snd Bs2)



Lemma7-5-11← : ∀{ℓ} {A : Type ℓ} {a : A} → (n : ℕ₋₂) → is- n -Connected (λ (x : Unit) → a) → (is- (suc₋₂ n) -ConnectedType A)
Lemma7-5-11← {A = A} {a = a} n iscon = Cor759← (suc₋₂ n) lemmas.isEquivMap
  where
  module lemmas  {ℓ' : Level} (B : HLevel ℓ' (2+ (suc₋₂ n))) where

    P : (f : A → fst B) → A → Type _
    P f a2 = (f a2 ≡ f a)

    hLevelP : (f : A → fst B) → (a : A) → isOfHLevel (2+ n) (P f a)
    hLevelP  f a2 = helper n (f a2) (f a) (snd B) 
      where
      helper : (n : ℕ₋₂) → (b1 b2 : (fst B)) → isOfHLevel (2+ suc₋₂ n) (fst B) → isOfHLevel (2+ n) (b1 ≡ b2)
      helper neg2 b1 b2 hlvl = (hlvl b1 b2) , λ y → isProp→isSet hlvl b1 b2 _ _
      helper (-1+ n) b1 b2 hlvl = hlvl b1 b2

    forAllP : (f : A → fst B) → (a : A) → P f a
    forAllP f = equiv-proof (conInd-i→ii (λ x → a) n iscon (λ a → P f a , hLevelP f a)) (λ a → refl) .fst .fst
      where
      helper : (n : ℕ₋₂) → (b1 b2 : (fst B)) → isOfHLevel (2+ suc₋₂ n) (fst B) → isOfHLevel (2+ n) (b1 ≡ b2)
      helper neg2 b1 b2 hlvl = (hlvl b1 b2) , λ y → isProp→isSet hlvl b1 b2 _ _
      helper (-1+ n) b1 b2 hlvl = hlvl b1 b2

    sect : section  (λ (b : fst B) (a : A) → b) λ f → f a
    sect f = funExt λ y → sym ((forAllP f) y)

    isEquivMap : isEquiv (λ (b : fst B) (a : A) → b)
    isEquivMap = isoToIsEquiv (iso (λ b a → b)
                              (λ f → f a)
                              sect
                              λ h → refl)
