{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Base

open import Cubical.Algebra.Group.Base

private
  variable
    ℓ : Level
    G : Type ℓ

isPropIsGroup : (1g : G) (_·_ : G → G → G) (inv : G → G)
              → isProp (IsGroup 1g _·_ inv)
isPropIsGroup 1g _·_ inv =
  isOfHLevelRetractFromIso 1 IsGroupIsoΣ
    (isPropΣ (isPropIsMonoid 1g _·_)
             λ mono → isProp× (isPropΠ λ _ → mono .is-set _ _)
             (isPropΠ λ _ → mono .is-set _ _))
    where
    open IsMonoid

module GroupTheory (G : Group ℓ) where
  open GroupStr (snd G)
  abstract
    ·CancelL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a · b ≡ a · c → b ≡ c
    ·CancelL a {b} {c} p =
       b               ≡⟨ sym (·IdL b) ∙ cong (_· b) (sym (·InvL a)) ∙ sym (·Assoc _ _ _) ⟩
      inv a · (a · b)  ≡⟨ cong (inv a ·_) p ⟩
      inv a · (a · c)  ≡⟨ ·Assoc _ _ _ ∙ cong (_· c) (·InvL a) ∙ ·IdL c ⟩
      c ∎

    ·CancelR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a · c ≡ b · c → a ≡ b
    ·CancelR {a} {b} c p =
      a                ≡⟨ sym (·IdR a) ∙ cong (a ·_) (sym (·InvR c)) ∙ ·Assoc _ _ _ ⟩
      (a · c) · inv c  ≡⟨ cong (_· inv c) p ⟩
      (b · c) · inv c  ≡⟨ sym (·Assoc _ _ _) ∙ cong (b ·_) (·InvR c) ∙ ·IdR b ⟩
      b ∎

    invInv : (a : ⟨ G ⟩) → inv (inv a) ≡ a
    invInv a = ·CancelL (inv a) (·InvR (inv a) ∙ sym (·InvL a))

    inv1g : inv 1g ≡ 1g
    inv1g = ·CancelL 1g (·InvR 1g ∙ sym (·IdL 1g))

    1gUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e · x ≡ x → e ≡ 1g
    1gUniqueL {e} x p = ·CancelR x (p ∙ sym (·IdL _))

    1gUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x · e ≡ x → e ≡ 1g
    1gUniqueR x {e} p = ·CancelL x (p ∙ sym (·IdR _))

    invUniqueL : {g h : ⟨ G ⟩} → g · h ≡ 1g → g ≡ inv h
    invUniqueL {g} {h} p = ·CancelR h (p ∙ sym (·InvL h))

    invUniqueR : {g h : ⟨ G ⟩} → g · h ≡ 1g → h ≡ inv g
    invUniqueR {g} {h} p = ·CancelL g (p ∙ sym (·InvR g))

    invDistr : (a b : ⟨ G ⟩) → inv (a · b) ≡ inv b · inv a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a · b) · (inv b · inv a) ≡ 1g
      γ = (a · b) · (inv b · inv a)
            ≡⟨ sym (·Assoc _ _ _) ⟩
          a · b · (inv b) · (inv a)
            ≡⟨ cong (a ·_) (·Assoc _ _ _ ∙ cong (_· (inv a)) (·InvR b)) ⟩
          a · (1g · inv a)
            ≡⟨ cong (a ·_) (·IdL (inv a)) ∙ ·InvR a ⟩
          1g ∎

congIdLeft≡congIdRight : (_·G_ : G → G → G) (-G_ : G → G)
            (0G : G)
            (rUnitG : (x : G) → x ·G 0G ≡ x)
            (lUnitG : (x : G) → 0G ·G x ≡ x)
          → (r≡l : rUnitG 0G ≡ lUnitG 0G)
          → (p : 0G ≡ 0G) →
            cong (0G ·G_) p ≡ cong (_·G 0G) p
congIdLeft≡congIdRight _·G_ -G_ 0G rUnitG lUnitG r≡l p =
            rUnit (cong (0G ·G_) p)
         ∙∙ ((λ i → (λ j → lUnitG 0G (i ∧ j)) ∙∙ cong (λ x → lUnitG x i) p ∙∙ λ j → lUnitG 0G (i ∧ ~ j))
         ∙∙ cong₂ (λ x y → x ∙∙ p ∙∙ y) (sym r≡l) (cong sym (sym r≡l))
         ∙∙ λ i → (λ j → rUnitG 0G (~ i ∧ j)) ∙∙ cong (λ x → rUnitG x (~ i)) p ∙∙ λ j → rUnitG 0G (~ i ∧ ~ j))
         ∙∙ sym (rUnit (cong (_·G 0G) p))
