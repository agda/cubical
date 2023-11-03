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
       b               ≡⟨ sym (·IdL b) ∙ congL _·_ (sym (·InvL a)) ∙ sym (·Assoc _ _ _) ⟩
      inv a · (a · b)  ≡⟨ congR _·_ p ⟩
      inv a · (a · c)  ≡⟨ ·Assoc _ _ _ ∙ congL _·_ (·InvL a) ∙ ·IdL c ⟩
      c ∎

    ·CancelR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a · c ≡ b · c → a ≡ b
    ·CancelR {a} {b} c p =
      a                ≡⟨ sym (·IdR a) ∙ congR _·_ (sym (·InvR c)) ∙ ·Assoc _ _ _ ⟩
      (a · c) · inv c  ≡⟨ congL _·_ p ⟩
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

    idFromIdempotency : (x : ⟨ G ⟩) → x ≡ x · x → x ≡ 1g
    idFromIdempotency x p =
      x                 ≡⟨ sym (·IdR x) ⟩
      x · 1g            ≡⟨ congR _·_ (sym (·InvR _)) ⟩
      x · (x · inv x)   ≡⟨ ·Assoc _ _ _ ⟩
      (x · x) · (inv x) ≡⟨ congL _·_ (sym p) ⟩
      x · (inv x)       ≡⟨ ·InvR _ ⟩
      1g              ∎

    invDistr : (a b : ⟨ G ⟩) → inv (a · b) ≡ inv b · inv a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a · b) · (inv b · inv a) ≡ 1g
      γ = (a · b) · (inv b · inv a) ≡⟨ sym (·Assoc _ _ _) ⟩
          a · b · (inv b) · (inv a) ≡⟨ congR _·_ (·Assoc _ _ _ ∙ congL _·_ (·InvR b)) ⟩
          a · (1g · inv a)          ≡⟨ congR _·_ (·IdL (inv a)) ∙ ·InvR a ⟩
          1g ∎

congIdLeft≡congIdRight : (_·G_ : G → G → G) (-G_ : G → G)
            (0G : G)
            (rUnitG : (x : G) → x ·G 0G ≡ x)
            (lUnitG : (x : G) → 0G ·G x ≡ x)
          → (r≡l : rUnitG 0G ≡ lUnitG 0G)
          → (p : 0G ≡ 0G) →
            congR _·G_ p ≡ congL _·G_ p
congIdLeft≡congIdRight _·G_ -G_ 0G rUnitG lUnitG r≡l p =
            rUnit (congR _·G_ p)
         ∙∙ ((λ i → (λ j → lUnitG 0G (i ∧ j)) ∙∙ cong (λ x → lUnitG x i) p ∙∙ λ j → lUnitG 0G (i ∧ ~ j))
         ∙∙ cong₂ (λ x y → x ∙∙ p ∙∙ y) (sym r≡l) (cong sym (sym r≡l))
         ∙∙ λ i → (λ j → rUnitG 0G (~ i ∧ j)) ∙∙ cong (λ x → rUnitG x (~ i)) p ∙∙ λ j → rUnitG 0G (~ i ∧ ~ j))
         ∙∙ sym (rUnit (congL _·G_ p))
