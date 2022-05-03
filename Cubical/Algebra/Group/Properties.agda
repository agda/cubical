{-

This file contains basic theory about groups

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.Base

private
  variable
    ℓ : Level
    G : Type ℓ

isPropIsGroup : (0g : G) (_+_ : G → G → G) (-_ : G → G)
              → isProp (IsGroup 0g _+_ -_)
IsGroup.isMonoid (isPropIsGroup 0g _+_ -_ g1 g2 i) =
  isPropIsMonoid _ _ (IsGroup.isMonoid g1) (IsGroup.isMonoid g2) i
IsGroup.inverse (isPropIsGroup 0g _+_ -_ g1 g2 i) =
  isPropInv (IsGroup.inverse g1) (IsGroup.inverse g2) i
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid g1))

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)


module GroupTheory (G : Group ℓ) where
  open GroupStr (snd G)
  abstract
    ·CancelL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a · b ≡ a · c → b ≡ c
    ·CancelL a {b} {c} p =
       b               ≡⟨ sym (lid b) ∙ cong (_· b) (sym (invl a)) ∙ sym (assoc _ _ _) ⟩
      inv a · (a · b)  ≡⟨ cong (inv a ·_) p ⟩
      inv a · (a · c)  ≡⟨ assoc _ _ _ ∙ cong (_· c) (invl a) ∙ lid c ⟩
      c ∎

    ·CancelR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a · c ≡ b · c → a ≡ b
    ·CancelR {a} {b} c p =
      a                ≡⟨ sym (rid a) ∙ cong (a ·_) (sym (invr c)) ∙ assoc _ _ _ ⟩
      (a · c) · inv c  ≡⟨ cong (_· inv c) p ⟩
      (b · c) · inv c  ≡⟨ sym (assoc _ _ _) ∙ cong (b ·_) (invr c) ∙ rid b ⟩
      b ∎

    invInv : (a : ⟨ G ⟩) → inv (inv a) ≡ a
    invInv a = ·CancelL (inv a) (invr (inv a) ∙ sym (invl a))

    inv1g : inv 1g ≡ 1g
    inv1g = ·CancelL 1g (invr 1g ∙ sym (lid 1g))

    1gUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e · x ≡ x → e ≡ 1g
    1gUniqueL {e} x p = ·CancelR x (p ∙ sym (lid _))

    1gUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x · e ≡ x → e ≡ 1g
    1gUniqueR x {e} p = ·CancelL x (p ∙ sym (rid _))

    invUniqueL : {g h : ⟨ G ⟩} → g · h ≡ 1g → g ≡ inv h
    invUniqueL {g} {h} p = ·CancelR h (p ∙ sym (invl h))

    invUniqueR : {g h : ⟨ G ⟩} → g · h ≡ 1g → h ≡ inv g
    invUniqueR {g} {h} p = ·CancelL g (p ∙ sym (invr g))

    invDistr : (a b : ⟨ G ⟩) → inv (a · b) ≡ inv b · inv a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a · b) · (inv b · inv a) ≡ 1g
      γ = (a · b) · (inv b · inv a)
            ≡⟨ sym (assoc _ _ _) ⟩
          a · b · (inv b) · (inv a)
            ≡⟨ cong (a ·_) (assoc _ _ _ ∙ cong (_· (inv a)) (invr b)) ⟩
          a · (1g · inv a)
            ≡⟨ cong (a ·_) (lid (inv a)) ∙ invr a ⟩
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
