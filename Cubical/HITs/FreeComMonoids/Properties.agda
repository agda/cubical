{-# OPTIONS --safe #-}

module Cubical.HITs.FreeComMonoids.Properties where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
open import Cubical.Foundations.Everything hiding (assoc; ⟨_⟩)

open import Cubical.Data.Nat hiding (_·_)

open import Cubical.HITs.FreeComMonoids.Base as FCM
open import Cubical.HITs.AssocList as AL
open import Cubical.HITs.FreeComMonoids.AssocListFunctions

private variable
  ℓ : Level
  A : Type ℓ

_^_ : A → ℕ → FreeComMonoid A
a ^ zero = ε
a ^ suc n = ⟦ a ⟧ · (a ^ n)

^+≡ : ∀ (p : A) m n → ((p ^ m) · (p ^ n)) ≡ (p ^ (m + n))
^+≡ p zero n = identityᵣ _
^+≡ p (suc m) n = sym (assoc _ _ _) ∙ cong (_ ·_) (^+≡ _ _ _)

to : AssocList A → FreeComMonoid A
to = AL.Rec.f trunc ε (λ a n → (a ^ n) ·_)
  per* agg* (const identityᵣ)
  where
  per* : ∀ x y (mon : FreeComMonoid A) →
    ((⟦ x ⟧ · ε) · ((⟦ y ⟧ · ε) · mon)) ≡
    ((⟦ y ⟧ · ε) · ((⟦ x ⟧ · ε) · mon))
  per* x y mon =
    (⟦ x ⟧ · ε) · ((⟦ y ⟧ · ε) · mon)
    ≡⟨ assoc _ _ _ ⟩
    ((⟦ x ⟧ · ε) · (⟦ y ⟧ · ε)) · mon
    ≡⟨ cong (_· mon) (comm _ _) ⟩
    (((⟦ y ⟧ · ε) · (⟦ x ⟧ · ε)) · mon)
    ≡⟨ sym (assoc _ _ _) ⟩
    ((⟦ y ⟧ · ε) · ((⟦ x ⟧ · ε) · mon)) ∎

  agg* : ∀ a m n mon →
      ((a ^ m) · ((a ^ n) · mon)) ≡ ((a ^ (m + n)) · mon)
  agg* a m n mon =
    ((a ^ m) · ((a ^ n) · mon))
    ≡⟨ assoc _ _ _ ⟩
    (((a ^ m) · (a ^ n)) · mon)
    ≡⟨ cong (_· _) (^+≡ _ _ _) ⟩
    ((a ^ (m + n)) · mon) ∎

from : FreeComMonoid A → AssocList A
from = FCM.Rec.f trunc ⟨_⟩ ⟨⟩ _++_ comm-++ unitr-++ (λ _ → refl) assoc-++

^-id : (x : A) (m : ℕ) (u : FreeComMonoid A)
  → from ((x ^ m) · u) ≡ ⟨ x , m ⟩∷ from u
^-id x zero u = cong from (identityᵣ u) ∙ sym (del _ _)
^-id x (suc m) u =
  from ((⟦ x ⟧ · (x ^ m)) · u)
  ≡⟨ cong ⟨ x , 1 ⟩∷_ (^-id x m u) ⟩
  ⟨ x , 1 ⟩∷ ⟨ x , m ⟩∷ from u
  ≡⟨ agg _ _ _ _ ⟩
  ⟨ x , suc m ⟩∷ from u ∎

++-· : (x y : AssocList A)
  → to (x ++ y) ≡ to x · to y
++-· = AL.ElimProp.f
  (isPropΠ (λ _ → trunc _ _))
  (λ _ → sym (identityᵣ _))
  λ x n {xs} p ys →
  to (((⟨ x , n ⟩∷ ⟨⟩) ++ xs) ++ ys)
  ≡⟨ cong to (cong (_++ ys) (comm-++ (⟨ x , n ⟩∷ ⟨⟩) xs) ∙ sym (assoc-++ xs _ ys)) ⟩
  to (xs ++ (⟨ x , n ⟩∷ ys))
  ≡⟨ p _ ⟩
  (to xs · ((x ^ n) · to ys))
  ≡⟨ assoc (to xs) _ _ ⟩
  ((to xs · (x ^ n)) · to ys)
  ≡⟨ cong (_· to ys) (comm _ _) ⟩
  ((x ^ n) · to xs) · to ys ∎

to∘from : section {A = AssocList A} to from
to∘from = FCM.ElimProp.f (trunc _ _) (λ x → identityₗ _ ∙ identityₗ _) refl
  λ {x y} p q → ++-· (from x) (from y) ∙ cong₂ _·_ p q

from∘to : retract {A = AssocList A} to from
from∘to = AL.ElimProp.f (trunc _ _) refl
  λ x n {xs} p → ^-id x n (to xs) ∙ cong (⟨ _ , _ ⟩∷_) p

FCMon≃AssocList : AssocList A ≃ FreeComMonoid A
FCMon≃AssocList = isoToEquiv (iso to from to∘from from∘to)

AssocList≃FCMon : FreeComMonoid A ≃ AssocList A
AssocList≃FCMon = isoToEquiv (iso from to from∘to to∘from)

FCMon≡AssocList : AssocList A ≡ FreeComMonoid A
FCMon≡AssocList = ua FCMon≃AssocList
