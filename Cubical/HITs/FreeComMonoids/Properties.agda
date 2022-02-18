{-# OPTIONS --safe #-}

module Cubical.HITs.FreeComMonoids.Properties where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
open import Cubical.Foundations.Everything hiding (assoc; ⟨_⟩)

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.FinData

open import Cubical.HITs.FreeComMonoids.Base as FCM
open import Cubical.HITs.AssocList as AL
open import Cubical.HITs.FreeComMonoids.AssocListFunctions

private variable
  ℓ : Level
  n nn : ℕ

PolyFin = AssocList ∘ Fin
FreeComMonoidFin = FreeComMonoid ∘ Fin

_^_ : Fin n → ℕ → FreeComMonoidFin n
fn ^ zero = ε
fn ^ suc n = ⟦ fn ⟧ · (fn ^ n)

^+≡ : ∀ (p : Fin nn) m n → ((p ^ m) · (p ^ n)) ≡ (p ^ (m + n))
^+≡ p zero n = identityᵣ _
^+≡ p (suc m) n = sym (assoc _ _ _) ∙ cong (_ ·_) (^+≡ _ _ _)

to : PolyFin n → FreeComMonoidFin n
to = AL.Rec.f trunc ε (λ fn n → (fn ^ n) ·_)
  per* agg* (const identityᵣ)
  where
  per* : ∀ x y (mon : FreeComMonoidFin n) →
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

  agg* : ∀ fn m n mon →
      ((fn ^ m) · ((fn ^ n) · mon)) ≡ ((fn ^ (m + n)) · mon)
  agg* fn m n mon =
    ((fn ^ m) · ((fn ^ n) · mon))
    ≡⟨ assoc _ _ _ ⟩
    (((fn ^ m) · (fn ^ n)) · mon)
    ≡⟨ cong (_· _) (^+≡ _ _ _) ⟩
    ((fn ^ (m + n)) · mon) ∎

from : FreeComMonoidFin n → PolyFin n
from = FCM.Rec.f trunc ⟨_⟩ ⟨⟩ _++_ comm-++ unitr-++ (λ _ → refl) assoc-++

^-id : (x : Fin n) (m : ℕ) (u : FreeComMonoidFin n)
  → from ((x ^ m) · u) ≡ ⟨ x , m ⟩∷ from u
^-id x zero u = cong from (identityᵣ u) ∙ sym (del _ _)
^-id x (suc m) u =
  from ((⟦ x ⟧ · (x ^ m)) · u)
  ≡⟨ cong ⟨ x , 1 ⟩∷_ (^-id x m u) ⟩
  ⟨ x , 1 ⟩∷ ⟨ x , m ⟩∷ from u
  ≡⟨ agg _ _ _ _ ⟩
  ⟨ x , suc m ⟩∷ from u ∎

++-· : (x y : PolyFin n)
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

to∘from : section {A = PolyFin n} to from
to∘from = FCM.ElimProp.f (trunc _ _) (λ x → identityₗ _ ∙ identityₗ _) refl
  λ {x y} p q → ++-· (from x) (from y) ∙ cong₂ _·_ p q

from∘to : retract {A = PolyFin n} to from
from∘to = AL.ElimProp.f (trunc _ _) refl
  λ x n {xs} p → ^-id x n (to xs) ∙ cong (⟨ _ , _ ⟩∷_) p

FCMon≃AssocList : PolyFin n ≃ FreeComMonoidFin n
FCMon≃AssocList = isoToEquiv (iso to from to∘from from∘to)

AssocList≃FCMon : FreeComMonoidFin n ≃ PolyFin n
AssocList≃FCMon = isoToEquiv (iso from to from∘to to∘from)

FCMon≡AssocList : PolyFin n ≡ FreeComMonoidFin n
FCMon≡AssocList = ua FCMon≃AssocList
