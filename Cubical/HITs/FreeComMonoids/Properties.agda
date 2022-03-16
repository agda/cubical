{-# OPTIONS --safe #-}

module Cubical.HITs.FreeComMonoids.Properties where

open import Cubical.Foundations.Everything hiding (assoc; ⟨_⟩)

open import Cubical.Data.Nat hiding (_·_ ; _^_)

open import Cubical.HITs.FreeComMonoids.Base as FCM
open import Cubical.HITs.AssocList as AL

private variable
  ℓ : Level
  A : Type ℓ

multi-· : A → ℕ → FreeComMonoid A → FreeComMonoid A
multi-· x zero xs = xs
multi-· x (suc n) xs = ⟦ x ⟧ · multi-· x n xs

_^_ : A → ℕ → FreeComMonoid A
x ^ n = multi-· x n ε

^+≡ : ∀ (p : A) m n → ((p ^ m) · (p ^ n)) ≡ (p ^ (m + n))
^+≡ p zero n = identityₗ _
^+≡ p (suc m) n = sym (assoc _ _ _) ∙ cong (_ ·_) (^+≡ _ _ _)

AL→FCM : AssocList A → FreeComMonoid A
AL→FCM = AL.Rec.f trunc ε (λ a n p → (a ^ n) · p)
  per* agg* (const identityₗ)
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

FCM→AL : FreeComMonoid A → AssocList A
FCM→AL = FCM.Rec.f trunc ⟨_⟩ ⟨⟩ _++_ comm-++ unitr-++ (λ _ → refl) assoc-++

^-id : (x : A) (m : ℕ) (u : FreeComMonoid A)
  → FCM→AL ((x ^ m) · u) ≡ ⟨ x , m ⟩∷ FCM→AL u
^-id x zero u = cong FCM→AL (identityₗ u) ∙ sym (del _ _)
^-id x (suc m) u =
  FCM→AL ((⟦ x ⟧ · (x ^ m)) · u)
  ≡⟨ cong ⟨ x , 1 ⟩∷_ (^-id x m u) ⟩
  ⟨ x , 1 ⟩∷ ⟨ x , m ⟩∷ FCM→AL u
  ≡⟨ agg _ _ _ _ ⟩
  ⟨ x , suc m ⟩∷ FCM→AL u ∎

++-· : (x y : AssocList A)
  → AL→FCM (x ++ y) ≡ AL→FCM x · AL→FCM y
++-· = AL.ElimProp.f
  (isPropΠ (λ _ → trunc _ _))
  (λ _ → sym (identityₗ _))
  λ x n {xs} p ys →
  AL→FCM (((⟨ x , n ⟩∷ ⟨⟩) ++ xs) ++ ys)
  ≡⟨ cong AL→FCM (cong (_++ ys) (comm-++ (⟨ x , n ⟩∷ ⟨⟩) xs) ∙ sym (assoc-++ xs _ ys)) ⟩
  AL→FCM (xs ++ (⟨ x , n ⟩∷ ys))
  ≡⟨ p _ ⟩
  (AL→FCM xs · ((x ^ n) · AL→FCM ys))
  ≡⟨ assoc (AL→FCM xs) _ _ ⟩
  ((AL→FCM xs · (x ^ n)) · AL→FCM ys)
  ≡⟨ cong (_· AL→FCM ys) (comm _ _) ⟩
  ((x ^ n) · AL→FCM xs) · AL→FCM ys ∎

AL→FCM∘FCM→AL≡id : section {A = AssocList A} AL→FCM FCM→AL
AL→FCM∘FCM→AL≡id = FCM.ElimProp.f (trunc _ _) (λ x → identityᵣ _ ∙ identityᵣ _) refl
  λ {x y} p q → ++-· (FCM→AL x) (FCM→AL y) ∙ cong₂ _·_ p q

FCM→AL∘AL→FCM≡id : retract {A = AssocList A} AL→FCM FCM→AL
FCM→AL∘AL→FCM≡id = AL.ElimProp.f (trunc _ _) refl
  λ x n {xs} p → ^-id x n (AL→FCM xs) ∙ cong (⟨ _ , _ ⟩∷_) p

AssocList≃FreeComMonoid : AssocList A ≃ FreeComMonoid A
AssocList≃FreeComMonoid = isoToEquiv (iso AL→FCM FCM→AL AL→FCM∘FCM→AL≡id FCM→AL∘AL→FCM≡id)

AssocList≡FreeComMonoid : AssocList A ≡ FreeComMonoid A
AssocList≡FreeComMonoid = ua AssocList≃FreeComMonoid
