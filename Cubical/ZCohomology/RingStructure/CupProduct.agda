{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CupProduct where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (_+'_ ; +'≡+ ; _+_)

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties

infixl 30 _·₀_
infixr 35 _⌣ₖ_
infixr 35 _⌣_

--- This definition of ℕ-addition removes some unnecessary transports.
open PlusBis

-- Cup product with one integer (K₀) argument
_·₀_ : {n : ℕ} (m : ℤ) → coHomK n → coHomK n
_·₀_ {n = n} (pos zero) x = 0ₖ _
_·₀_ {n = n} (pos (suc m)) x = x +ₖ (pos m ·₀ x)
_·₀_ {n = n} (negsuc zero) x = -ₖ x
_·₀_ {n = n} (negsuc (suc m)) x = (negsuc m ·₀ x) -ₖ x

·₀-0ₖ : {n : ℕ} (m : ℤ) → _·₀_ m (0ₖ n) ≡ 0ₖ n
·₀-0ₖ (pos zero) = refl
·₀-0ₖ (pos (suc n)) = cong (0ₖ _ +ₖ_) (·₀-0ₖ (pos n)) ∙ rUnitₖ _ (0ₖ _)
·₀-0ₖ (negsuc zero) = -0ₖ
·₀-0ₖ (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (·₀-0ₖ (negsuc n)) ∙ rCancelₖ _ (0ₖ _)

-- Pointed version first (enables truncation elimination)
⌣ₖ∙ : (n m : ℕ) → coHomK n → coHomK-ptd m →∙ coHomK-ptd (n +' m)
fst (⌣ₖ∙ zero m a) b = a ·₀ b
snd (⌣ₖ∙ zero m a) = ·₀-0ₖ a
fst (⌣ₖ∙ (suc n) zero a) b = b ·₀ a
snd (⌣ₖ∙ (suc n) zero a) = refl
⌣ₖ∙ (suc n) (suc m) = T.rec (isOfHLevel↑∙ (suc n) m) (cup n m)
  where
  cup : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
  fst (cup zero m base) _ = 0ₖ _
  fst (cup zero m (loop i)) x = Kn→ΩKn+1 _ x i
  fst (cup (suc n) m north) _ = 0ₖ _
  fst (cup (suc n) m south) _ = 0ₖ _
  fst (cup (suc n) m (merid a i)) x = Kn→ΩKn+1 _ (fst (cup n m a) x) i
  snd (cup zero m base) = refl
  snd (cup zero m (loop i)) k = Kn→ΩKn+10ₖ _ k i
  snd (cup (suc n) m north) = refl
  snd (cup (suc n) m south) = refl
  snd (cup (suc n) m (merid a i)) k = (cong (Kn→ΩKn+1 _) (snd (cup n m a)) ∙ Kn→ΩKn+10ₖ _) k i

-- Non pointed version
_⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n +' m)
_⌣ₖ_ {n = n} {m = m} x y = fst (⌣ₖ∙ n m x) y

-- Doubly pointed version
⌣ₖ∙∙ : (n m : ℕ) → coHomK-ptd n →∙ (coHomK-ptd m →∙ coHomK-ptd (n +' m) ∙)
fst (⌣ₖ∙∙ n m) = ⌣ₖ∙ n m
fst (snd (⌣ₖ∙∙ zero zero) i) x = 0
fst (snd (⌣ₖ∙∙ zero (suc m)) i) x = 0ₖ _
fst (snd (⌣ₖ∙∙ (suc n) zero) i) x = ·₀-0ₖ x i
fst (snd (⌣ₖ∙∙ (suc zero) (suc m)) i) x = 0ₖ _
fst (snd (⌣ₖ∙∙ (suc (suc n)) (suc m)) i) x = 0ₖ _
snd (snd (⌣ₖ∙∙ zero zero) i) = refl
snd (snd (⌣ₖ∙∙ zero (suc m)) i) = refl
snd (snd (⌣ₖ∙∙ (suc n) zero) i) = refl
snd (snd (⌣ₖ∙∙ (suc zero) (suc m)) i) = refl
snd (snd (⌣ₖ∙∙ (suc (suc n)) (suc m)) i) = refl

-- Cup product
_⌣_ : ∀ {ℓ} {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n +' m) A
_⌣_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂
