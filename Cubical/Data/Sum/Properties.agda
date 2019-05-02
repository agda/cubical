{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Nat

open import Cubical.Data.Sum.Base

-- Path space of sum type
module SumPath {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  Cover : A ⊎ B → A ⊎ B → Type (ℓ-max ℓ ℓ')
  Cover (inl a) (inl a') = Lift {j = ℓ-max ℓ ℓ'} (a ≡ a')
  Cover (inl _) (inr _) = Lift ⊥
  Cover (inr _) (inl _) = Lift ⊥
  Cover (inr b) (inr b') = Lift {j = ℓ-max ℓ ℓ'} (b ≡ b')

  reflCode : (c : A ⊎ B) → Cover c c
  reflCode (inl a) = lift refl
  reflCode (inr b) = lift refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode (inl a) (inl a') (lift p) = cong inl p
  decode (inl a) (inr b') ()
  decode (inr b) (inl a') ()
  decode (inr b) (inr b') (lift q) = cong inr q

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl (inl a) = refl
  decodeRefl (inr b) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  isOfHLevelCover : (n : ℕ)
    → isOfHLevel (suc (suc n)) A
    → isOfHLevel (suc (suc n)) B
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p q (inl a) (inl a') = isOfHLevelLift (suc n) (p a a')
  isOfHLevelCover n p q (inl a) (inr b') =
    isOfHLevelLift (suc n)
    (subst (λ m → isOfHLevel m ⊥) (+-comm n 1)
      (hLevelLift n isProp⊥))
  isOfHLevelCover n p q (inr b) (inl a') =
    isOfHLevelLift (suc n)
      (subst (λ m → isOfHLevel m ⊥) (+-comm n 1)
        (hLevelLift n isProp⊥))
  isOfHLevelCover n p q (inr b) (inr b') = isOfHLevelLift (suc n) (q b b')

isOfHLevelSum : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) B
  → isOfHLevel (suc (suc n)) (A ⊎ B)
isOfHLevelSum n lA lB c c' =
  retractIsOfHLevel (suc n)
    (SumPath.encode c c')
    (SumPath.decode c c')
    (SumPath.decodeEncode c c')
    (SumPath.isOfHLevelCover n lA lB c c')
