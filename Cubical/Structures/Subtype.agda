{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Subtype where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

-- The type of Subtypes of a type
Subtype : {ℓ : Level} → (ℓ' : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Subtype ℓ' A = A → (hProp ℓ')

-- Coercion from Subtype to Type
Subtype→Type : {ℓ ℓ' : Level} {A : Type ℓ} (B : Subtype ℓ' A) → Type (ℓ-max ℓ ℓ')
Subtype→Type {A = A} B = Σ[ a ∈ A ] (fst (B a))

-- if A has Level n > 0 then so do all of its subtypes -}
subtypePreservesHLevel : {ℓ ℓ' : Level} {A : Type ℓ} {n : ℕ₊₁} (p : isOfHLevel (ℕ₊₁→ℕ n) A) (B : Subtype ℓ' A) → isOfHLevel (ℕ₊₁→ℕ n) (Subtype→Type B)
subtypePreservesHLevel {n = one} p B = isPropΣ p λ a → snd (B a)
subtypePreservesHLevel {n = 1+ (suc n)} p B = isOfHLevelΣ (suc (suc n)) p λ a → isProp→isOfHLevelSuc (suc n) (snd (B a))

-- if two terms x and y of the original type A are equal by q, and p and p' witness that x , y are in
-- the subtype then p ≡ p' over q
subtypeWitnessIrrelevance : {A : Type ℓ} (B : Subtype ℓ' A) {xp yp : Subtype→Type B} (q : fst xp ≡ fst yp) → xp ≡ yp
subtypeWitnessIrrelevance B {xp} {yp} q = ΣPathP (q , isProp→PathP (λ i → snd (B (q i))) (snd xp) (snd yp))
