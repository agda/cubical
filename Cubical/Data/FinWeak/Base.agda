{-# OPTIONS --safe #-}
module Cubical.Data.FinWeak.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Relation.Nullary

private variable
  n : ℕ

data FinPure : ℕ → Type where
  zero : FinPure 1
  suc  : FinPure n → FinPure (suc n)

data Fin : ℕ → Type where
  pure   : FinPure n → Fin n
  weaken : Fin n     → Fin (suc n)

-- useful patterns
pattern one = suc zero
pattern two = suc one

sucFin : Fin n → Fin (suc n)
sucFin (pure p)   = pure (suc p)
sucFin (weaken p) = weaken (sucFin p)

toℕ : Fin n → ℕ
toℕ (pure zero)    = 0
toℕ (pure (suc n)) = suc (toℕ (pure n))
toℕ (weaken p)     = toℕ p

fromℕPure : (n : ℕ) → FinPure (suc n)
fromℕPure zero    = zero
fromℕPure (suc n) = suc (fromℕPure n)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = pure ∘ fromℕPure

toFromId : ∀ n → toℕ (fromℕ n) ≡ n
toFromId zero    = refl
toFromId (suc n) = cong suc (toFromId n)

¬Fin0 : ¬ Fin 0
¬Fin0 (pure ())

_≡ᵇ_ : Fin n → Fin n → Bool
pure _ ≡ᵇ pure _     = true
pure _ ≡ᵇ weaken _   = false
weaken _ ≡ᵇ pure _   = false
weaken p ≡ᵇ weaken q = p ≡ᵇ q

predFinPure : FinPure (suc (suc n)) → FinPure (suc n)
predFinPure (suc p) = p
