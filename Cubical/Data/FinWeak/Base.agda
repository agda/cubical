module Cubical.Data.FinWeak.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData as FD using (isWeaken?)

open import Cubical.Relation.Nullary

private variable
  n : ℕ

-- k : FinPure n is a proposition that means k is n - 1
data FinPure : ℕ → Type where
  zero : FinPure 1
  suc  : FinPure n → FinPure (suc n)

-- Fin n can be two cases:
-- Pure, that means n - 1
-- Weaken, that means a value that is less than n - 1
-- This Fin decreases on pattern match, different from FinData that increases
data Fin : ℕ → Type where
  pure   : FinPure n → Fin n
  weaken : Fin n     → Fin (suc n)

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
pure _   ≡ᵇ pure _   = true
pure _   ≡ᵇ weaken _ = false
weaken _ ≡ᵇ pure _   = false
weaken p ≡ᵇ weaken q = p ≡ᵇ q

predFinPure : FinPure (suc (suc n)) → FinPure (suc n)
predFinPure (suc p) = p

-- A simple example of how this data structure can be useful
-- This function can calculate the successor of Fin n in Fin n
-- In pure case, we already know that Fin n is `n - 1`. so it is already the maximum
-- In weaken case, it is less than n - 1, so it is possible to calculate the successor
sucFinOrMax : Fin n → Maybe (Fin n)
sucFinOrMax (pure _) = nothing
sucFinOrMax (weaken x) = just (sucFin x)

-- This is another way to calculate `sucFinOrMax` using regular FinData
-- This case is a little bit harder because it is necessary to use with instead of just pattern match
-- like in the case before.
sucFinDataOrMax : FD.Fin n → Maybe (FD.Fin n)
sucFinDataOrMax {suc _} p with isWeaken? p
... | no _ = nothing
... | yes (q , _) = just (FD.suc q)
