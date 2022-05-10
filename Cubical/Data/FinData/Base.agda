{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; +-assoc)
open import Cubical.Data.Bool.Base
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A B : Type ℓ

data Fin : ℕ → Type₀ where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- useful patterns
pattern one = suc zero
pattern two = suc one

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

toFromId : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n
toFromId zero = refl
toFromId (suc n) = cong suc (toFromId n)

¬Fin0 : ¬ Fin 0
¬Fin0 ()

_==_ : ∀ {n} → Fin n → Fin n → Bool
zero == zero   = true
zero == suc _  = false
suc _ == zero  = false
suc m == suc n = m == n

weakenFin : {n : ℕ} → Fin n → Fin (suc n)
weakenFin zero = zero
weakenFin (suc i) = suc (weakenFin i)

predFin : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
predFin zero = zero
predFin (suc x) = x

foldrFin : ∀ {n} → (A → B → B) → B → (Fin n → A) → B
foldrFin {n = zero}  _ b _ = b
foldrFin {n = suc n} f b l = f (l zero) (foldrFin f b (l ∘ suc))

elim
  : ∀(P : ∀{k} → Fin k → Type ℓ)
  → (∀{k} → P {suc k} zero)
  → (∀{k} → {fn : Fin k} → P fn → P (suc fn))
  → {k : ℕ} → (fn : Fin k) → P fn

elim P fz fs {zero} = ⊥.rec ∘ ¬Fin0
elim P fz fs {suc k} zero = fz
elim P fz fs {suc k} (suc fj) = fs (elim P fz fs fj)


rec : ∀{k} → (a0 aS : A) → Fin k → A
rec a0 aS zero = a0
rec a0 aS (suc x) = aS


FinVec : (A : Type ℓ) (n : ℕ) → Type ℓ
FinVec A n = Fin n → A

replicateFinVec : (n : ℕ) → A → FinVec A n
replicateFinVec _ a _ = a


_++Fin_ : {n m : ℕ} → FinVec A n → FinVec A m → FinVec A (n + m)
_++Fin_ {n = zero} _ W i = W i
_++Fin_ {n = suc n} V _ zero = V zero
_++Fin_ {n = suc n} V W (suc i) = ((V ∘ suc) ++Fin W) i
