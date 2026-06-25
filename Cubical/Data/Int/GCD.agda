module Cubical.Data.Int.GCD where

open import Cubical.Data.Empty as ⊥
import Cubical.Data.Nat.GCD as ℕ
open import Cubical.Data.Nat.Divisibility renaming (_∣_ to _∣ℕ_)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.Int

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

gcd : ℤ → ℤ → ℤ
gcd i j = pos (ℕ.gcd  (abs i) (abs j))

gcd-def : ∀ i j → gcd i j ≡ pos (ℕ.gcd (abs i) (abs j))
gcd-def i j = refl

gcdSym : ∀ i j → gcd i j ≡ gcd j i
gcdSym i j = cong pos (ℕ.gcdSym (abs i) (abs j))

------------------------------------------------------------------------
-- ℕ and ℤ conversions
------------------------------------------------------------------------

gcd∣ℕ→∣ℤ-lemma : ∀ {i j k : ℤ} → ℕ.gcd (abs i) (abs j) ∣ℕ (abs k) → gcd i j ∣ k
gcd∣ℕ→∣ℤ-lemma {i}{j}{k} gcdij|k = ∣ℕ→∣ gcdij|k

ℕ∣gcd→ℤ∣-lemma : ∀ {i j k : ℤ} →  (abs k) ∣ℕ ℕ.gcd (abs i) (abs j) → k ∣ gcd i j
ℕ∣gcd→ℤ∣-lemma {i}{j}{k} k|gcdij = ∣ℕ→∣ k|gcdij

gcd∣ℤ→∣ℕ-lemma : ∀ {i j k : ℤ} → gcd i j ∣ k → ℕ.gcd (abs i) (abs j) ∣ℕ (abs k)
gcd∣ℤ→∣ℕ-lemma {i}{j}{k} gcdij|k = ∣→∣ℕ gcdij|k

ℤ∣gcd→ℕ∣-lemma : ∀ {i j k : ℤ} → k ∣ gcd i j → (abs k) ∣ℕ ℕ.gcd (abs i) (abs j)
ℤ∣gcd→ℕ∣-lemma {i}{j}{k} k|gcdij = ∣→∣ℕ k|gcdij

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

gcd[i,j]∣i : ∀ i j → gcd i j ∣ i
gcd[i,j]∣i i j = gcd∣ℕ→∣ℤ-lemma {i}{j} (ℕ.gcd[m,n]∣m (abs i) (abs j))

gcd[i,j]∣j : ∀ i j → gcd i j ∣ j
gcd[i,j]∣j i j = gcd∣ℕ→∣ℤ-lemma {i}{j} (ℕ.gcd[m,n]∣n (abs i) (abs j))

gcd-greatest : ∀ {i j c} → c ∣ i → c ∣ j → c ∣ gcd i j
gcd-greatest {i}{j}{c} ci cj =
  ℕ∣gcd→ℤ∣-lemma {i}{j}{c} (ℕ.gcd-greatest (∣→∣ℕ ci) (∣→∣ℕ cj))

gcd[0,0]≡0 : gcd 0 0 ≡ 0
gcd[0,0]≡0  = cong pos ℕ.gcd[0,0]≡0

gcd[i,j]≡0⇒i≡0 : ∀ {i j} → gcd i j ≡ 0 → i ≡ 0
gcd[i,j]≡0⇒i≡0 {i} {j} eqn = abs≡0 i (ℕ.gcd[m,n]≡0⇒m≡0 {abs i}{abs j} (injPos eqn))

gcd[i,j]≡0⇒j≡0 : ∀ {i j} → gcd i j ≡ 0 → j ≡ 0
gcd[i,j]≡0⇒j≡0 {i}{j} eqn = gcd[i,j]≡0⇒i≡0 {j}{i} (gcdSym j i ∙ eqn)
