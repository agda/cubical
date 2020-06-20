{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.SumFin.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (tt) renaming (Unit to ⊤) public
open import Cubical.Data.Sum using (_⊎_; inl; inr) public

open import Cubical.Data.Nat hiding (elim)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    ℓ : Level
    k : ℕ

Fin : ℕ → Type₀
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ (Fin n)

pattern fzero = inl tt
pattern fsuc n = inr n

elim
  : (P : ∀ {k} → Fin k → Type ℓ)
  → (∀ {k} → P {suc k} fzero)
  → (∀ {k} {fn : Fin k} → P fn → P (fsuc fn))
  → {k : ℕ} (fn : Fin k) → P fn
elim P fz fs {zero}  f0        = ⊥.rec f0
elim P fz fs {suc k} fzero     = fz
elim P fz fs {suc k} (fsuc fk) = fs (elim P fz fs fk)

finj : Fin k → Fin (suc k)
finj {suc k} fzero    = fzero
finj {suc k} (fsuc n) = fsuc (finj {k} n)

toℕ : Fin k → ℕ
toℕ {suc k} (inl tt) = zero
toℕ {suc k} (inr x)  = suc (toℕ {k} x)

toℕ-injective : {m n : Fin k} → toℕ m ≡ toℕ n → m ≡ n
toℕ-injective {suc k} {fzero}  {fzero}  _ = refl
toℕ-injective {suc k} {fzero}  {fsuc x} p = ⊥.rec (znots p)
toℕ-injective {suc k} {fsuc m} {fzero}  p = ⊥.rec (snotz p)
toℕ-injective {suc k} {fsuc m} {fsuc x} p = cong fsuc (toℕ-injective (injSuc p))

-- Thus, Fin k is discrete
discreteFin : Discrete (Fin k)
discreteFin fj fk with discreteℕ (toℕ fj) (toℕ fk)
... | yes p = yes (toℕ-injective p)
... | no ¬p = no (λ p → ¬p (cong toℕ p))

isSetFin : isSet (Fin k)
isSetFin = Discrete→isSet discreteFin
