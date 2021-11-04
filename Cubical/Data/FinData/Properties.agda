
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData.Base as Fin
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary

private
 variable
   ℓ : Level
   A : Type ℓ


znots : ∀{k} {m : Fin k} → ¬ (zero ≡ (suc m))
znots {k} {m} x = subst (Fin.rec (Fin k) ⊥) x m

snotz : ∀{k} {m : Fin k} → ¬ ((suc m) ≡ zero)
snotz {k} {m} x = subst (Fin.rec ⊥ (Fin k)) x m

isPropFin0 : isProp (Fin 0)
isPropFin0 = Empty.rec ∘ ¬Fin0

isContrFin1 : isContr (Fin 1)
isContrFin1 .fst = zero
isContrFin1 .snd zero = refl

injSucFin : ∀ {n} { p q : Fin n} → suc p ≡ suc q → p ≡ q
injSucFin {ℕ.suc ℕ.zero} {zero} {zero} pf = refl
injSucFin {ℕ.suc (ℕ.suc n)} pf = cong predFin pf


discreteFin : ∀{k} → Discrete (Fin k)
discreteFin zero zero = yes refl
discreteFin zero (suc y) = no znots
discreteFin (suc x) zero = no snotz
discreteFin (suc x) (suc y) with discreteFin x y
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (injSucFin q))

isSetFin : ∀{k} → isSet (Fin k)
isSetFin = Discrete→isSet discreteFin


weakenRespToℕ : ∀ {n} (i : Fin n) → toℕ (weakenFin i) ≡ toℕ i
weakenRespToℕ zero = refl
weakenRespToℕ (suc i) = cong ℕ.suc (weakenRespToℕ i)

toℕ<n : ∀ {n} (i : Fin n) → toℕ i < n
toℕ<n {n = ℕ.suc n} zero = n , ℕ.+-comm n 1
toℕ<n {n = ℕ.suc n} (suc i) = toℕ<n i .fst , ℕ.+-suc _ _ ∙ cong ℕ.suc (toℕ<n i .snd)
