
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.FinData.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData.Base as Fin
import Cubical.Data.Nat as ℕ
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
