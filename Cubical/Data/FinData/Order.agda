module Cubical.Data.FinData.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool.Base
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary


open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Properties

private
  variable
    ℓ : Level


-- Order relation:
_≤Fin_ : {n : ℕ} → Fin n → Fin n → Type
i ≤Fin j = (toℕ i) ≤ (toℕ j)

_<Fin_ : {n : ℕ} → Fin n → Fin n → Type
i <Fin j = (suc i) ≤Fin (weakenFin j)

open BinaryRelation
≤FinIsPropValued : ∀ {n : ℕ} → isPropValued (_≤Fin_ {n})
≤FinIsPropValued _ _ = isProp≤


-- inductive version
_≤'Fin_ : {n : ℕ} → Fin n → Fin n → Type
i ≤'Fin j = (toℕ i) ≤' (toℕ j)

_<'Fin_ : {n : ℕ} → Fin n → Fin n → Type
i <'Fin j = (suc i) ≤'Fin (weakenFin j)


weakenPredFinLt : {n : ℕ} → (k l : Fin (ℕ.suc (ℕ.suc n))) → toℕ k <' toℕ l → k ≤'Fin weakenFin (predFin l)
weakenPredFinLt {ℕ.zero} zero one (s≤s z≤) = z≤
weakenPredFinLt {ℕ.zero} one one (s≤s ())
weakenPredFinLt {ℕ.zero} one (suc (suc ())) (s≤s le)
weakenPredFinLt {ℕ.suc n} zero one (s≤s z≤) = z≤
weakenPredFinLt {ℕ.suc n} zero (suc (suc l)) (s≤s le) = z≤
weakenPredFinLt {ℕ.suc n} (suc k) (suc (suc l)) (s≤s (s≤s le)) = s≤s ( weakenPredFinLt {n} k (suc l) (s≤s le))

weakenweakenFinLe : {n : ℕ} → (i : Fin (ℕ.suc n)) → (j : Fin (ℕ.suc n)) → toℕ i ≤' toℕ j → weakenFin i ≤'Fin weakenFin j
weakenweakenFinLe {ℕ.zero} zero zero le = le
weakenweakenFinLe {ℕ.suc n} zero zero le = le
weakenweakenFinLe {ℕ.suc n} zero (suc j) le = z≤
weakenweakenFinLe {ℕ.suc n} (suc i) (suc j) (s≤s le) = s≤s (weakenweakenFinLe {n} i j le)

weakenFinLe : {n : ℕ} → (i : Fin (ℕ.suc (ℕ.suc n))) → (j : Fin (ℕ.suc n)) → toℕ i ≤' toℕ j → i ≤'Fin weakenFin j
weakenFinLe {ℕ.zero} zero zero le = le
weakenFinLe {ℕ.zero} one zero ()
weakenFinLe {ℕ.zero} one (suc ()) le
weakenFinLe {ℕ.suc n} zero j le = z≤
weakenFinLe {ℕ.suc n} (suc i) (suc j) (s≤s le) = s≤s (weakenFinLe {n} i j le)

strengthenFin : {n : ℕ} {j : Fin (ℕ.suc n)} → (i : Fin (ℕ.suc n)) → toℕ i <' toℕ j → Fin n
strengthenFin {ℕ.zero} {zero} i ()
strengthenFin {ℕ.zero} {suc ()} i le
strengthenFin {ℕ.suc n} {suc j} zero le = zero
strengthenFin {ℕ.suc n} {suc j} (suc i) (s≤s le) = suc (strengthenFin {n} {j} i le)

strengthenFinLt : {n : ℕ} {j : Fin (ℕ.suc n)} → (i : Fin (ℕ.suc n)) → (le : toℕ i <' toℕ j) →
  toℕ (strengthenFin i le) <' toℕ j
strengthenFinLt {ℕ.zero} {zero} zero ()
strengthenFinLt {ℕ.zero} {suc ()} i le
strengthenFinLt {ℕ.suc n} {suc j} zero (s≤s z≤) = s≤s z≤
strengthenFinLt {ℕ.suc n} {suc j} (suc i) (s≤s le) = s≤s (strengthenFinLt {n} {j} i le)

weakenStrengthenFin : {n : ℕ} {j : Fin (ℕ.suc n)} → (i : Fin (ℕ.suc n)) → (le : toℕ i <' toℕ j) →
  weakenFin (strengthenFin i le) ≡ i
weakenStrengthenFin {ℕ.zero} {zero} i ()
weakenStrengthenFin {ℕ.zero} {suc ()} zero le
weakenStrengthenFin {ℕ.suc n} {suc j} zero le = refl
weakenStrengthenFin {ℕ.suc n} {suc j} (suc i) (s≤s le) =
  cong
  (λ a → suc a)
  (weakenStrengthenFin {n} {j} i le)

toℕstrengthenFin : {n : ℕ} {j : Fin (ℕ.suc n)} → (i : Fin (ℕ.suc n)) → (le : toℕ i <' toℕ j) →
  toℕ (strengthenFin i le) ≡ toℕ i
toℕstrengthenFin {ℕ.zero} {zero} i ()
toℕstrengthenFin {ℕ.zero} {suc ()} i (le)
toℕstrengthenFin {ℕ.suc n} {suc j} zero le = refl
toℕstrengthenFin {ℕ.suc n} {suc j} (suc i) (s≤s le) =
  cong (λ a → ℕ.suc a) (toℕstrengthenFin {n} {j} i le)

open BinaryRelation
≤'FinIsPropValued : ∀ {n : ℕ} → isPropValued (_≤'Fin_ {n})
≤'FinIsPropValued _ _ = ≤'IsPropValued _ _


data FinTrichotomy {n : ℕ} (i j : Fin n) : Type₀ where
  lt : i <'Fin j → FinTrichotomy i j
  eq : i ≡ j → FinTrichotomy i j
  gt : j <'Fin i → FinTrichotomy i j


FinTrichotomy-suc : {n : ℕ} {i j : Fin n} → FinTrichotomy i j → FinTrichotomy (suc i) (suc j)
FinTrichotomy-suc (lt i<j) = lt (s≤s i<j)
FinTrichotomy-suc (eq i=j) = eq (cong suc i=j)
FinTrichotomy-suc (gt j<i) = gt (s≤s j<i)

_≟Fin_ : {n : ℕ} (i j : Fin n) → FinTrichotomy i j
_≟Fin_ {n = ℕ.suc n} zero zero = eq refl
_≟Fin_ {n = ℕ.suc n} zero (suc j) = lt (s≤s z≤)
_≟Fin_ {n = ℕ.suc n} (suc i) zero = gt (s≤s z≤)
_≟Fin_ {n = ℕ.suc n} (suc i) (suc j) = FinTrichotomy-suc (i ≟Fin j)
