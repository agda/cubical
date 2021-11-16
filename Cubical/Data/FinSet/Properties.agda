{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to EmptyRec)
open import Cubical.Data.Sigma

open import Cubical.Data.Fin
open import Cubical.Data.SumFin renaming (Fin to SumFin) hiding (discreteFin)
open import Cubical.Data.FinSet.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Nullary.HLevels

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- infix operator to more conveniently compose equivalences

_⋆_ = compEquiv

infixr 30 _⋆_

-- useful implications

isFinSetFin : ∀ {n} → isFinSet (Fin n)
isFinSetFin = ∣ _ , pathToEquiv refl ∣

isFinSetUnit : isFinSet Unit
isFinSetUnit = ∣ 1 , Unit≃Fin1 ∣

isFinSet→Discrete : {X : Type ℓ} → isFinSet X → Discrete X
isFinSet→Discrete p =
  rec isPropDiscrete (λ (_ , p) → EquivPresDiscrete (invEquiv p) discreteFin) p

isFinSet→isSet : {X : Type ℓ} → isFinSet X → isSet X
isFinSet→isSet p = Discrete→isSet (isFinSet→Discrete p)

isContr→isFinSet : {X : Type ℓ} → isContr X → isFinSet X
isContr→isFinSet h = ∣ 1 , isContr→≃Unit* h ⋆ invEquiv (Unit≃Unit* ) ⋆ Unit≃Fin1 ∣

isDecProp→isFinSet : {P : Type ℓ} → isProp P → Dec P → isFinSet P
isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
isDecProp→isFinSet h (no ¬p) = ∣ 0 , uninhabEquiv ¬p ¬Fin0 ∣

EquivPresFinSet : {X : Type ℓ}{Y : Type ℓ'} → X ≃ Y → isFinSet X → isFinSet Y
EquivPresFinSet e p = rec isPropIsFinSet (λ (n , p) → ∣ n , compEquiv (invEquiv e) p ∣) p

{-

Alternative definition of finite sets

A set is finite if it is merely equivalent to `Fin n` for some `n`. We
can translate this to code in two ways: a truncated sigma of a nat and
an equivalence, or a sigma of a nat and a truncated equivalence. We
prove that both formulations are equivalent.

-}

isFinSet' : Type ℓ → Type ℓ
isFinSet' A = Σ[ n ∈ ℕ ] ∥ A ≃ Fin n ∥

FinSet' : (ℓ : Level) → Type (ℓ-suc ℓ)
FinSet' ℓ = TypeWithStr _ isFinSet'

isPropIsFinSet' : isProp (isFinSet' A)
isPropIsFinSet' {A = A} (n , equivn) (m , equivm) =
  Σ≡Prop (λ _ → isPropPropTrunc) n≡m
  where
    Fin-n≃Fin-m : ∥ Fin n ≃ Fin m ∥
    Fin-n≃Fin-m = rec
      isPropPropTrunc
      (rec
        (isPropΠ λ _ → isPropPropTrunc)
        (λ hm hn → ∣ Fin n ≃⟨ invEquiv hn ⟩ A ≃⟨ hm ⟩ Fin m ■ ∣)
        equivm
      )
      equivn

    Fin-n≡Fin-m : ∥ Fin n ≡ Fin m ∥
    Fin-n≡Fin-m = rec isPropPropTrunc (∣_∣ ∘ ua) Fin-n≃Fin-m

    ∥n≡m∥ : ∥ n ≡ m ∥
    ∥n≡m∥ = rec isPropPropTrunc (∣_∣ ∘ Fin-inj n m) Fin-n≡Fin-m

    n≡m : n ≡ m
    n≡m = rec (isSetℕ n m) (λ p → p) ∥n≡m∥

isFinSet≡isFinSet' : isFinSet A ≡ isFinSet' A
isFinSet≡isFinSet' {A = A} = hPropExt isPropIsFinSet isPropIsFinSet' to from
  where
    to : isFinSet A → isFinSet' A
    to ∣ n , equiv ∣ = n , ∣ equiv ∣
    to (squash p q i) = isPropIsFinSet' (to p) (to q) i

    from : isFinSet' A → isFinSet A
    from (n , ∣ isFinSet-A ∣) = ∣ n , isFinSet-A ∣
    from (n , squash p q i) = isPropIsFinSet (from (n , p)) (from (n , q)) i

FinSet≡FinSet' : FinSet ℓ ≡ FinSet' ℓ
FinSet≡FinSet' = ua (isoToEquiv (iso to from to-from from-to))
  where
    to : FinSet ℓ → FinSet' ℓ
    to (A , isFinSetA) = A , transport isFinSet≡isFinSet' isFinSetA

    from : FinSet' ℓ → FinSet ℓ
    from (A , isFinSet'A) = A , transport (sym isFinSet≡isFinSet') isFinSet'A

    to-from : ∀ A → to (from A) ≡ A
    to-from A = Σ≡Prop (λ _ → isPropIsFinSet') refl

    from-to : ∀ A → from (to A) ≡ A
    from-to A = Σ≡Prop (λ _ → isPropIsFinSet) refl

-- cardinality of finite sets

card : FinSet ℓ → ℕ
card = fst ∘ snd ∘ transport FinSet≡FinSet'

-- Definitions to reduce problems about FinSet to SumFin

≃Fin : Type ℓ → Type ℓ
≃Fin A = Σ[ n ∈ ℕ ] A ≃ Fin n

≃SumFin : Type ℓ → Type ℓ
≃SumFin A = Σ[ n ∈ ℕ ] A ≃ SumFin n

≃Fin→SumFin : {X : Type ℓ} → ≃Fin X → ≃SumFin X
≃Fin→SumFin (n , e) = n , compEquiv e (invEquiv (SumFin≃Fin _))

≃SumFin→Fin : {X : Type ℓ} → ≃SumFin X → ≃Fin X
≃SumFin→Fin (n , e) = n , compEquiv e (SumFin≃Fin _)

transpFamily : {X : Type ℓ}{Y : X → Type ℓ'}
  → ((n , e) : ≃SumFin X) → (x : X) → Y x ≃ Y (invEq e (e .fst x))
transpFamily {X = X} {Y = Y} (n , e) x = pathToEquiv (λ i → Y (retEq e x (~ i)))
