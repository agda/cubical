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
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- infix operator to more conveniently compose equivalences

_⋆_ = compEquiv

infixr 30 _⋆_

-- useful implications

EquivPresIsFinSet : A ≃ B → isFinSet A → isFinSet B
EquivPresIsFinSet e = rec isPropIsFinSet (λ (n , p) → ∣ n , compEquiv (invEquiv e) p ∣)

isFinSetFin : {n : ℕ} → isFinSet (Fin n)
isFinSetFin = ∣ _ , pathToEquiv refl ∣

isFinSetUnit : isFinSet Unit
isFinSetUnit = ∣ 1 , Unit≃Fin1 ∣

isFinSet→Discrete : isFinSet A → Discrete A
isFinSet→Discrete = rec isPropDiscrete (λ (_ , p) → EquivPresDiscrete (invEquiv p) discreteFin)

isContr→isFinSet : isContr A → isFinSet A
isContr→isFinSet h = ∣ 1 , isContr→≃Unit* h ⋆ invEquiv (Unit≃Unit* ) ⋆ Unit≃Fin1 ∣

isDecProp→isFinSet : isProp A → Dec A → isFinSet A
isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
isDecProp→isFinSet h (no ¬p) = ∣ 0 , uninhabEquiv ¬p ¬Fin0 ∣

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

-- logical equivalence of two definitions

isFinSet→isFinSet' : isFinSet A → isFinSet' A
isFinSet→isFinSet' ∣ n , equiv ∣ = n , ∣ equiv ∣
isFinSet→isFinSet' (squash p q i) = isPropIsFinSet' (isFinSet→isFinSet' p) (isFinSet→isFinSet' q) i

isFinSet'→isFinSet : isFinSet' A → isFinSet A
isFinSet'→isFinSet (n , ∣ isFinSet-A ∣) = ∣ n , isFinSet-A ∣
isFinSet'→isFinSet (n , squash p q i) = isPropIsFinSet (isFinSet'→isFinSet (n , p)) (isFinSet'→isFinSet (n , q)) i

isFinSet≡isFinSet' : isFinSet A ≡ isFinSet' A
isFinSet≡isFinSet' {A = A} = hPropExt isPropIsFinSet isPropIsFinSet' isFinSet→isFinSet' isFinSet'→isFinSet

FinSet→FinSet' : FinSet ℓ → FinSet' ℓ
FinSet→FinSet' (A , isFinSetA) = A , isFinSet→isFinSet' isFinSetA

FinSet'→FinSet : FinSet' ℓ → FinSet ℓ
FinSet'→FinSet (A , isFinSet'A) = A , isFinSet'→isFinSet isFinSet'A

FinSet≃FinSet' : FinSet ℓ ≃ FinSet' ℓ
FinSet≃FinSet' =
  isoToEquiv
    (iso FinSet→FinSet' FinSet'→FinSet
        (λ _ → Σ≡Prop (λ _ → isPropIsFinSet') refl)
        (λ _ → Σ≡Prop (λ _ → isPropIsFinSet) refl))

FinSet≡FinSet' : FinSet ℓ ≡ FinSet' ℓ
FinSet≡FinSet' = ua FinSet≃FinSet'

-- cardinality of finite sets

card : FinSet ℓ → ℕ
card = fst ∘ snd ∘ FinSet→FinSet'

-- definitions to reduce problems about FinSet to SumFin

≃Fin : Type ℓ → Type ℓ
≃Fin A = Σ[ n ∈ ℕ ] A ≃ Fin n

≃SumFin : Type ℓ → Type ℓ
≃SumFin A = Σ[ n ∈ ℕ ] A ≃ SumFin n

≃Fin→SumFin : ≃Fin A → ≃SumFin A
≃Fin→SumFin (n , e) = n , compEquiv e (invEquiv (SumFin≃Fin _))

≃SumFin→Fin : ≃SumFin A → ≃Fin A
≃SumFin→Fin (n , e) = n , compEquiv e (SumFin≃Fin _)

transpFamily :
    {A : Type ℓ}{B : A → Type ℓ'}
  → ((n , e) : ≃SumFin A) → (x : A) → B x ≃ B (invEq e (e .fst x))
transpFamily {B = B} (n , e) x = pathToEquiv (λ i → B (retEq e x (~ i)))
