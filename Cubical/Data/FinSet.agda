{-

Definition of finite sets

A set is finite if it is merely equivalent to `Fin n` for some `n`. We
can translate this to code in two ways: a truncated sigma of a nat and
an equivalence, or a sigma of a nat and a truncated equivalence. We
prove that both formulations are equivalent.

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.FinSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A : Type ℓ

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∃[ n ∈ ℕ ] A ≃ Fin n

isProp-isFinSet : isProp (isFinSet A)
isProp-isFinSet = propTruncIsProp

FinSet : Type (ℓ-suc ℓ)
FinSet = TypeWithStr _ isFinSet

isFinSetFin : ∀ {n} → isFinSet (Fin n)
isFinSetFin = ∣ _ , pathToEquiv refl ∣

isFinSetUnit : isFinSet Unit
isFinSetUnit = ∣ 1 , Unit≃Fin1 ∣

isFinSetΣ : Type ℓ → Type ℓ
isFinSetΣ A = Σ[ n ∈ ℕ ] ∥ A ≃ Fin n ∥

FinSetΣ : Type (ℓ-suc ℓ)
FinSetΣ = TypeWithStr _ isFinSetΣ

isProp-isFinSetΣ : isProp (isFinSetΣ A)
isProp-isFinSetΣ {A = A} (n , equivn) (m , equivm) =
  Σ≡Prop (λ _ → propTruncIsProp) n≡m
  where
    Fin-n≃Fin-m : ∥ Fin n ≃ Fin m ∥
    Fin-n≃Fin-m = rec
      propTruncIsProp
      (rec
        (isPropΠ λ _ → propTruncIsProp)
        (λ hm hn → ∣ Fin n ≃⟨ invEquiv hn ⟩ A ≃⟨ hm ⟩ Fin m ■ ∣)
        equivm
      )
      equivn

    Fin-n≡Fin-m : ∥ Fin n ≡ Fin m ∥
    Fin-n≡Fin-m = rec propTruncIsProp (∣_∣ ∘ ua) Fin-n≃Fin-m

    ∥n≡m∥ : ∥ n ≡ m ∥
    ∥n≡m∥ = rec propTruncIsProp (∣_∣ ∘ Fin-inj n m) Fin-n≡Fin-m

    n≡m : n ≡ m
    n≡m = rec (isSetℕ n m) (λ p → p) ∥n≡m∥

isFinSet≡isFinSetΣ : isFinSet A ≡ isFinSetΣ A
isFinSet≡isFinSetΣ {A = A} = hPropExt isProp-isFinSet isProp-isFinSetΣ to from
  where
    to : isFinSet A → isFinSetΣ A
    to ∣ n , equiv ∣ = n , ∣ equiv ∣
    to (squash p q i) = isProp-isFinSetΣ (to p) (to q) i

    from : isFinSetΣ A → isFinSet A
    from (n , ∣ isFinSet-A ∣) = ∣ n , isFinSet-A ∣
    from (n , squash p q i) = isProp-isFinSet (from (n , p)) (from (n , q)) i

FinSet≡FinSetΣ : FinSet {ℓ} ≡ FinSetΣ
FinSet≡FinSetΣ = ua (isoToEquiv (iso to from to-from from-to))
  where
    to : FinSet → FinSetΣ
    to (A , isFinSetA) = A , transport isFinSet≡isFinSetΣ isFinSetA

    from : FinSetΣ → FinSet
    from (A , isFinSetΣA) = A , transport (sym isFinSet≡isFinSetΣ) isFinSetΣA

    to-from : ∀ A → to (from A) ≡ A
    to-from A = Σ≡Prop (λ _ → isProp-isFinSetΣ) refl

    from-to : ∀ A → from (to A) ≡ A
    from-to A = Σ≡Prop (λ _ → isProp-isFinSet) refl

card : FinSet {ℓ} → ℕ
card = fst ∘ snd ∘ transport FinSet≡FinSetΣ
