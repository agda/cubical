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
  where
    Unit≃Fin1 : Unit ≃ Fin 1
    Unit≃Fin1 =
      isoToEquiv
        (iso
          (const fzero)
          (const tt)
          (isContrFin1 .snd)
          (isContrUnit .snd)
        )

isFinSet′ : Type ℓ → Type ℓ
isFinSet′ A = Σ[ n ∈ ℕ ] ∥ A ≃ Fin n ∥

FinSet′ : Type (ℓ-suc ℓ)
FinSet′ = TypeWithStr _ isFinSet′

isProp-isFinSet′ : isProp (isFinSet′ A)
isProp-isFinSet′ {A = A} (n , equivn) (m , equivm) =
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

isFinSet≡isFinSet′ : isFinSet A ≡ isFinSet′ A
isFinSet≡isFinSet′ {A = A} = ua (isoToEquiv (iso to from to-from from-to))
  where
    to : isFinSet A → isFinSet′ A
    to ∣ n , equiv ∣ = n , ∣ equiv ∣
    to (squash p q i) = isProp-isFinSet′ (to p) (to q) i

    from : isFinSet′ A → isFinSet A
    from (n , ∣ isFinSet-A ∣) = ∣ n , isFinSet-A ∣
    from (n , squash p q i) = isProp-isFinSet (from (n , p)) (from (n , q)) i

    to-from : ∀ isFinSet-A → to (from isFinSet-A) ≡ isFinSet-A
    to-from isFinSet′-A = isProp-isFinSet′ (to (from isFinSet′-A)) isFinSet′-A

    from-to : ∀ isFinSet′-A → from (to isFinSet′-A) ≡ isFinSet′-A
    from-to isFinSet-A = isProp-isFinSet (from (to isFinSet-A)) isFinSet-A

FinSet≡FinSet′ : FinSet {ℓ} ≡ FinSet′
FinSet≡FinSet′ = ua (isoToEquiv (iso to from to-from from-to))
  where
    to : FinSet → FinSet′
    to (A , isFinSetA) = A , transport isFinSet≡isFinSet′ isFinSetA

    from : FinSet′ → FinSet
    from (A , isFinSet′A) = A , transport (sym isFinSet≡isFinSet′) isFinSet′A

    to-from : ∀ A → to (from A) ≡ A
    to-from A = Σ≡Prop (λ _ → isProp-isFinSet′) refl

    from-to : ∀ A → from (to A) ≡ A
    from-to A = Σ≡Prop (λ _ → isProp-isFinSet) refl

card : FinSet {ℓ} → ℕ
card = fst ∘ snd ∘ transport FinSet≡FinSet′
