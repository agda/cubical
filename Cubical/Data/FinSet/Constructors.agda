{-

Closure properties of FinSet under several type constructors.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Constructors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation renaming (rec to TruncRec)

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to EmptyRec)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.Fin
open import Cubical.Data.SumFin renaming (Fin to SumFin) hiding (discreteFin)
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.FiniteChoice

open import Cubical.Relation.Nullary

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _
  (X : Type ℓ)(p : ≃Fin X) where

  ≃Fin∥∥ : ≃Fin ∥ X ∥
  ≃Fin∥∥ = ≃SumFin→Fin (_ , compEquiv (propTrunc≃ (≃Fin→SumFin p .snd)) (SumFin∥∥≃ _))

module _
  (X : Type ℓ )(p : ≃Fin X)
  (Y : Type ℓ')(q : ≃Fin Y) where

  ≃Fin⊎ : ≃Fin (X ⊎ Y)
  ≃Fin⊎ = ≃SumFin→Fin (_ , compEquiv (⊎-equiv (≃Fin→SumFin p .snd) (≃Fin→SumFin q .snd)) (SumFin⊎≃ _ _))

  ≃Fin× : ≃Fin (X × Y)
  ≃Fin× = ≃SumFin→Fin (_ , compEquiv (Σ-cong-equiv (≃Fin→SumFin p .snd) (λ _ → ≃Fin→SumFin q .snd)) (SumFin×≃ _ _))

module _
  (X : Type ℓ )(p : ≃Fin X)
  (Y : X → Type ℓ')(q : (x : X) → ≃Fin (Y x)) where

  private
    p' = ≃Fin→SumFin p

    m = p' .fst
    e = p' .snd

    q' : (x : X) → ≃SumFin (Y x)
    q' x = ≃Fin→SumFin (q x)

    f : (x : X) → ℕ
    f x = q' x .fst

  ≃SumFinΣ : ≃SumFin (Σ X Y)
  ≃SumFinΣ = _ ,
      Σ-cong-equiv {B' = λ x → Y (invEq (p' .snd) x)} (p' .snd) (transpFamily p')
    ⋆ Σ-cong-equiv-snd (λ x → q' (invEq e x) .snd)
    ⋆ SumFinΣ≃ _ _

  ≃SumFinΠ : ≃SumFin ((x : X) → Y x)
  ≃SumFinΠ = _ ,
      equivΠ {B' = λ x → Y (invEq (p' .snd) x)} (p' .snd) (transpFamily p')
    ⋆ equivΠCod (λ x → q' (invEq e x) .snd)
    ⋆ SumFinΠ≃ _ _

  ≃FinΣ : ≃Fin (Σ X Y)
  ≃FinΣ = ≃SumFin→Fin ≃SumFinΣ

  ≃FinΠ : ≃Fin ((x : X) → Y x)
  ≃FinΠ = ≃SumFin→Fin ≃SumFinΠ

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ') where

  isFinSetΣ : isFinSet (Σ (X .fst) (λ x → Y x .fst))
  isFinSetΣ =
    elim2 (λ _ _ → isPropIsFinSet {A = Σ (X .fst) (λ x → Y x .fst)})
          (λ p q → ∣ ≃FinΣ (X .fst) p (λ x → Y x .fst) q ∣)
          (X .snd) (choice X (λ x → ≃Fin (Y x .fst)) (λ x → Y x .snd))

  isFinSetΠ : isFinSet ((x : X .fst) → Y x .fst)
  isFinSetΠ =
    elim2 (λ _ _ → isPropIsFinSet {A = ((x : X .fst) → Y x .fst)})
          (λ p q → ∣ ≃FinΠ (X .fst) p (λ x → Y x .fst) q ∣)
          (X .snd) (choice X (λ x → ≃Fin (Y x .fst)) (λ x → Y x .snd))

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ')
  (Z : (x : X .fst) → Y x .fst → FinSet ℓ'') where

  isFinSetΠ2 : isFinSet ((x : X .fst) → (y : Y x .fst) → Z x y .fst)
  isFinSetΠ2 = isFinSetΠ X (λ x → _ , isFinSetΠ (Y x) (Z x))

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ')
  (Z : (x : X .fst) → Y x .fst → FinSet ℓ'')
  (W : (x : X .fst) → (y : Y x .fst) → Z x y .fst → FinSet ℓ''') where

  isFinSetΠ3 : isFinSet ((x : X .fst) → (y : Y x .fst) → (z : Z x y .fst) → W x y z .fst)
  isFinSetΠ3 = isFinSetΠ X (λ x → _ , isFinSetΠ2 (Y x) (Z x) (W x))

module _
  (X : FinSet ℓ) where

  isFinSet≡ : (a b : X .fst) → isFinSet (a ≡ b)
  isFinSet≡ a b = isDecProp→isFinSet (isFinSet→isSet (X .snd) a b) (isFinSet→Discrete (X .snd) a b)

  isFinSetIsContr : isFinSet (isContr (X .fst))
  isFinSetIsContr = isFinSetΣ X (λ x → _ , (isFinSetΠ X (λ y → _ , isFinSet≡ x y)))

  isFinSet∥∥ : isFinSet ∥ X .fst ∥
  isFinSet∥∥ = TruncRec isPropIsFinSet (λ p → ∣ ≃Fin∥∥ (X .fst) p ∣) (X .snd)

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ')
  (f : X .fst → Y .fst) where

  isFinSetFiber : (y : Y .fst) → isFinSet (fiber f y)
  isFinSetFiber y = isFinSetΣ X (λ x → _ , isFinSet≡ Y (f x) y)

  isFinSetIsEquiv : isFinSet (isEquiv f)
  isFinSetIsEquiv =
    EquivPresIsFinSet
      (invEquiv (isEquiv≃isEquiv' f))
      (isFinSetΠ Y (λ y → _ , isFinSetIsContr (_ , isFinSetFiber y)))

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  isFinSet⊎ : isFinSet (X .fst ⊎ Y .fst)
  isFinSet⊎ = elim2 (λ _ _ → isPropIsFinSet) (λ p q → ∣ ≃Fin⊎ (X .fst) p (Y .fst) q ∣) (X .snd) (Y .snd)

  isFinSet× : isFinSet (X .fst × Y .fst)
  isFinSet× = elim2 (λ _ _ → isPropIsFinSet) (λ p q → ∣ ≃Fin× (X .fst) p (Y .fst) q ∣) (X .snd) (Y .snd)

  isFinSet→ : isFinSet (X .fst → Y .fst)
  isFinSet→ = isFinSetΠ X (λ _ → Y)

  isFinSet≃ : isFinSet (X .fst ≃ Y .fst)
  isFinSet≃ = isFinSetΣ (_ , isFinSet→) (λ f → _ , isFinSetIsEquiv X Y f)

module _
  (X : FinSet ℓ) where

  isFinSet¬ : isFinSet (¬ (X .fst))
  isFinSet¬ = isFinSet→ X (⊥ , ∣ 0 , uninhabEquiv (λ x → x) ¬Fin0 ∣)

module _
  (X : FinSet ℓ) where

  isFinSetNonEmpty : isFinSet (NonEmpty (X .fst))
  isFinSetNonEmpty = isFinSet¬ (_ , isFinSet¬ X)

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ')
  (f : X .fst → Y .fst) where

  isFinSetIsEmbedding : isFinSet (isEmbedding f)
  isFinSetIsEmbedding =
    isFinSetΠ2 X (λ _ → X)
      (λ a b → _ , isFinSetIsEquiv (_ , isFinSet≡ X a b) (_ , isFinSet≡ Y (f a) (f b)) (cong f))

  isFinSetIsSurjection : isFinSet (isSurjection f)
  isFinSetIsSurjection =
    isFinSetΠ Y (λ y → _ , isFinSet∥∥ (_ , isFinSetFiber X Y f y))

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  isFinSet↪ : isFinSet (X .fst ↪ Y .fst)
  isFinSet↪ = isFinSetΣ (_ , isFinSet→ X Y) (λ f → _ , isFinSetIsEmbedding X Y f)

  isFinSet↠ : isFinSet (X .fst ↠ Y .fst)
  isFinSet↠ = isFinSetΣ (_ , isFinSet→ X Y) (λ f → _ , isFinSetIsSurjection X Y f)
