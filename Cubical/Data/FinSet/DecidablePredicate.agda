{-

This files contains:
- Lots of useful properties about (this) decidable predicates on finite sets.
  (P.S. We use the alternative definition of decidability for computational effectivity.)

-}

module Cubical.Data.FinSet.DecidablePredicate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Equiv.Properties

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Data.Fin
open import Cubical.Data.SumFin renaming (Fin to SumFin)
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
  hiding (DecProp) renaming (DecProp' to DecProp)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _
  (X : Type ℓ)(p : isFinOrd X) where

  isDecProp¬' : isDecProp (¬ X)
  isDecProp¬' = _ ,  invEquiv (preCompEquiv (p .snd)) ⋆ SumFin¬ _

  isDecProp∥∥' : isDecProp ∥ X ∥₁
  isDecProp∥∥' = _ , propTrunc≃ (p .snd) ⋆ SumFin∥∥DecProp _

module _
  (X : Type ℓ )(p : isFinOrd X)
  (P : X → Type ℓ')
  (dec : (x : X) → isDecProp (P x)) where

  private
    e = p .snd

  isFinOrdSub : isFinOrd (Σ X P)
  isFinOrdSub = _ ,
      Σ-cong-equiv {B' = λ x → P (invEq e x)} e (transpFamily p)
    ⋆ Σ-cong-equiv-snd (λ x → dec (invEq e x) .snd)
    ⋆ SumFinSub≃ _ (fst ∘ dec ∘ invEq e)

  isDecProp∃' : isDecProp ∥ Σ X P ∥₁
  isDecProp∃' = _ ,
      Prop.propTrunc≃ (
        Σ-cong-equiv {B' = λ x → P (invEq e x)} e (transpFamily p)
      ⋆ Σ-cong-equiv-snd (λ x → dec (invEq e x) .snd))
    ⋆ SumFin∃≃ _ (fst ∘ dec ∘ invEq e)

  isDecProp∀' : isDecProp ((x : X) → P x)
  isDecProp∀' = _ ,
      equivΠ {B' = λ x → P (invEq e x)} e (transpFamily p)
    ⋆ equivΠCod (λ x → dec (invEq e x) .snd)
    ⋆ SumFin∀≃ _ (fst ∘ dec ∘ invEq e)

module _
  (X : Type ℓ )(p : isFinOrd X)
  (a b : X) where

  private
    e = p .snd

  isDecProp≡' : isDecProp (a ≡ b)
  isDecProp≡' .fst = SumFin≡ _ (e .fst a) (e .fst b)
  isDecProp≡' .snd = congEquiv e ⋆ SumFin≡≃ _ _ _

module _
  (X : FinSet ℓ)
  (P : X .fst → DecProp ℓ') where

  isFinSetSub : isFinSet (Σ (X .fst) (λ x → P x .fst))
  isFinSetSub = Prop.rec isPropIsFinSet
    (λ p → isFinOrd→isFinSet (isFinOrdSub (X .fst) (_ , p) (λ x → P x .fst) (λ x → P x .snd)))
    (X .snd .snd)

  isDecProp∃ : isDecProp ∥ Σ (X .fst) (λ x → P x .fst) ∥₁
  isDecProp∃ = Prop.rec isPropIsDecProp
    (λ p → isDecProp∃' (X .fst) (_ , p) (λ x → P x .fst) (λ x → P x .snd)) (X .snd .snd)

  isDecProp∀ : isDecProp ((x : X .fst) → P x .fst)
  isDecProp∀ = Prop.rec isPropIsDecProp
    (λ p → isDecProp∀' (X .fst) (_ , p) (λ x → P x .fst) (λ x → P x .snd)) (X .snd .snd)

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ')
  (Z : (x : X .fst) → Y x .fst → DecProp ℓ'') where

  isDecProp∀2 : isDecProp ((x : X .fst) → (y : Y x .fst) → Z x y .fst)
  isDecProp∀2 = isDecProp∀ X (λ x → _ , isDecProp∀ (Y x) (Z x))

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ')
  (Z : (x : X .fst) → Y x .fst → FinSet ℓ'')
  (W : (x : X .fst) → (y : Y x .fst) → Z x y .fst → DecProp ℓ''') where

  isDecProp∀3 : isDecProp ((x : X .fst) → (y : Y x .fst) → (z : Z x y .fst) → W x y z .fst)
  isDecProp∀3 = isDecProp∀ X (λ x → _ , isDecProp∀2 (Y x) (Z x) (W x))

module _
  (X : FinSet ℓ) where

  isDecProp≡ : (a b : X .fst) → isDecProp (a ≡ b)
  isDecProp≡ a b = Prop.rec isPropIsDecProp
    (λ p → isDecProp≡' (X .fst) (_ , p) a b) (X .snd .snd)

module _
  (P : DecProp ℓ )
  (Q : DecProp ℓ') where

  isDecProp× : isDecProp (P .fst × Q .fst)
  isDecProp× .fst = P .snd .fst and Q .snd .fst
  isDecProp× .snd = Σ-cong-equiv (P .snd .snd) (λ _ → Q .snd .snd) ⋆ Bool→Type×≃ _ _

module _
  (X : FinSet ℓ) where

  isDecProp¬ : isDecProp (¬ (X .fst))
  isDecProp¬ = Prop.rec isPropIsDecProp
    (λ p → isDecProp¬' (X .fst) (_ , p)) (X .snd .snd)

  isDecProp∥∥ : isDecProp ∥ X .fst ∥₁
  isDecProp∥∥ = Prop.rec isPropIsDecProp
    (λ p → isDecProp∥∥' (X .fst) (_ , p)) (X .snd .snd)
