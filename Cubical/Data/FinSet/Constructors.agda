{-

This files contains:
- Facts about constructions on finite sets, especially when they preserve finiteness.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Constructors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.Fin.LehmerCode as LehmerCode
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.FiniteChoice

open import Cubical.Relation.Nullary

open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _
  (X : Type ℓ)(p : isFinOrd X) where

  isFinOrd∥∥ : isFinOrd ∥ X ∥
  isFinOrd∥∥ = _ , propTrunc≃ (p .snd) ⋆ SumFin∥∥≃ _

  isFinOrd≃ : isFinOrd (X ≃ X)
  isFinOrd≃ = _ , equivComp (p .snd) (p .snd) ⋆ SumFin≃≃ _

module _
  (X : Type ℓ )(p : isFinOrd X)
  (Y : Type ℓ')(q : isFinOrd Y) where

  isFinOrd⊎ : isFinOrd (X ⊎ Y)
  isFinOrd⊎ = _ , ⊎-equiv (p .snd) (q .snd) ⋆ SumFin⊎≃ _ _

  isFinOrd× : isFinOrd (X × Y)
  isFinOrd× = _ , Σ-cong-equiv (p .snd) (λ _ → q .snd) ⋆ SumFin×≃ _ _

module _
  (X : Type ℓ )(p : isFinOrd X)
  (Y : X → Type ℓ')(q : (x : X) → isFinOrd (Y x)) where

  private
    e = p .snd

    f : (x : X) → ℕ
    f x = q x .fst

  isFinOrdΣ : isFinOrd (Σ X Y)
  isFinOrdΣ = _ ,
      Σ-cong-equiv {B' = λ x → Y (invEq e x)} e (transpFamily p)
    ⋆ Σ-cong-equiv-snd (λ x → q (invEq e x) .snd)
    ⋆ SumFinΣ≃ _ _

  isFinOrdΠ : isFinOrd ((x : X) → Y x)
  isFinOrdΠ = _ ,
      equivΠ {B' = λ x → Y (invEq e x)} e (transpFamily p)
    ⋆ equivΠCod (λ x → q (invEq e x) .snd)
    ⋆ SumFinΠ≃ _ _

-- closedness under several type constructors

module _
  (X : FinSet ℓ)
  (Y : X .fst → FinSet ℓ') where

  isFinSetΣ : isFinSet (Σ (X .fst) (λ x → Y x .fst))
  isFinSetΣ = rec2 isPropIsFinSet
    (λ p q → isFinOrd→isFinSet (isFinOrdΣ (X .fst) (_ , p) (λ x → Y x .fst) q))
    (X .snd .snd) (choice X (λ x → isFinOrd (Y x .fst)) (λ x → isFinSet→isFinSet' (Y x .snd)))

  isFinSetΠ : isFinSet ((x : X .fst) → Y x .fst)
  isFinSetΠ = rec2 isPropIsFinSet
    (λ p q → isFinOrd→isFinSet (isFinOrdΠ (X .fst) (_ , p) (λ x → Y x .fst) q))
    (X .snd .snd) (choice X (λ x → isFinOrd (Y x .fst)) (λ x → isFinSet→isFinSet' (Y x .snd)))

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

  isFinSet∥∥ : isFinSet ∥ X .fst ∥
  isFinSet∥∥ = Prop.rec isPropIsFinSet (λ p → isFinOrd→isFinSet (isFinOrd∥∥ (X .fst) (_ , p))) (X .snd .snd)

  isFinSetIsContr : isFinSet (isContr (X .fst))
  isFinSetIsContr = isFinSetΣ X (λ x → _ , (isFinSetΠ X (λ y → _ , isFinSet≡ x y)))

  isFinSetIsProp : isFinSet (isProp (X .fst))
  isFinSetIsProp = isFinSetΠ2 X (λ _ → X) (λ x x' → _ , isFinSet≡ x x')

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
  isFinSet⊎ = card X + card Y ,
    map2 (λ p q → isFinOrd⊎ (X .fst) (_ , p) (Y .fst) (_ , q) .snd) (X .snd .snd) (Y .snd .snd)

  isFinSet× : isFinSet (X .fst × Y .fst)
  isFinSet× = card X · card Y ,
    map2 (λ p q → isFinOrd× (X .fst) (_ , p) (Y .fst) (_ , q) .snd) (X .snd .snd) (Y .snd .snd)

  isFinSet→ : isFinSet (X .fst → Y .fst)
  isFinSet→ = isFinSetΠ X (λ _ → Y)

  isFinSet≃ : isFinSet (X .fst ≃ Y .fst)
  isFinSet≃ = isFinSetΣ (_ , isFinSet→) (λ f → _ , isFinSetIsEquiv X Y f)

module _
  (X Y : FinSet ℓ ) where

  isFinSetType≡ : isFinSet (X .fst ≡ Y .fst)
  isFinSetType≡ = EquivPresIsFinSet (invEquiv univalence) (isFinSet≃ X Y)

module _
  (X : FinSet ℓ) where

  isFinSetAut : isFinSet (X .fst ≃ X .fst)
  isFinSetAut = LehmerCode.factorial (card X) ,
    Prop.map (λ p → isFinOrd≃ (X .fst) (card X , p) .snd) (X .snd .snd)

  isFinSetTypeAut : isFinSet (X .fst ≡ X .fst)
  isFinSetTypeAut = EquivPresIsFinSet (invEquiv univalence) isFinSetAut

module _
  (X : FinSet ℓ) where

  isFinSet¬ : isFinSet (¬ (X .fst))
  isFinSet¬ = isFinSet→ X (Fin 0 , isFinSetFin)

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

-- a criterion of being finite set

module _
  (X : Type ℓ)(Y : FinSet ℓ')
  (f : X → Y .fst)
  (h : (y : Y .fst) → isFinSet (fiber f y)) where

  isFinSetTotal : isFinSet X
  isFinSetTotal = EquivPresIsFinSet (invEquiv (totalEquiv f)) (isFinSetΣ Y (λ y → _ , h y))

-- a criterion of fibers being finite sets, more general than the previous result

module _
  (X : FinSet ℓ)
  (Y : Type ℓ')(h : Discrete Y)
  (f : X. fst → Y) where

  isFinSetFiberDisc : (y : Y) → isFinSet (fiber f y)
  isFinSetFiberDisc y = isFinSetΣ X (λ x → _ , isDecProp→isFinSet (Discrete→isSet h _ _) (h (f x) y))
