

{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Properties where

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
open import Cubical.Data.FinSet hiding (isFinSetΣ)
open import Cubical.Data.FinSet.SumFinReduction
open import Cubical.Data.FinSet.FiniteChoice

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Nullary.HLevels

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

isFinSet→Discrete : {X : Type ℓ} → isFinSet X → Discrete X
isFinSet→Discrete p =
  TruncRec isPropDiscrete (λ (_ , p) → EquivPresDiscrete (invEquiv p) discreteFin) p

isFinSet→isSet : {X : Type ℓ} → isFinSet X → isSet X
isFinSet→isSet p = Discrete→isSet (isFinSet→Discrete p)

isContr→isFinSet : {X : Type ℓ} → isContr X → isFinSet X
isContr→isFinSet h = ∣ 1 , isContr→≃Unit* h ⋆ invEquiv (Unit≃Unit* ) ⋆ Unit≃Fin1 ∣

isDecProp→isFinSet : {P : Type ℓ} → isProp P → Dec P → isFinSet P
isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
isDecProp→isFinSet h (no ¬p) = ∣ 0 , uninhabEquiv ¬p ¬Fin0 ∣

EquivPresFinSet : {X : Type ℓ}{Y : Type ℓ'} → X ≃ Y → isFinSet X → isFinSet Y
EquivPresFinSet e p = TruncRec isProp-isFinSet (λ (n , p) → ∣ n , compEquiv (invEquiv e) p ∣) p

module _
  (X : Type ℓ)(p : ≃Fin X) where

  ≃Fin∥∥ : ≃Fin ∥ X ∥
  ≃Fin∥∥ = ≃SumFin→Fin (_ , compEquiv (propTrunc≃ (≃Fin→SumFin p .snd)) (SumFin∥∥ _))

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
  (X : FinSet {ℓ})
  (Y : X .fst → FinSet {ℓ'}) where

  isFinSetΣ : isFinSet (Σ (X .fst) (λ x → Y x .fst))
  isFinSetΣ =
    elim2 (λ _ _ → isProp-isFinSet {A = Σ (X .fst) (λ x → Y x .fst)})
          (λ p q → ∣ ≃FinΣ (X .fst) p (λ x → Y x .fst) q ∣)
          (X .snd) (choice X (λ x → ≃Fin (Y x .fst)) (λ x → Y x .snd))

  isFinSetΠ : isFinSet ((x : X .fst) → Y x .fst)
  isFinSetΠ =
    elim2 (λ _ _ → isProp-isFinSet {A = ((x : X .fst) → Y x .fst)})
          (λ p q → ∣ ≃FinΠ (X .fst) p (λ x → Y x .fst) q ∣)
          (X .snd) (choice X (λ x → ≃Fin (Y x .fst)) (λ x → Y x .snd))

module _
  (X : FinSet {ℓ})
  (Y : X .fst → FinSet {ℓ'})
  (Z : (x : X .fst) → Y x .fst → FinSet {ℓ''}) where

  isFinSetΠ2 : isFinSet ((x : X .fst) → (y : Y x .fst) → Z x y .fst)
  isFinSetΠ2 = isFinSetΠ X (λ x → _ , isFinSetΠ (Y x) (Z x))

module _
  (X : FinSet {ℓ})
  (Y : X .fst → FinSet {ℓ'})
  (Z : (x : X .fst) → Y x .fst → FinSet {ℓ''})
  (W : (x : X .fst) → (y : Y x .fst) → Z x y .fst → FinSet {ℓ'''}) where

  isFinSetΠ3 : isFinSet ((x : X .fst) → (y : Y x .fst) → (z : Z x y .fst) → W x y z .fst)
  isFinSetΠ3 = isFinSetΠ X (λ x → _ , isFinSetΠ2 (Y x) (Z x) (W x))

module _
  (X : FinSet {ℓ}) where

  isFinSet≡ : (a b : X .fst) → isFinSet (a ≡ b)
  isFinSet≡ a b = isDecProp→isFinSet (isFinSet→isSet (X .snd) a b) (isFinSet→Discrete (X .snd) a b)

  isFinSetIsContr : isFinSet (isContr (X .fst))
  isFinSetIsContr = isFinSetΣ X (λ x → _ , (isFinSetΠ X (λ y → _ , isFinSet≡ x y)))

  isFinSet∥∥ : isFinSet ∥ X .fst ∥
  isFinSet∥∥ = TruncRec isProp-isFinSet (λ p → ∣ ≃Fin∥∥ (X .fst) p ∣) (X .snd)

module _
  (X : FinSet {ℓ })
  (Y : FinSet {ℓ'})
  (f : X .fst → Y .fst) where

  isFinSetFiber : (y : Y .fst) → isFinSet (fiber f y)
  isFinSetFiber y = isFinSetΣ X (λ x → _ , isFinSet≡ Y (f x) y)

  isFinSetIsEquiv : isFinSet (isEquiv f)
  isFinSetIsEquiv =
    EquivPresFinSet
      (invEquiv (isEquiv≃isEquiv' f))
      (isFinSetΠ Y (λ y → _ , isFinSetIsContr (_ , isFinSetFiber y)))

module _
  (X : FinSet {ℓ })
  (Y : FinSet {ℓ'}) where

  isFinSet⊎ : isFinSet (X .fst ⊎ Y .fst)
  isFinSet⊎ = elim2 (λ _ _ → isProp-isFinSet) (λ p q → ∣ ≃Fin⊎ (X .fst) p (Y .fst) q ∣) (X .snd) (Y .snd)

  isFinSet× : isFinSet (X .fst × Y .fst)
  isFinSet× = elim2 (λ _ _ → isProp-isFinSet) (λ p q → ∣ ≃Fin× (X .fst) p (Y .fst) q ∣) (X .snd) (Y .snd)

  isFinSet→ : isFinSet (X .fst → Y .fst)
  isFinSet→ = isFinSetΠ X (λ _ → Y)

  isFinSet≃ : isFinSet (X .fst ≃ Y .fst)
  isFinSet≃ = isFinSetΣ (_ , isFinSet→) (λ f → _ , isFinSetIsEquiv X Y f)

module _
  (X : FinSet {ℓ}) where

  isFinSet¬ : isFinSet (¬ (X .fst))
  isFinSet¬ = isFinSet→ X (⊥ , ∣ 0 , uninhabEquiv (λ x → x) ¬Fin0 ∣)

module _
  (X : FinSet {ℓ}) where

  isFinSetNonEmpty : isFinSet (NonEmpty (X .fst))
  isFinSetNonEmpty = isFinSet¬ (_ , isFinSet¬ X)

module _
  {X : Type ℓ }
  {Y : Type ℓ'}
  (f : X → Y) where

  isInjective : Type (ℓ-max ℓ ℓ')
  isInjective = (a b : X) → ¬ (a ≡ b) → ¬ (f a ≡ f b)

  isSurjective : Type (ℓ-max ℓ ℓ')
  isSurjective = (y : Y) → NonEmpty (fiber f y)

  isBijective : Type (ℓ-max ℓ ℓ')
  isBijective = isInjective × isSurjective

module _
  (X : Type ℓ )
  (Y : Type ℓ') where

  Injection : Type (ℓ-max ℓ ℓ')
  Injection = Σ[ f ∈ (X → Y) ] isInjective f

  Surjection : Type (ℓ-max ℓ ℓ')
  Surjection = Σ[ f ∈ (X → Y) ] isSurjective f

  Bijection : Type (ℓ-max ℓ ℓ')
  Bijection = Σ[ f ∈ (X → Y) ] isBijective f

module _
  (X : FinSet {ℓ })
  (Y : FinSet {ℓ'})
  (f : X .fst → Y .fst) where

  isFinSetIsInjective : isFinSet (isInjective f)
  isFinSetIsInjective =
    isFinSetΠ3
      X (λ _ → X) (λ a b → _ , isFinSet¬ (_ , isFinSet≡ X a b))
      (λ a b _ → _ , isFinSet¬ (_ , isFinSet≡ Y (f a) (f b)))

  isFinSetIsSurjective : isFinSet (isSurjective f)
  isFinSetIsSurjective =
    isFinSetΠ Y (λ y → _ , isFinSetNonEmpty (_ , isFinSetFiber X Y f y))

  isFinSetIsBijective : isFinSet (isBijective f)
  isFinSetIsBijective = isFinSet× (_ , isFinSetIsInjective) (_ , isFinSetIsSurjective)

module _
  (X : FinSet {ℓ })
  (Y : FinSet {ℓ'}) where

  isFinSetInjection : isFinSet (Injection (X .fst) (Y .fst))
  isFinSetInjection =
    isFinSetΣ (_ , isFinSet→ X Y) (λ f → _ , isFinSetIsInjective X Y f)

  isFinSetSurjection : isFinSet (Surjection (X .fst) (Y .fst))
  isFinSetSurjection =
    isFinSetΣ (_ , isFinSet→ X Y) (λ f → _ , isFinSetIsSurjective X Y f)

  isFinSetBijection : isFinSet (Bijection (X .fst) (Y .fst))
  isFinSetBijection =
    isFinSetΣ (_ , isFinSet→ X Y) (λ f → _ , isFinSetIsBijective X Y f)

-- some computable function

card+ : ℕ → ℕ → ℕ
card+ m n = card (Fin m ⊎ Fin n , isFinSet⊎ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card× : ℕ → ℕ → ℕ
card× m n = card (Fin m × Fin n , isFinSet× (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card→ : ℕ → ℕ → ℕ
card→ m n = card ((Fin m → Fin n) , isFinSet→ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card≃ : ℕ → ℕ → ℕ
card≃ m n = card ((Fin m ≃ Fin n) , isFinSet≃ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardInj : ℕ → ℕ → ℕ
cardInj m n = card (Injection (Fin m) (Fin n) , isFinSetInjection (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardSurj : ℕ → ℕ → ℕ
cardSurj m n = card (Surjection (Fin m) (Fin n) , isFinSetSurjection (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardBij : ℕ → ℕ → ℕ
cardBij m n = card (Bijection (Fin m) (Fin n) , isFinSetBijection (Fin m , isFinSetFin) (Fin n , isFinSetFin))
