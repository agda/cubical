{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Nat
import Cubical.Data.Nat.Order.Recursive as Ord
import Cubical.Data.Fin as Fin
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- operators to more conveniently compose equivalences

module _
  {A : Type ℓ}{B : Type ℓ'}{C : Type ℓ''} where

  infixr 30 _⋆̂_

  _⋆̂_ : ∥ A ≃ B ∥₁ → ∥ B ≃ C ∥₁ → ∥ A ≃ C ∥₁
  _⋆̂_ = Prop.map2 (_⋆_)

module _
  {A : Type ℓ}{B : Type ℓ'} where

  ∣invEquiv∣ : ∥ A ≃ B ∥₁ → ∥ B ≃ A ∥₁
  ∣invEquiv∣ = Prop.map invEquiv

-- useful implications

EquivPresIsFinSet : A ≃ B → isFinSet A → isFinSet B
EquivPresIsFinSet e (_ , p) = _ , ∣ invEquiv e ∣₁ ⋆̂ p

isFinSetFin : {n : ℕ} → isFinSet (Fin n)
isFinSetFin = _ , ∣ idEquiv _ ∣₁

isFinSetUnit : isFinSet Unit
isFinSetUnit = 1 , ∣ invEquiv Fin1≃Unit ∣₁

isFinSetBool : isFinSet Bool
isFinSetBool = 2 , ∣ invEquiv SumFin2≃Bool ∣₁

isFinSet→Discrete : isFinSet A → Discrete A
isFinSet→Discrete h = Prop.rec isPropDiscrete (λ p → EquivPresDiscrete (invEquiv p) discreteFin) (h .snd)

isContr→isFinSet : isContr A → isFinSet A
isContr→isFinSet h = 1 , ∣ isContr→≃Unit h ⋆ invEquiv Fin1≃Unit ∣₁

isDecProp→isFinSet : isProp A → Dec A → isFinSet A
isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
isDecProp→isFinSet h (no ¬p) = 0 , ∣ uninhabEquiv ¬p (idfun _) ∣₁

isDec→isFinSet∥∥ : Dec A → isFinSet ∥ A ∥₁
isDec→isFinSet∥∥ dec = isDecProp→isFinSet isPropPropTrunc (Dec∥∥ dec)

isFinSet→Dec∥∥ : isFinSet A → Dec ∥ A ∥₁
isFinSet→Dec∥∥ h =
  Prop.rec (isPropDec isPropPropTrunc)
      (λ p → EquivPresDec (propTrunc≃ (invEquiv p)) (Dec∥Fin∥ _)) (h .snd)

isFinProp→Dec : isFinSet A → isProp A → Dec A
isFinProp→Dec p h = subst Dec (propTruncIdempotent h) (isFinSet→Dec∥∥ p)

PeirceLaw∥∥ : isFinSet A → NonEmpty ∥ A ∥₁ → ∥ A ∥₁
PeirceLaw∥∥ p = Dec→Stable (isFinSet→Dec∥∥ p)

PeirceLaw : isFinSet A → NonEmpty A → ∥ A ∥₁
PeirceLaw p q = PeirceLaw∥∥ p (λ f → q (λ x → f ∣ x ∣₁))

-- transprot family towards Fin

transpFamily :
    {A : Type ℓ}{B : A → Type ℓ'}
  → ((n , e) : isFinOrd A) → (x : A) → B x ≃ B (invEq e (e .fst x))
transpFamily {B = B} (n , e) x = pathToEquiv (λ i → B (retEq e x (~ i)))

isContr→isFinOrd : ∀ {ℓ} → {A : Type ℓ} →
  isContr A → isFinOrd A
isContr→isFinOrd isContrA = 1 , isContr→Equiv isContrA isContrSumFin1

isFinSet⊥ : isFinSet ⊥
isFinSet⊥ = isFinSetFin

isFinSetLift :
  {L L' : Level} →
  {A : Type L} →
  isFinSet A → isFinSet (Lift {L}{L'} A)
fst (isFinSetLift {A = A} isFinSetA) = isFinSetA .fst
snd (isFinSetLift {A = A} isFinSetA) =
  Prop.elim
  {P = λ _ → ∥ Lift A ≃ Fin (isFinSetA .fst) ∥₁}
  (λ [a] → isPropPropTrunc )
  (λ A≅Fin → ∣ compEquiv (invEquiv (LiftEquiv {A = A})) A≅Fin ∣₁)
  (isFinSetA .snd)

EquivPresIsFinOrd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → isFinOrd A → isFinOrd B
EquivPresIsFinOrd e (_ , p) = _ , compEquiv (invEquiv e) p

isFinOrdFin : ∀ {n} → isFinOrd (Fin n)
isFinOrdFin {n} = n , (idEquiv (Fin n))

isFinOrd⊥ : isFinOrd ⊥
fst isFinOrd⊥ = 0
snd isFinOrd⊥ = idEquiv ⊥

isFinOrdUnit : isFinOrd Unit
isFinOrdUnit =
  EquivPresIsFinOrd
    (isContr→Equiv isContrSumFin1 isContrUnit) isFinOrdFin

takeFirstFinOrd : ∀ {ℓ} → (A : Type ℓ) →
  (the-ord : isFinOrd A) → 0 Ord.< the-ord .fst → A
takeFirstFinOrd A (suc n , the-eq) x =
  the-eq .snd .equiv-proof (Fin→SumFin (Fin.fromℕ≤ 0 n x)) .fst .fst

isFinSet⊤ : isFinSet ⊤
isFinSet⊤ = 1 , ∣ invEquiv ⊎-IdR-⊥-≃ ∣₁
