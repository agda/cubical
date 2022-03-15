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
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
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

  _⋆̂_ : ∥ A ≃ B ∥ → ∥ B ≃ C ∥ → ∥ A ≃ C ∥
  _⋆̂_ = Prop.map2 (_⋆_)

module _
  {A : Type ℓ}{B : Type ℓ'} where

  ∣invEquiv∣ : ∥ A ≃ B ∥ → ∥ B ≃ A ∥
  ∣invEquiv∣ = Prop.map invEquiv

-- useful implications

EquivPresIsFinSet : A ≃ B → isFinSet A → isFinSet B
EquivPresIsFinSet e (_ , p) = _ , ∣ invEquiv e ∣ ⋆̂ p

isFinSetFin : {n : ℕ} → isFinSet (Fin n)
isFinSetFin = _ , ∣ idEquiv _ ∣

isFinSetUnit : isFinSet Unit
isFinSetUnit = 1 , ∣ invEquiv Fin1≃Unit ∣

isFinSetBool : isFinSet Bool
isFinSetBool = 2 , ∣ invEquiv SumFin2≃Bool ∣

isFinSet→Discrete : isFinSet A → Discrete A
isFinSet→Discrete h = Prop.rec isPropDiscrete (λ p → EquivPresDiscrete (invEquiv p) discreteFin) (h .snd)

isContr→isFinSet : isContr A → isFinSet A
isContr→isFinSet h = 1 , ∣ isContr→≃Unit* h ⋆ invEquiv Unit≃Unit* ⋆ invEquiv Fin1≃Unit ∣

isDecProp→isFinSet : isProp A → Dec A → isFinSet A
isDecProp→isFinSet h (yes p) = isContr→isFinSet (inhProp→isContr p h)
isDecProp→isFinSet h (no ¬p) = 0 , ∣ uninhabEquiv ¬p (idfun _) ∣

isDec→isFinSet∥∥ : Dec A → isFinSet ∥ A ∥
isDec→isFinSet∥∥ dec = isDecProp→isFinSet isPropPropTrunc (Dec∥∥ dec)

isFinSet→Dec∥∥ : isFinSet A → Dec ∥ A ∥
isFinSet→Dec∥∥ h =
  Prop.rec (isPropDec isPropPropTrunc)
      (λ p → EquivPresDec (propTrunc≃ (invEquiv p)) (Dec∥Fin∥ _)) (h .snd)

isFinProp→Dec : isFinSet A → isProp A → Dec A
isFinProp→Dec p h = subst Dec (propTruncIdempotent h) (isFinSet→Dec∥∥ p)

PeirceLaw∥∥ : isFinSet A → NonEmpty ∥ A ∥ → ∥ A ∥
PeirceLaw∥∥ p = Dec→Stable (isFinSet→Dec∥∥ p)

PeirceLaw : isFinSet A → NonEmpty A → ∥ A ∥
PeirceLaw p q = PeirceLaw∥∥ p (λ f → q (λ x → f ∣ x ∣))

-- transprot family towards Fin

transpFamily :
    {A : Type ℓ}{B : A → Type ℓ'}
  → ((n , e) : isFinOrd A) → (x : A) → B x ≃ B (invEq e (e .fst x))
transpFamily {B = B} (n , e) x = pathToEquiv (λ i → B (retEq e x (~ i)))
