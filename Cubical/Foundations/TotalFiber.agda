{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.TotalFiber where

open import Cubical.Core.Everything
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Surjection
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' : Level

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  private
    ℓ'' : Level
    ℓ'' = ℓ-max ℓ ℓ'

    LiftA : Type ℓ''
    LiftA = Lift {j = ℓ'} A

  Total-fiber : Type ℓ''
  Total-fiber = Σ B \ b → fiber f b

  A→Total-fiber : A → Total-fiber
  A→Total-fiber a = f a , a , refl

  Total-fiber→A : Total-fiber → A
  Total-fiber→A (b , a , p) = a

  Total-fiber→A→Total-fiber : ∀ t → A→Total-fiber (Total-fiber→A t) ≡ t
  Total-fiber→A→Total-fiber (b , a , p) i = p i , a , λ j → p (i ∧ j)

  A→Total-fiber→A : ∀ a → Total-fiber→A (A→Total-fiber a) ≡ a
  A→Total-fiber→A a = refl

  LiftA→Total-fiber : LiftA → Total-fiber
  LiftA→Total-fiber x = A→Total-fiber (lower x)

  Total-fiber→LiftA : Total-fiber → LiftA
  Total-fiber→LiftA x = lift (Total-fiber→A x)

  Total-fiber→LiftA→Total-fiber : ∀ t → LiftA→Total-fiber (Total-fiber→LiftA t) ≡ t
  Total-fiber→LiftA→Total-fiber (b , a , p) i = p i , a , λ j → p (i ∧ j)

  LiftA→Total-fiber→LiftA : ∀ a → Total-fiber→LiftA (LiftA→Total-fiber a) ≡ a
  LiftA→Total-fiber→LiftA a = refl

  A≡Total : Lift A ≡ Total-fiber
  A≡Total = isoToPath (iso
    LiftA→Total-fiber
    Total-fiber→LiftA
    Total-fiber→LiftA→Total-fiber
    LiftA→Total-fiber→LiftA)

  -- HoTT Lemma 4.8.2
  A≃Total : A ≃ Total-fiber
  A≃Total = isoToEquiv (iso
    A→Total-fiber
    Total-fiber→A
    Total-fiber→A→Total-fiber
    (λ _ → refl))
