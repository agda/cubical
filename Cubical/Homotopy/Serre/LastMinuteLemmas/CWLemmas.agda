{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.CWLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

open import Cubical.CW.Base
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.SmashProduct.SymmetricMonoidal
open import Cubical.HITs.Wedge
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Connected

open import Cubical.Homotopy.Serre.FiniteCW

private
  variable
    ℓ ℓ' ℓ'' : Level

-- move to Cubical.Fin.Instances.Sum
isFinCW⊎ : {A B : Type ℓ} → isFinCW A → isFinCW B
  → isFinCW (A ⊎ B)
isFinCW⊎ {A = A} {B = B} fA fB =
  subst isFinCW
    (isoToPath PushoutEmptyDomainIso*)
    (isFinCWPushout {X = ⊥*} {A} {B}
      (λ()) (λ()) (snd (finCW⊥* _)) fA fB)
  where
  PushoutEmptyDomainIso* : {A : Type ℓ} {B : Type ℓ'}
    → Iso (Pushout {A = ⊥* {ℓ''}} {B = A} {C = B}
                    (λ()) (λ()))
           (A ⊎ B)
  PushoutEmptyDomainIso* .Iso.fun (inl x) = inl x
  PushoutEmptyDomainIso* .Iso.fun (inr x) = inr x
  PushoutEmptyDomainIso* .Iso.inv (inl x) = inl x
  PushoutEmptyDomainIso* .Iso.inv (inr x) = inr x
  PushoutEmptyDomainIso* .Iso.sec (inl x) = refl
  PushoutEmptyDomainIso* .Iso.sec (inr x) = refl
  PushoutEmptyDomainIso* .Iso.ret (inl x) = refl
  PushoutEmptyDomainIso* .Iso.ret (inr x) = refl

-- move to Cubical.Fin.Instances.Fin
isFinCWFin : (n : ℕ) → isFinCW (Fin n)
isFinCWFin zero =
  subst isFinCW (ua (uninhabEquiv (λ()) ¬Fin0))
        (snd finCW⊥)
isFinCWFin (suc n) =
  subst isFinCW (isoToPath (Iso-Fin1⊎Fin-FinSuc {n}))
    (isFinCW⊎
      (subst isFinCW
        (ua (isContr→Equiv isContrUnit*
             (fzero , isPropFin1 fzero)))
        isFinCWUnit)
    (isFinCWFin n))

module _ {A B : Pointed ℓ} (cwA : isFinCW (typ A)) (cwB : isFinCW (typ B)) where
  private
    A⋁B' = Pushout {A = Unit* {ℓ = ℓ}} (λ _ → pt A) (λ _ → pt B)

    A⋁B'≃A⋁B : A⋁B' ≃ (A ⋁ B)
    A⋁B'≃A⋁B = invEquiv (pushoutEquiv _ _ _ _ LiftEquiv
                                      (idEquiv _) (idEquiv _) refl refl)

    A⋀B' = Pushout {A = A⋁B'} {B = Unit* {ℓ = ℓ}}
                   (λ _ → tt*) (⋁↪ ∘ fst A⋁B'≃A⋁B)

    A⋀B'≃A⋀B : A⋀B' ≃ (A ⋀ B)
    A⋀B'≃A⋀B = pushoutEquiv _ _ _ _ A⋁B'≃A⋁B
                            (invEquiv LiftEquiv) (idEquiv _) refl refl

  -- Move to Cubical.CW.Instances.Wedge
  isFinCW⋁ : isFinCW (A ⋁ B)
  isFinCW⋁ = subst isFinCW (sym lem)
                   (isFinCWPushout _ _ isFinCWUnit cwA cwB)
    where
    lem : A ⋁ B ≡ Pushout {A = Unit* {ℓ = ℓ}} (λ _ → pt A) (λ _ → pt B)
    lem = ua (pushoutEquiv _ _ _ _ LiftEquiv (idEquiv _) (idEquiv _) refl refl)

  -- Move to Cubical.CW.Instances.SmashProduct
  isFinCW⋀ : isFinCW (A ⋀ B)
  isFinCW⋀ = subst isFinCW (sym lem⋀)
                   (isFinCWPushout _ _ isFinCW⋁ isFinCWUnit
                     (isFinCW× (_ , cwA) (_ , cwB)))
    where
    lem⋀ : A ⋀ B ≡ Pushout {A = A ⋁ B} {B = Unit* {ℓ = ℓ}} (λ _ → tt*) ⋁↪
    lem⋀ = ua (pushoutEquiv _ _ _ _
                (idEquiv _) LiftEquiv (idEquiv _) refl refl)
