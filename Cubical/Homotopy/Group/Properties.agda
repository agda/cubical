{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.Group.Properties where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR

open import Cubical.Data.Nat

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Abelianization.Properties

connectedFun→πEquiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → GroupEquiv (πGr n A) (πGr n B)
connectedFun→πEquiv {ℓ = ℓ}  {A = A} {B = B} n f conf =
  (πHom n f .fst
  , subst isEquiv (funExt (ST.elim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (πA≃πB .snd))
  , πHom n f .snd
  where
  lem : (n : ℕ) → suc (suc n) ∸ n ≡ 2
  lem zero = refl
  lem (suc n) = lem n

  connΩ^→f : isConnectedFun 2 (fst (Ω^→ (suc n) f))
  connΩ^→f = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc (suc n)) (suc n) f conf)

  πA≃πB : π (suc n) A ≃ π (suc n) B
  πA≃πB = compEquiv setTrunc≃Trunc2
         (compEquiv (connectedTruncEquiv 2
                     (fst (Ω^→ (suc n) f)) connΩ^→f)
          (invEquiv setTrunc≃Trunc2))

connectedFun→π'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) = π'∘∙Hom n f .fst
snd (fst (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) =
  transport (λ i → isEquiv (GroupHomπ≅π'PathP-hom n f i .fst))
            (connectedFun→πEquiv n f conf .fst .snd)
snd (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf) = π'∘∙Hom n f .snd

connected→Abπ'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → AbGroupEquiv (AbelianizationAbGroup (π'Gr n A)) (AbelianizationAbGroup (π'Gr n B))
connected→Abπ'Equiv n f isc = AbelianizationEquiv (connectedFun→π'Equiv n f isc)

connectedFun→πSurj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 + n) (fst f)
  → isSurjective {G = πGr n A} {H = πGr n B} (πHom n f)
connectedFun→πSurj {ℓ = ℓ}  {A = A} {B = B} n f conf =
  ST.elim (λ _ → isProp→isSet squash₁)
    λ p → TR.rec squash₁ (λ {(q , r) → ∣ ∣ q ∣₂ , (cong ∣_∣₂ r) ∣₁})
                 (connΩ^→f p .fst)
  where
  lem : (n : ℕ) → suc n ∸ n ≡ 1
  lem zero = refl
  lem (suc n) = lem n

  connΩ^→f : isConnectedFun 1 (fst (Ω^→ (suc n) f))
  connΩ^→f = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
                    (lem n)
                    (isConnectedΩ^→ (suc n) (suc n) f conf)

connectedFun→π'Surj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 + n) (fst f)
  → isSurjective (π'∘∙Hom n f)
connectedFun→π'Surj n f conf =
  transport (λ i → isSurjective (GroupHomπ≅π'PathP-hom n f i))
            (connectedFun→πSurj n f conf)
