{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Functorial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Foundations.SIP

private
  variable
    ℓ ℓ₁ : Level

-- Standard notion of structure from a "functorial" action
-- We don't need all the functor axioms, only F id ≡ id

FunctorialIso : {S : Type ℓ → Type ℓ₁}
  → (∀ {X Y} → (X → Y) → S X → S Y)
  → StrEquiv S ℓ₁
FunctorialIso F (X , s) (Y , t) e = F (e .fst) s ≡ t

functorialUnivalentStr : {S : Type ℓ → Type ℓ₁}
  (F : ∀ {X Y} → (X → Y) → S X → S Y)
  → (∀ {X} s → F (idfun X) s ≡ s)
  → UnivalentStr S (FunctorialIso F)
functorialUnivalentStr F η =
  UnivalentStr-≡→UnivalentStr
    (FunctorialIso F)
    (λ s t → pathToEquiv (cong (_≡ t) (η s)))
