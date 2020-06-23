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

FunctorialEquivStr : {S : Type ℓ → Type ℓ₁}
  → (∀ {X Y} → (X → Y) → S X → S Y)
  → StrEquiv S ℓ₁
FunctorialEquivStr F (X , s) (Y , t) e = F (e .fst) s ≡ t

functorialUnivalentStr : {S : Type ℓ → Type ℓ₁}
  (F : ∀ {X Y} → (X → Y) → S X → S Y)
  → (∀ {X} s → F (idfun X) s ≡ s)
  → UnivalentStr S (FunctorialEquivStr F)
functorialUnivalentStr F η =
  UnivalentStr-≡→UnivalentStr
    (FunctorialEquivStr F)
    (λ s t → pathToEquiv (cong (_≡ t) (η s)))
