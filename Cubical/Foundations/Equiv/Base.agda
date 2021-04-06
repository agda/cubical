{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Core.Glue public
  using (isEquiv ; equiv-proof ; _≃_ ; equivFun ; equivProof ; lineToEquiv)

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- The identity equivalence
idIsEquiv : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

idIsEquiv' : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
idIsEquiv' A = subst isEquiv (λ i → transp (λ i → A) i)
                     (lineToEquiv (λ i → A) .snd)

idEquiv' : ∀ {ℓ} (A : Type ℓ) → A ≃ A
fst (idEquiv' A) = idfun A
snd (idEquiv' A) = idIsEquiv' A

idEquiv'≡lineEquiv : ∀ {ℓ} (A : Type ℓ) → lineToEquiv (λ i → A) ≡ idEquiv' A
fst (idEquiv'≡lineEquiv A i) = transp (λ i → A) i 
snd (idEquiv'≡lineEquiv A j) = transp (λ i → isEquiv (transp (λ i → A) (i ∧ j))) (~ j)
                                      (lineToEquiv (λ i → A) .snd)
