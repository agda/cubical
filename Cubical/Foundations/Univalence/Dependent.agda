{-

Dependent Version of Univalence

The univalence corresponds to the dependent equivalences/isomorphisms,
c.f. `Cubical.Foundations.Equiv.Dependent`.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Univalence.Dependent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level


-- Dependent Univalence

-- A quicker proof provided by @ecavallo: uaOver e F equiv = ua→ (λ a → ua (_ , equiv a))
-- Unfortunately it gives a larger term overall.
uaOver :
  {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'}
  (e : A ≃ B) (F : mapOver (e .fst) P Q)
  (equiv : isEquivOver {P = P} {Q = Q} F)
  → PathP (λ i → ua e i → Type ℓ') P Q
uaOver {A = A} {P = P} {Q} e F equiv i x =
  hcomp (λ j → λ
    { (i = i0) → ua (_ , equiv x) (~ j)
    ; (i = i1) → Q x })
  (Q (unglue (i ∨ ~ i) x))


-- Dependent `isoToPath`

open isHAEquiv

isoToPathOver :
  {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'}
  (f : A → B) (hae : isHAEquiv f)
  (isom : IsoOver (isHAEquiv→Iso hae) P Q)
  → PathP (λ i → ua (_ , isHAEquiv→isEquiv hae) i → Type ℓ') P Q
isoToPathOver f hae isom = uaOver _ _ (isoToEquivOver f hae isom)
