{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Reflection.StrictEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.List.Base
open import Cubical.Data.Unit.Base

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

private
  Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
  Fun A B = A → B

  _`→`_ : R.Term → R.Term → R.Term
  A `→` B = R.def (quote Fun) (A v∷ B v∷ [])

  _`≃`_ : R.Term → R.Term → R.Term
  A `≃` B = R.def (quote _≃_) (A v∷ B v∷ [])

  `id` : R.Term → R.Term
  `id` t = R.def (quote idfun) (R.unknown v∷ t v∷ [])

strictEquivTerm : R.Term → R.Term → R.Term
strictEquivTerm f g =
  R.pat-lam
    ( R.clause []
        (R.proj (quote fst) v∷ [])
        f
    ∷ R.clause []
        (R.proj (quote snd) v∷ R.proj (quote equiv-proof) v∷ [])
        (R.def (quote strictContrFibers) (g v∷ []))
    ∷ []
    )
    []

strictEquivMacro : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → B) → (B → A) → R.Term → R.TC Unit
strictEquivMacro {A = A} {B} f g hole =
  R.quoteTC A >>= λ `A` →
  R.quoteTC B >>= λ `B` →
  R.checkType hole (`A` `≃` `B`) >>
  R.quoteTC f >>= λ `f` →
  R.quoteTC g >>= λ `g` →
  R.unify (strictEquivTerm `f` `g`) hole

strictIsoToEquivMacro : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B → R.Term → R.TC Unit
strictIsoToEquivMacro isom =
  strictEquivMacro (Iso.fun isom) (Iso.inv isom)

macro
  -- (f : A → B) → (g : B → A) → (A ≃ B)
  -- Assumes that `f` and `g` are inverse up to definitional equality
  strictEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (A → B) → (B → A) → R.Term → R.TC Unit
  strictEquiv = strictEquivMacro

  -- (isom : Iso A B) → (A ≃ B)
  -- Assumes that the functions defining `isom` are inverse up to definitional equality
  strictIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → Iso A B → R.Term → R.TC Unit
  strictIsoToEquiv = strictIsoToEquivMacro
