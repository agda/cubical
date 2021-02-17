{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Reflection.StrictEquiv where

open import Cubical.Foundations.Prelude
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

strictEquivMacro : R.Term → R.Term → R.Term → R.TC Unit
strictEquivMacro f g hole =
  newMeta (R.def (quote Type) [ varg R.unknown ]) >>= λ A →
  newMeta (R.def (quote Type) [ varg R.unknown ]) >>= λ B →
  R.checkType hole (A `≃` B) >>
  newMeta (A `→` B) >>= λ fHole →
  newMeta (B `→` A) >>= λ gHole →
  R.unify f fHole >>
  R.unify g gHole >>
  R.unify (strictEquivTerm fHole gHole) hole

strictIsoToEquivMacro : R.Term → R.Term → R.TC Unit
strictIsoToEquivMacro isom =
  strictEquivMacro
    (R.def (quote Iso.fun) (isom v∷ []))
    (R.def (quote Iso.inv) (isom v∷ []))

macro
  -- (f : A → B) → (g : B → A) → (A ≃ B)
  -- Assumes that `f` and `g` are inverse up to definitional equality
  strictEquiv : R.Term → R.Term → R.Term → R.TC Unit
  strictEquiv = strictEquivMacro

  -- (isom : Iso A B) → (A ≃ B)
  -- Assumes that the functions defining `isom` are inverse up to definitional equality
  strictIsoToEquiv : R.Term → R.Term → R.TC Unit
  strictIsoToEquiv = strictIsoToEquivMacro
