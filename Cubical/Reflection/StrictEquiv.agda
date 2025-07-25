module Cubical.Reflection.StrictEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.List.Base
open import Cubical.Data.Unit.Base

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

strictEquivClauses : R.Term → R.Term → List R.Clause
strictEquivClauses f g =
  R.clause []
    (R.proj (quote fst) v∷ [])
    f
  ∷ R.clause []
    (R.proj (quote snd) v∷ R.proj (quote equiv-proof) v∷ [])
    (R.def (quote strictContrFibers) (g v∷ []))
  ∷ []

strictEquivTerm : R.Term → R.Term → R.Term
strictEquivTerm f g = R.pat-lam (strictEquivClauses f g) []

strictEquivMacro : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → B) → (B → A) → R.Term → R.TC Unit
strictEquivMacro {A = A} {B} f g hole =
  R.quoteTC (A ≃ B) >>= λ equivTy →
  R.checkType hole equivTy >>
  R.quoteTC f >>= λ `f` →
  R.quoteTC g >>= λ `g` →
  R.unify (strictEquivTerm `f` `g`) hole

strictIsoToEquivMacro : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B → R.Term → R.TC Unit
strictIsoToEquivMacro isom =
  strictEquivMacro (Iso.fun isom) (Iso.inv isom)

-- For use with unquoteDef

defStrictEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → R.Name → (A → B) → (B → A) → R.TC Unit
defStrictEquiv idName f g =
  R.quoteTC f >>= λ `f` →
  R.quoteTC g >>= λ `g` →
  R.defineFun idName (strictEquivClauses `f` `g`)

defStrictIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → R.Name → Iso A B → R.TC Unit
defStrictIsoToEquiv idName isom =
  defStrictEquiv idName (Iso.fun isom) (Iso.inv isom)

-- For use with unquoteDef

declStrictEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → R.Name → (A → B) → (B → A) → R.TC Unit
declStrictEquiv {A = A} {B = B} idName f g =
  R.quoteTC (A ≃ B) >>= λ ty →
  R.declareDef (varg idName) ty >>
  defStrictEquiv idName f g

declStrictIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → R.Name → Iso A B → R.TC Unit
declStrictIsoToEquiv idName isom =
  declStrictEquiv idName (Iso.fun isom) (Iso.inv isom)

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
