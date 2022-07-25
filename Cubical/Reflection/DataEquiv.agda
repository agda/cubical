{-
  Reflection-based isomorphism between a non-recursive data type and a coproduct of Σ-types.
-}
module Cubical.Reflection.DataEquiv where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Sum
--open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma

open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

getSigmaType : List (String × R.Type) → R.Type
getSigmaType [] = R.def (quote Unit) []
getSigmaType ((argName , argTy) ∷ args) = R.def (quote Σ) (
  argTy v∷
  R.lam R.visible (R.abs argName (getSigmaType args)) v∷
  [])

getCoprodType : List (R.Name × List (String × R.Type)) → R.Type
getCoprodType [] = R.def (quote ⊥) []
getCoprodType ((consName , consArgs) ∷ constructors) = R.def (quote _⊎_) (
  getSigmaType consArgs v∷
  getCoprodType constructors v∷
  [])

piToList : R.Name → R.Type → R.TC (List (String × R.Type))
piToList consName (R.var x args) = R.returnTC []
piToList consName (R.con c args) = R.returnTC []
piToList consName (R.def f args) = R.returnTC [] -- we should look up the definition in case of a strictly positive datatype
piToList consName (R.lam v₁ t) = R.returnTC []
piToList consName (R.pat-lam cs args) = R.returnTC []
piToList consName (R.pi (R.arg _ a) (R.abs argStr b)) = liftTC ((argStr , a) ∷_) (piToList consName b)
piToList consName (R.agda-sort s) = R.returnTC []
piToList consName (R.lit l) = R.returnTC []
piToList consName (R.meta x x₁) = R.returnTC []
piToList consName R.unknown = R.returnTC []

getConsArgs : ℕ → R.Name → R.TC (List (String × R.Type))
getConsArgs nParams consName = do
  ty ← R.getType consName
  liftTC (drop nParams) (piToList consName ty)

getAllConsArgs : ℕ → List R.Name → R.TC (List (R.Name × List (String × R.Type)))
getAllConsArgs nParams [] = R.returnTC []
getAllConsArgs nParams (consName ∷ consNames) = do
  consArgs ← getConsArgs nParams consName
  liftTC ((consName , consArgs) ∷_) (getAllConsArgs nParams consNames)

declareDataIso⊎' : R.Name → R.Name → ℕ → List R.Name → R.TC Unit
declareDataIso⊎' idName dataName nParams consNames = do
  constructors ← getAllConsArgs nParams consNames
  let coprodType = getCoprodType constructors
  {!!}

declareDataIso⊎ : R.Name → R.Name → R.TC Unit
declareDataIso⊎ idName dataName =
  R.getDefinition dataName >>= λ where
    (R.data-type nParams consNames) → declareDataIso⊎' idName dataName nParams consNames
    _ → R.typeError (R.strErr "Not a data type name:" ∷ R.nameErr dataName ∷ [])

private
  module Example where
    variable
      ℓ ℓ' : Level
      A : Type ℓ
      B : A → Type ℓ'

    data Example0 {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
      spam : A → Example0 B
      eggs : (a : A) → B a → Example0 B

    --unquoteDecl i = declareDataIso⊎ i (quote Example0)
