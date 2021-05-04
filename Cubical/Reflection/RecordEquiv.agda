{-

  Reflection-based tools for converting between iterated record types, particularly between
  record types and iterated Σ-types.

  See end of file for examples.

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.RecordEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma

open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

Projections = Maybe (List R.Name)

-- Describes a correspondence between two iterated record types
RecordAssoc = List (Projections × Projections)

-- Describes a correspondence between a record type and an iterated Σ-types;
-- more convenient than RecordAssoc for this special case
data ΣFormat : Type where
  leaf : R.Name → ΣFormat
  _,_ : ΣFormat → ΣFormat → ΣFormat
  unit : ΣFormat

infixr 4 _,_

flipRecordAssoc : RecordAssoc → RecordAssoc
flipRecordAssoc = List.map λ {p .fst → p .snd; p .snd → p .fst}

fstIdRecordAssoc : RecordAssoc → RecordAssoc
fstIdRecordAssoc = List.map λ {p .fst → p .fst; p .snd → p .fst}

List→ΣFormat : List R.Name → ΣFormat
List→ΣFormat [] = unit
List→ΣFormat (x ∷ []) = leaf x
List→ΣFormat (x ∷ y ∷ xs) = leaf x , List→ΣFormat (y ∷ xs)

ΣFormat→RecordAssoc : ΣFormat → RecordAssoc
ΣFormat→RecordAssoc = go []
  where
  go : List R.Name → ΣFormat → RecordAssoc
  go prefix unit = [ just prefix , nothing ]
  go prefix (leaf fieldName) = [ just prefix , just [ fieldName ] ]
  go prefix (sig₁ , sig₂) =
    go (quote fst ∷ prefix) sig₁ ++ go (quote snd ∷ prefix) sig₂

-- Derive the shape of the compound Σ-type
ΣFormat→Ty : ΣFormat → R.Type
ΣFormat→Ty unit = R.def (quote Unit) []
ΣFormat→Ty (leaf _) = R.unknown
ΣFormat→Ty (sig₁ , sig₂) =
  R.def (quote Σ) (ΣFormat→Ty sig₁ v∷ R.lam R.visible (R.abs "_" (ΣFormat→Ty sig₂)) v∷ [])

recordName→isoTy : R.Name → R.Term → R.TC R.Term
recordName→isoTy name σShape =
  R.inferType (R.def name []) >>= R.normalise >>= go []
  where
  go : List R.ArgInfo → R.Type → R.TC R.Term
  go acc (R.pi (R.arg i argTy) (R.abs s ty)) =
    liftTC (λ t → R.pi (R.arg i' argTy) (R.abs s t)) (go (i ∷ acc) ty)
    where
    i' = R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)
  go acc (R.agda-sort _) =
    R.returnTC (R.def (quote Iso) (R.def name (makeArgs 0 [] acc) v∷ σShape v∷ []))
    where
    makeArgs : ℕ → List (R.Arg R.Term) → List R.ArgInfo → List (R.Arg R.Term)
    makeArgs n acc [] = acc
    makeArgs n acc (i ∷ infos) = makeArgs (suc n) (R.arg i (v n) ∷ acc) infos
  go _ _ = R.typeError (R.strErr "Not a record type name: " ∷ R.nameErr name ∷ [])

projNames→Patterns : List R.Name → List (R.Arg R.Pattern)
projNames→Patterns = go []
  where
  go : List (R.Arg R.Pattern) → List R.Name → List (R.Arg R.Pattern)
  go acc [] = acc
  go acc (π ∷ projs) = go (varg (R.proj π) ∷ acc) projs

projNames→Term : R.Term → List R.Name → R.Term
projNames→Term term [] = term
projNames→Term term (π ∷ projs) = R.def π [ varg (projNames→Term term projs) ]

convertClauses : RecordAssoc → R.Term → List R.Clause
convertClauses al term = fixIfEmpty (List.filterMap makeClause al)
  where
  makeClause : Projections × Projections → Maybe R.Clause
  makeClause (projl , just projr) =
    just (R.clause [] (goPat [] projr) (Maybe.rec R.unknown goTm projl))
    where
    goPat : List (R.Arg R.Pattern) → List R.Name → List (R.Arg R.Pattern)
    goPat acc [] = acc
    goPat acc (π ∷ projs) = goPat (varg (R.proj π) ∷ acc) projs

    goTm : List R.Name → R.Term
    goTm [] = term
    goTm (π ∷ projs) = R.def π [ varg (goTm projs) ]
  makeClause (_ , nothing) = nothing

  fixIfEmpty : List R.Clause → List R.Clause
  fixIfEmpty [] = [ R.clause [] [] R.unknown ]
  fixIfEmpty (c ∷ cs) = c ∷ cs

mapClause :
  (List (String × R.Arg R.Type) → List (String × R.Arg R.Type))
  → (List (R.Arg R.Pattern) → List (R.Arg R.Pattern))
  → (R.Clause → R.Clause)
mapClause f g (R.clause tel ps t) = R.clause (f tel) (g ps) t
mapClause f g (R.absurd-clause tel ps) = R.absurd-clause (f tel) (g ps)

recordIsoΣClauses : ΣFormat → List R.Clause
recordIsoΣClauses σ =
  funClauses (quote Iso.fun) Σ↔R ++
  funClauses (quote Iso.inv) R↔Σ ++
  pathClauses (quote Iso.rightInv) R↔Σ ++
  pathClauses (quote Iso.leftInv) Σ↔R
  where
  R↔Σ = ΣFormat→RecordAssoc σ
  Σ↔R = flipRecordAssoc R↔Σ

  funClauses : R.Name → RecordAssoc → List R.Clause
  funClauses name al =
    List.map
      (mapClause
        (("_" , varg R.unknown) ∷_)
        (λ ps → R.proj name v∷ R.var 0 v∷ ps))
      (convertClauses al (v 0))

  pathClauses : R.Name → RecordAssoc → List R.Clause
  pathClauses name al =
    List.map
      (mapClause
        (λ vs → ("_" , varg R.unknown) ∷ ("_" , varg R.unknown) ∷ vs)
        (λ ps → R.proj name v∷ R.var 1 v∷ R.var 0 v∷ ps))
      (convertClauses (fstIdRecordAssoc al) (v 1))

recordIsoΣTerm : ΣFormat → R.Term
recordIsoΣTerm σ = R.pat-lam (recordIsoΣClauses σ) []

-- with a provided ΣFormat for the record
declareRecordIsoΣ' : R.Name → ΣFormat → R.Name → R.TC Unit
declareRecordIsoΣ' idName σ recordName =
  let σTy = ΣFormat→Ty σ in
  recordName→isoTy recordName σTy >>= λ isoTy →
  R.declareDef (varg idName) isoTy >>
  R.defineFun idName (recordIsoΣClauses σ)

-- using the right-associated Σ given by the record fields
declareRecordIsoΣ : R.Name → R.Name → R.TC Unit
declareRecordIsoΣ idName recordName =
  R.getDefinition recordName >>= λ where
  (R.record-type _ fs) →
    let σ = List→ΣFormat (List.map (λ {(R.arg _ n) → n}) fs) in
    declareRecordIsoΣ' idName σ recordName
  _ →
    R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr recordName ∷ [])

private
  module Example where
    variable
      ℓ ℓ' : Level
      A : Type ℓ
      B : A → Type ℓ'

    record Example0 {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
      no-eta-equality -- works with or without eta equality
      field
        cool : A
        fun : A
        wow : B cool

    -- Declares a function `Example0IsoΣ` that gives an isomorphism between the record type and a
    -- right-associated nested Σ-type (with the parameters to Example0 as implict arguments).
    unquoteDecl Example0IsoΣ = declareRecordIsoΣ Example0IsoΣ (quote Example0)

    -- `Example0IsoΣ` has the type we expect
    test0 : Iso (Example0 B) (Σ[ a ∈ A ] (Σ[ _ ∈ A ] B a))
    test0 = Example0IsoΣ

    -- A record with no fields is isomorphic to Unit

    record Example1 : Type where

    unquoteDecl Example1IsoΣ = declareRecordIsoΣ Example1IsoΣ (quote Example1)

    test1 : Iso Example1 Unit
    test1 = Example1IsoΣ
