{-

  Reflection-based tools for converting between iterated record types, particularly between
  record types and iterated Σ-types.

  The main functions are `declareRecordIsoΣ` and `declareRecordIsoΣ`. See end of file for
  example usage.

-}
{-# OPTIONS --no-exact-split #-}
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

-- Intended to represent a (possibly nested) field of a record type. For example, the list
-- "snd" ∷ fst" ∷ []` would represent the field `.fst .snd`.
Projections = List R.Name

-- Intended to represent a bijection between two record types by an association list
-- between (possibly nested) fields of the one and the other. The `Maybe`s are included to
-- allow dropping fields of Unit (or other definitionally unique) type.
--
-- For example, the correspondence
--
--   .fst .fst ↔ .snd
--   .fst .snd ↔ .fst
--   .snd ↔ ∅
--
-- between (A × B) × Unit and B × A would be represented by the list
--
--   [ (just ["fst"; "fst"] , just ["snd"])
--   ; (just ["snd"; "fst"] , just ["fst"])
--   ; (just ["snd"] , nothing)
--   ]
RecordAssoc = List (Maybe Projections × Maybe Projections)

-- Describes a correspondence between a non-nested record and an iterated Σ-type; more
-- convenient to work with than RecordAssoc in this special case, which is the most common
-- one. For example,
--
--   leaf "a" , (leaf "b" , leaf "c")
--
-- describes the following RecordAssoc:
--
--   .fst ↔ .a
--   .snd .fst ↔ .b
--   .snd .snd ↔ .c
--
-- The `unit` constructor is the correspondence between Unit ("nullary Σ") and the empty
-- record.
data ΣFormat : Type where
  leaf : R.Name → ΣFormat
  _,_ : ΣFormat → ΣFormat → ΣFormat
  unit : ΣFormat

infixr 4 _,_

-- Inverse of a correspondence between record types
flipRecordAssoc : RecordAssoc → RecordAssoc
flipRecordAssoc = List.map λ {p .fst → p .snd; p .snd → p .fst}

-- The identity correspondence on the domain of a given correspondence
fstIdRecordAssoc : RecordAssoc → RecordAssoc
fstIdRecordAssoc = List.map λ {p .fst → p .fst; p .snd → p .fst}

-- Constructs a ΣFormat from a list of fields meant to represent a right-associated Σ-type
List→ΣFormat : List R.Name → ΣFormat
List→ΣFormat [] = unit
List→ΣFormat (x ∷ []) = leaf x
List→ΣFormat (x ∷ y ∷ xs) = leaf x , List→ΣFormat (y ∷ xs)

-- Converts a ΣFormat to an association list as described above.
-- The domain of the RecordAssoc is the record type, the codomain is the Σ-type.
ΣFormat→RecordAssoc : ΣFormat → RecordAssoc
ΣFormat→RecordAssoc = go []
  where
  go : List R.Name → ΣFormat → RecordAssoc
  go prefix unit = [ nothing , just prefix ]
  go prefix (leaf fieldName) = [ just [ fieldName ] , just prefix ]
  go prefix (sig₁ , sig₂) =
    go (quote fst ∷ prefix) sig₁ ++ go (quote snd ∷ prefix) sig₂

-- Define a reflected type with the shape of the Σ-type described by a ΣFormat.
-- The type arguments to the Σ are filled in with unsolved metavariables.
ΣFormat→Ty : ΣFormat → R.Type
ΣFormat→Ty unit = R.def (quote Unit) []
ΣFormat→Ty (leaf _) = R.unknown
ΣFormat→Ty (sig₁ , sig₂) =
  R.def (quote Σ) (ΣFormat→Ty sig₁ v∷ R.lam R.visible (R.abs "_" (ΣFormat→Ty sig₂)) v∷ [])

-- Given the name of a record type and a ΣFormat describing an isomorphism between this
-- type and a Σ-type, constructs a reflected type of isomorphisms between the record and
-- Σ-type. If the record type takes parameters or indices, then the result is a similarly
-- parameterized family of isomorphisms. All parameters to the isomorphism are made
-- implicit.
recordName→isoTy : R.Name → ΣFormat → R.TC R.Term
recordName→isoTy name σ =
  R.inferType (R.def name []) >>= R.normalise >>= go []
  where
  σTy = ΣFormat→Ty σ

  -- Recurses on the type of the named record type
  go : List R.ArgInfo → R.Type → R.TC R.Term
  go acc (R.pi (R.arg i argTy) (R.abs s ty)) =
    -- If the record takes a parameter, the returned isomorphism is likewise parameterized
    liftTC (λ t → R.pi (R.arg i' argTy) (R.abs s t)) (go (i ∷ acc) ty)
    where
    i' = R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)
  go acc (R.agda-sort _) =
    -- Main case, constructs isomorphism type
    R.returnTC (R.def (quote Iso) (R.def name (makeArgs 0 [] acc) v∷ σTy v∷ []))
    where
    makeArgs : ℕ → List (R.Arg R.Term) → List R.ArgInfo → List (R.Arg R.Term)
    makeArgs n acc [] = acc
    makeArgs n acc (i ∷ infos) = makeArgs (suc n) (R.arg i (v n) ∷ acc) infos
  go _ _ = R.typeError (R.strErr "Not a record type name: " ∷ R.nameErr name ∷ [])

-- Given an association list `al` defining a correspondence between record types (say R
-- and S) and a `term` belonging to R, produces clauses defining an element of S, with
-- each field of S instantiated with a field of `term` according to `al`.  For example,
-- the correspondence
--
--   .fst ↔ .a
--   .snd .fst ↔ .b
--   .snd .snd ↔ ∅
--   ∅ ↔ .c
--
-- would produce the clauses
--
-- ... .a = term .fst
-- ... .b = term .snd
-- ... .c = _
--
-- Here the type of .c should have a definitionally unique element, so
-- we can safely fill it with an unsolved metavariable.
convertClauses : RecordAssoc → R.Term → List R.Clause
convertClauses al term = fixIfEmpty (List.filterMap makeClause al)
  where
  makeClause : Maybe Projections × Maybe Projections → Maybe R.Clause
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

  -- If there end up being zero clauses, then S should be a type with a definitionally
  -- unique element, so we return a single clause defined by an unsolved metavariable.
  fixIfEmpty : List R.Clause → List R.Clause
  fixIfEmpty [] = [ R.clause [] [] R.unknown ]
  fixIfEmpty (c ∷ cs) = c ∷ cs

-- Apply functions to the telescope and pattern parts of a clause
mapClause :
  (List (String × R.Arg R.Type) → List (String × R.Arg R.Type))
  → (List (R.Arg R.Pattern) → List (R.Arg R.Pattern))
  → (R.Clause → R.Clause)
mapClause f g (R.clause tel ps t) = R.clause (f tel) (g ps) t
mapClause f g (R.absurd-clause tel ps) = R.absurd-clause (f tel) (g ps)

-- Given a ΣFormat `σ` relating a record type R and Σ-type S, returns
-- a list of clauses defining an isomorphism between R and S.
recordIsoΣClauses : ΣFormat → List R.Clause
recordIsoΣClauses σ =
  funClauses (quote Iso.fun) R↔Σ ++
  funClauses (quote Iso.inv) Σ↔R ++
  -- Clauses for the forward and backward inverse conditions
  pathClauses (quote Iso.rightInv) Σ↔R ++
  pathClauses (quote Iso.leftInv) R↔Σ
  where
  R↔Σ = ΣFormat→RecordAssoc σ
  Σ↔R = flipRecordAssoc R↔Σ

  -- Given an association list `al` for a correspondence R ↔ S, produces the list of
  -- clauses defining a function from R to S.
  -- The `prefix` will be either `Iso.fun` or `Iso.inv`.
  funClauses : R.Name → RecordAssoc → List R.Clause
  funClauses prefix al =
    List.map
      -- Introduce a new variable of the input type
      (mapClause
        (("_" , varg R.unknown) ∷_)
        (λ ps → R.proj prefix v∷ R.var 0 v∷ ps))
      -- Each clause is a projection applied to the input variable
      (convertClauses al (v 0))

  -- Given an association list `al` for a correspondence R ↔ S, produces the list of
  -- clauses defining the inverse path for the round-trip R → S → R.
  -- The `prefix` will be either `Iso.rightInv` or `Iso.leftInv`.
  pathClauses : R.Name → RecordAssoc → List R.Clause
  pathClauses prefix al =
    List.map
      -- Introduce a variable of the input type and an interval variable
      (mapClause
        (λ vs → ("_" , varg R.unknown) ∷ ("_" , varg (R.def (quote I) [])) ∷ vs)
        (λ ps → R.proj prefix v∷ R.var 1 v∷ R.var 0 v∷ ps))
      -- The inverse condition at each clause holds by reflexivity
      (convertClauses (fstIdRecordAssoc al) (v 1))

------------------------------------------------------------------------------------------
-- Main functions
------------------------------------------------------------------------------------------

-- Given a ΣFormat describing a correspondence between a record and nested Σ-type,
-- constructs an isomorphism between them as a term.
--
-- Because this term is a large pattern-matching lambda, it is better to use the
-- declare* functions below, which declare a named function.
recordIsoΣTerm : ΣFormat → R.Term
recordIsoΣTerm σ = R.pat-lam (recordIsoΣClauses σ) []

-- Given a name `idName`, a ΣFormat `σ` describing a correspondence between a record and
-- nested Σ-type, and the name `recordName` of the record type, declares a function with
-- name `idName` defining an isomorphism between the two types (with implicit parameters
-- corresponding to the parameters and indices of the record type).
declareRecordIsoΣ' : R.Name → ΣFormat → R.Name → R.TC Unit
declareRecordIsoΣ' idName σ recordName =
  recordName→isoTy recordName σ >>= λ isoTy →
  R.declareDef (varg idName) isoTy >>
  R.defineFun idName (recordIsoΣClauses σ)

-- Given a name `idName` and the name `recordName` of a record type, declares a function
-- with name `idName` defining an isomorphism from the record type to the right-associated
-- Σ-type corresponding to its list of fields (with implicit parameters corresponding to
-- the parameters and indices of the record type).
declareRecordIsoΣ : R.Name → R.Name → R.TC Unit
declareRecordIsoΣ idName recordName =
  R.getDefinition recordName >>= λ where
  (R.record-type _ fs) →
    let σ = List→ΣFormat (List.map (λ {(R.arg _ n) → n}) fs) in
    declareRecordIsoΣ' idName σ recordName
  _ →
    R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr recordName ∷ [])


------------------------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------------------------

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
