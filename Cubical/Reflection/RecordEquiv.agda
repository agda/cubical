{-

  Reflection-based tools for converting between iterated record types, particularly between
  record types and iterated Σ-types. Currently requires eta equality.

  See end of file for examples.

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Reflection.RecordEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

Projections = List R.Name

-- Describes a correspondence between two iterated record types
Assoc = List (Projections × Projections)

-- Describes a correspondence between a record type and an iterated Σ-types;
-- more convenient than Assoc for this special case
data ΣFormat : Type where
  leaf : R.Name → ΣFormat
  _,_ : ΣFormat → ΣFormat → ΣFormat

infixr 4 _,_

module Internal where

  flipAssoc : Assoc → Assoc
  flipAssoc = List.map λ {p .fst → p .snd; p .snd → p .fst}

  list→ΣFormat : List R.Name → Maybe ΣFormat
  list→ΣFormat [] = nothing
  list→ΣFormat (x ∷ []) = just (leaf x)
  list→ΣFormat (x ∷ y ∷ xs) = map-Maybe (leaf x ,_) (list→ΣFormat (y ∷ xs))

  recordName→ΣFormat : R.Name → R.TC (Maybe ΣFormat)
  recordName→ΣFormat name = R.getDefinition name >>= go
    where
    go : R.Definition → R.TC (Maybe ΣFormat)
    go (R.record-type c fs) = R.returnTC (list→ΣFormat (List.map (λ {(R.arg _ n) → n}) fs))
    go _ = R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr name ∷ [])

  ΣFormat→Assoc : ΣFormat → Assoc
  ΣFormat→Assoc = go []
    where
    go : List R.Name → ΣFormat → Assoc
    go prefix (leaf fieldName) = [ prefix , [ fieldName ] ]
    go prefix (sig₁ , sig₂) =
      go (quote fst ∷ prefix) sig₁ ++ go (quote snd ∷ prefix) sig₂

  MaybeΣFormat→Assoc : Maybe ΣFormat → Assoc
  MaybeΣFormat→Assoc nothing = [ [] , [] ]
  MaybeΣFormat→Assoc (just sig) = ΣFormat→Assoc sig
  
  convertTerm : Assoc → R.Term → R.Term
  convertTerm al term = R.pat-lam (List.map makeClause al) []
    where
    makeClause : Projections × Projections → R.Clause
    makeClause (projl , projr) =
      R.clause [] (goPat [] projr) (goTm projl)
      where
      goPat : List (R.Arg R.Pattern) → List R.Name → List (R.Arg R.Pattern)
      goPat acc [] = acc
      goPat acc (π ∷ projs) = goPat (varg (R.proj π) ∷ acc) projs

      goTm : List R.Name → R.Term
      goTm [] = term
      goTm (π ∷ projs) = R.def π [ varg (goTm projs) ]

  convertFun : Assoc → R.Term
  convertFun al = vlam "ρ" (convertTerm al (v 0))

  convertMacro : Assoc → R.Term → R.TC Unit
  convertMacro al hole = R.unify hole (convertFun al)

  equivMacro : Assoc → R.Term → R.TC Unit
  equivMacro al hole =
    newMeta R.unknown >>= λ hole₁ →
    newMeta R.unknown >>= λ hole₂ →
    let
      iso : R.Term
      iso =
        R.pat-lam
          ( R.clause [] [ varg (R.proj (quote Iso.fun)) ] hole₁
          ∷ R.clause [] [ varg (R.proj (quote Iso.inv)) ] hole₂
          ∷ R.clause [] [ varg (R.proj (quote Iso.rightInv)) ] (vlam "_" (R.def (quote refl) []))
          ∷ R.clause [] [ varg (R.proj (quote Iso.leftInv)) ] (vlam "_" (R.def (quote refl) []))
          ∷ []
          )
          []
    in
    R.unify hole (R.def (quote isoToEquiv) [ varg iso ]) >>
    convertMacro al hole₁ >>
    convertMacro (flipAssoc al) hole₂

open Internal

macro
  -- ΣFormat → <Σ-Type> ≃ <RecordType>
  Σ≃Record : ΣFormat → R.Term → R.TC Unit
  Σ≃Record sig = equivMacro (ΣFormat→Assoc sig)

  -- ΣFormat → <RecordType> ≃ <Σ-Type>
  Record≃Σ : ΣFormat → R.Term → R.TC Unit
  Record≃Σ sig = equivMacro (flipAssoc (ΣFormat→Assoc sig))

  -- <RecordTypeName> → <Σ-Type> ≃ <RecordType>
  FlatΣ≃Record : R.Name → R.Term → R.TC Unit
  FlatΣ≃Record name hole =
    recordName→ΣFormat name >>= λ sig →
    equivMacro (MaybeΣFormat→Assoc sig) hole

  -- <RecordTypeName> → <RecordType> ≃ <Σ-Type>
  Record≃FlatΣ : R.Name → R.Term → R.TC Unit
  Record≃FlatΣ name hole =
    recordName→ΣFormat name >>= λ sig →
    equivMacro (flipAssoc (MaybeΣFormat→Assoc sig)) hole

  -- ΣFormat → <RecordType₁> ≃ <RecordType₂>
  Record≃Record : Assoc → R.Term → R.TC Unit
  Record≃Record = equivMacro


module Example where

  private
    variable
      ℓ ℓ' : Level
      A : Type ℓ
      B : A → Type ℓ'

  record Example {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      cool : A
      fun : A
      wow : B cool

  open Example

  {-
    Example: Equivalence between a Σ-type and record type using FlatΣ≃Record
  -}

  Example0 : (Σ[ a ∈ A ] Σ[ a' ∈ A ] B a) ≃ Example B
  Example0 = FlatΣ≃Record Example

  Example0' : Example B ≃ (Σ[ a ∈ A ] Σ[ a' ∈ A ] B a)
  Example0' = Record≃FlatΣ Example

  Example0'' : Unit ≃ Unit -- any record with no fields is equivalent to unit
  Example0'' = FlatΣ≃Record Unit

  {-
    Example: Equivalence between an arbitrarily arrange Σ-type and record type using Σ≃Record
  -}

  Example1 : (Σ[ p ∈ A × A ] B (p .snd)) ≃ Example B
  Example1 =
    Σ≃Record ((leaf (quote fun) , leaf (quote cool)) , leaf (quote wow))

  {-
    Example: Equivalence between arbitrary iterated record types (less convenient) using
    Record≃Record
  -}

  record Inner {A : Type ℓ} (B : A → Type ℓ') (a : A) : Type (ℓ-max ℓ ℓ') where
    field
      fun' : A
      wow' : B a

  record Outer {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      cool' : A
      inner : B cool'

  open Inner
  open Outer

  Example2 : Example B ≃ Outer (Inner B)
  Example2 =
    Record≃Record
      ( ([ quote cool ] , [ quote cool' ])
      ∷ ([ quote fun ] , (quote fun' ∷ quote inner ∷ []))
      ∷ ([ quote wow ] , (quote wow' ∷ quote inner ∷ []))
      ∷ []
      )
