{-

Generate univalent reflexive graph characterizations for record types from
characterizations of the field types using reflection.

See end of file for an example.

-}
{-# OPTIONS --no-exact-split #-}
module Cubical.Displayed.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.List as List
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Maybe as Maybe

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties
open import Cubical.Displayed.Prop
open import Cubical.Displayed.Sigma
open import Cubical.Displayed.Unit
open import Cubical.Displayed.Universe
open import Cubical.Displayed.Auto

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base
import Cubical.Reflection.RecordEquiv as RE

{-
  `DUAFields`
  A collection of DURG characterizations for fields of a record is described by an element of this inductive
  family. If you just want to see how to use it, have a look at the end of the file first.

  An element of `DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅` describes a mapping
  - from a structure `R : A → Type _` and notion of structured equivalence `_≅R⟨_⟩_`,
    which are meant to be defined as parameterized record types,
  - to a DURG `𝒮ᴰ-S`,
    the underlying structure of which will be an iterated Σ-type,
  - via projections `πS` and `πS≅`.

  `𝒮-A`, `R`, and `_≅R⟨_⟩_` are parameters, while `πS`, `𝒮ᴰ-S`, and `πS≅` are indices;
  the user builds up the Σ-type representation of the record using the DUAFields constructors.

  A DUAFields representation is _total_ when the projections `πS` and `πS≅` are equivalences, in which case we
  obtain a DURG on `R` with `_≅R⟨_⟩_` as the notion of structured equivalence---see `𝒮ᴰ-Fields` below.

  When `R`, and `_≅R⟨_⟩_` are defined by record types, we can use reflection to automatically generate proofs
  `πS` and `πS≅` are equivalences---see `𝒮ᴰ-Record` below.

-}
data DUAFields {ℓA ℓ≅A ℓR ℓ≅R} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  (R : A → Type ℓR) (_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
  : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    (πS : ∀ {a} → R a → S a) (𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S)
    (πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r'))
    → Typeω
  where

  -- `fields:`
  -- Base case, no fields yet recorded in `𝒮ᴰ-S`.
  fields: : DUAFields 𝒮-A R _≅R⟨_⟩_ (λ _ → tt) (𝒮ᴰ-Unit 𝒮-A) (λ _ → tt)

  -- `… data[ πF ∣ 𝒮ᴰ-F ∣ πF≅ ]`
  -- Add a new field with a DURG. `πF` should be the name of the field in the structure record `R` and `πF≅`
  -- the name of the corresponding field in the equivalence record `_≅R⟨_⟩_`, while `𝒮ᴰ-F` is a DURG for the
  -- field's type over `𝒮-A`. Data fields that depend on previous fields of the record are not currently
  -- supported.
  _data[_∣_∣_] : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → ∀ {ℓF ℓ≅F} {F : A → Type ℓF}
    (πF : ∀ {a} → (r : R a) → F a)
    (𝒮ᴰ-F : DUARel 𝒮-A F ℓ≅F)
    (πF≅ : ∀ {a} {r : R a} {e} {r' : R a} (p : r ≅R⟨ e ⟩ r') → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-F (πF r) e (πF r'))
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (𝒮ᴰ-S ×𝒮ᴰ 𝒮ᴰ-F) (λ p → πS≅ p , πF≅ p)

  -- `… prop[ πF ∣ propF ]`
  -- Add a new propositional field. `πF` should be the name of the field in the structure record `R`, while
  -- propF is a proof that this field is a proposition.
  _prop[_∣_] : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → ∀ {ℓF} {F : (a : A) → S a → Type ℓF}
    (πF : ∀ {a} → (r : R a) → F a (πS r))
    (propF : ∀ a s → isProp (F a s))
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (𝒮ᴰ-subtype 𝒮ᴰ-S propF) (λ p → πS≅ p)

module _ {ℓA ℓ≅A} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {ℓR ℓ≅R} {R : A → Type ℓR} (_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
  {ℓS ℓ≅S} {S : A → Type ℓS}
  {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
  {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
  (fs : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-S

  𝒮ᴰ-Fields :
    (e : ∀ a → Iso (R a) (S a))
    (e≅ : ∀ a a' (r : R a) p (r' : R a') → Iso (r ≅R⟨ p ⟩ r') ((e a .Iso.fun r ≅ᴰ⟨ p ⟩ e a' .Iso.fun r')))
    → DUARel 𝒮-A R ℓ≅R
  DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Fields e e≅) r p r' = r ≅R⟨ p ⟩ r'
  DUARel.uaᴰ (𝒮ᴰ-Fields e e≅) r p r' =
    isoToEquiv
      (compIso
        (e≅ _ _ r p r')
        (compIso
          (equivToIso (uaᴰ (e _ .Iso.fun r) p (e _ .Iso.fun r')))
          (invIso (congPathIso λ i → isoToEquiv (e _)))))

module DisplayedRecordMacro where

  -- Extract a name from a term
  findName : R.Term → R.TC R.Name
  findName t =
    Maybe.rec
      (R.typeError (R.strErr "Not a name: " ∷ R.termErr t ∷ []))
      (λ s → s)
      (go t)
    where
    go : R.Term → Maybe (R.TC R.Name)
    go (R.meta x _) = just (R.blockOnMeta x)
    go (R.def name _) = just (R.returnTC name)
    go (R.lam _ (R.abs _ t)) = go t
    go t = nothing

  -- ℓA ℓ≅A ℓR ℓ≅R A 𝒮-A R _≅R⟨_⟩_
  pattern family∷ hole = _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ hole

  -- ℓS ℓ≅S S πS 𝒮ᴰ-S πS≅
  pattern indices∷ hole = _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ hole

  {-
    Takes a reflected DUAFields term as input and collects lists of structure field names and equivalence
    field names. (These are returned in reverse order.
  -}
  parseFields : R.Term → R.TC (List R.Name × List R.Name)
  parseFields (R.con (quote fields:) _) = R.returnTC ([] , [])
  parseFields (R.con (quote _data[_∣_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ ℓ≅F h∷ F h∷ πF v∷ 𝒮ᴰ-F v∷ πF≅ v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    findName πF≅ >>= λ f≅ →
    R.returnTC (f ∷ fs , f≅ ∷ f≅s)
  parseFields (R.con (quote _prop[_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ F h∷ πF v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    R.returnTC (f ∷ fs , f≅s)
  parseFields (R.meta x _) = R.blockOnMeta x
  parseFields t = R.typeError (R.strErr "Malformed specification: " ∷ R.termErr t ∷ [])

  {-
    Given a list of record field names (in reverse order), generates a ΣFormat (in the sense of
    Cubical.Reflection.RecordEquiv) associating the record fields with the fields of a left-associated
    iterated Σ-type
  -}
  List→LeftAssoc : List R.Name → RE.ΣFormat
  List→LeftAssoc [] = RE.unit
  List→LeftAssoc (x ∷ xs) = List→LeftAssoc xs RE., RE.leaf x

  module _ {ℓA ℓ≅A} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
    {ℓR ℓ≅R} {R : A → Type ℓR} (≅R : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
    {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → ≅R r e r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    where

    {-
      "𝒮ᴰ-Record ... : DUARel 𝒮-A R ℓ≅R"
      Requires that `R` and `_≅R⟨_⟩_` are defined by records and `πS` and `πS≅` are equivalences.
      The proofs of equivalence are generated using Cubical.Reflection.RecordEquiv and then
      `𝒮ᴰ-Fields` is applied.
    -}
    𝒮ᴰ-Record : DUAFields 𝒮-A R ≅R πS 𝒮ᴰ-S πS≅ → R.Term → R.TC Unit
    𝒮ᴰ-Record fs hole =
      R.quoteTC (DUARel 𝒮-A R ℓ≅R) >>= R.checkType hole >>= λ hole →
      R.quoteωTC fs >>= λ `fs` →
      parseFields `fs` >>= λ (fields , ≅fields) →
      R.freshName "fieldsIso" >>= λ fieldsIso →
      R.freshName "≅fieldsIso" >>= λ ≅fieldsIso →
      R.quoteTC R >>= R.normalise >>= λ `R` →
      R.quoteTC {A = {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R} ≅R >>= R.normalise >>= λ `≅R` →
      findName `R` >>= RE.declareRecordIsoΣ' fieldsIso (List→LeftAssoc fields) >>
      findName `≅R` >>= RE.declareRecordIsoΣ' ≅fieldsIso (List→LeftAssoc ≅fields) >>
      R.unify hole
        (R.def (quote 𝒮ᴰ-Fields)
          (`≅R` v∷ `fs` v∷
            vlam "_" (R.def fieldsIso []) v∷
            vlam "a" (vlam "a'" (vlam "r" (vlam "p" (vlam "r'" (R.def ≅fieldsIso []))))) v∷
            []))

macro
  𝒮ᴰ-Record = DisplayedRecordMacro.𝒮ᴰ-Record

-- Example

private
  module Example where

    record Example (A : Type) : Type where
      no-eta-equality -- works with or without eta equality
      field
        dog : A → A → A
        cat : A → A → A
        mouse : Unit

    open Example

    record ExampleEquiv {A B : Type} (x : Example A) (e : A ≃ B) (y : Example B) : Type where
      no-eta-equality -- works with or without eta equality
      field
        dogEq : ∀ a a' → e .fst (x .dog a a') ≡ y .dog (e .fst a) (e .fst a')
        catEq : ∀ a a' → e .fst (x .cat a a') ≡ y .cat (e .fst a) (e .fst a')

    open ExampleEquiv

    example : DUARel (𝒮-Univ ℓ-zero) Example ℓ-zero
    example =
      𝒮ᴰ-Record (𝒮-Univ ℓ-zero) ExampleEquiv
        (fields:
          data[ dog ∣ autoDUARel _ _ ∣ dogEq ]
          data[ cat ∣ autoDUARel _ _ ∣ catEq ]
          prop[ mouse ∣ (λ _ _ → isPropUnit) ])
