{-

Generate univalent reflexive graph characterizations for record types from
characterizations of the field types using reflection.

See end of file for an example.

-}
{-# OPTIONS --cubical --no-exact-split --no-import-sorts --safe #-}
module Cubical.Displayed.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.List as List
open import Cubical.Data.Unit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties

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
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (𝒮ᴰ-Axioms 𝒮-A 𝒮ᴰ-S F propF) (λ p → πS≅ p)

{-
  Agda may have trouble inferring the notion of equivalence for the record, so we include it as an annotation
-}
fields[_]: : ∀ {ℓA ℓ≅A ℓR ℓ≅R} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {R : A → Type ℓR} (_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
  → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ _ → tt) (𝒮ᴰ-Unit 𝒮-A) (λ _ → tt)
fields[ _ ]: = fields:

module _ {ℓA ℓ≅A} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {ℓR ℓ≅R} {R : A → Type ℓR} {_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R}
  {ℓS ℓ≅S} {S : A → Type ℓS}
  {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
  {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
  (fs : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-S

  𝒮ᴰ-Fields : (e : ∀ {a} → S a ≃ R a)
    (e≅ : ∀ {a a'} (r : R a) p (r' : R a') → r ≅R⟨ p ⟩ r' ≃ (invEq e r ≅ᴰ⟨ p ⟩ invEq e r'))
    → DUARel 𝒮-A R ℓ≅R
  DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Fields e e≅) r p r' = r ≅R⟨ p ⟩ r'
  DUARel.uaᴰ (𝒮ᴰ-Fields e e≅) r p r' =
    compEquiv
      (e≅ r p r')
      (compEquiv
        (uaᴰ (invEq e r) p (invEq e r'))
        (invEquiv (congPathEquiv λ i → invEquiv e)))

module Macro where

  -- Extract a name from a term
  findName : R.Term → R.TC R.Name
  findName (R.def name _) = R.returnTC name
  findName (R.lam R.hidden (R.abs _ t)) = findName t
  findName t = R.typeError (R.strErr "Not a name: " ∷ R.termErr t ∷ [])

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
  parseFields t = R.typeError (R.strErr "Malformed specification (1): " ∷ R.termErr t ∷ [])

  {-
    Given a list of record field names (in reverse order), generates an association (in the sense of
    Cubical.Reflection.RecordEquiv) between the record fields and the fields of a left-associated iterated
    Σ-type
  -}
  List→LeftAssoc : List R.Name → RE.Assoc
  List→LeftAssoc xs = RE.Internal.ΣFormat→Assoc (go xs)
    where
    go : List R.Name → RE.ΣFormat
    go [] = RE.unit
    go (x ∷ xs) = go xs RE., RE.leaf x

  {-
    "𝒮ᴰ-Record : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅ → DUARel 𝒮-A R ℓ≅R"
    Requires that `R` and `_≅R⟨_⟩_` are defined by records and `πS` and `πS≅` are equivalences.
    The proofs of the latter are generated using Cubical.Reflection.RecordEquiv and then
    `𝒮ᴰ-Fields` is applied.
  -}
  𝒮ᴰ-Record : R.Term → R.Term → R.TC Unit
  𝒮ᴰ-Record spec hole =
    R.normalise spec >>= parseFields >>= λ (fields , ≅fields) →
    inFieldsContext (newMeta R.unknown) >>= λ fieldsEquiv →
    in≅FieldsContext (newMeta R.unknown) >>= λ ≅fieldsEquiv →
    R.unify hole
      (R.def (quote 𝒮ᴰ-Fields)
        (spec v∷
          hlam "_" fieldsEquiv v∷
          hlam "a" (hlam "a'" (vlam "r" (vlam "p" (vlam "r'" ≅fieldsEquiv)))) v∷
          [])) >>
    inFieldsContext (I.equivMacro (List→LeftAssoc fields) fieldsEquiv) >>
    in≅FieldsContext (I.equivMacro (I.flipAssoc (List→LeftAssoc ≅fields)) ≅fieldsEquiv)
    where
    module I = RE.Internal

    inFieldsContext : ∀ {A : Type} → R.TC A → R.TC A
    inFieldsContext = R.extendContext (varg R.unknown)

    in≅FieldsContext : ∀ {A : Type} → R.TC A → R.TC A
    in≅FieldsContext =
      extend*Context (R.unknown h∷ R.unknown h∷ R.unknown v∷ R.unknown v∷ R.unknown v∷ [])

macro
  -- "𝒮ᴰ-Record : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅ → DUARel 𝒮-A R ℓ≅R"
  -- Requires that `R` and `_≅R⟨_⟩_` are defined by records and `πS` and `πS≅` are equivalences.
  𝒮ᴰ-Record : R.Term → R.Term → R.TC Unit
  𝒮ᴰ-Record = Macro.𝒮ᴰ-Record

module Example where

  record Example (A : Type) : Type where
    field
      dog : A
      cat : A
      mouse : Unit

  record ExampleEquiv {A B : Type} (x : Example A) (e : A ≃ B) (x' : Example B) : Type where
    field
      dogEq : e .fst (Example.dog x) ≡ Example.dog x'
      catEq : e .fst (Example.cat x) ≡ Example.cat x'

  example : DUARel (𝒮-univ ℓ-zero) Example ℓ-zero
  example =
    𝒮ᴰ-Record
      (fields[ ExampleEquiv ]:
        data[ Example.dog ∣ 𝒮ᴰ-element ℓ-zero ∣ ExampleEquiv.dogEq ]
        data[ Example.cat ∣ 𝒮ᴰ-element ℓ-zero ∣ ExampleEquiv.catEq ]
        prop[ Example.mouse ∣ (λ _ _ → isPropUnit) ])
