{-

Tooling to generate univalent reflexive graph characterizations for record types

-}
{-# OPTIONS --cubical --no-exact-split --no-import-sorts #-} -- --safe #-}
module Cubical.Displayed.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.List as List
open import Cubical.Data.Unit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base
import Cubical.Reflection.RecordEquiv as RE

data DUAFields {ℓA ℓ≅A ℓR ℓ≅R} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  (R : A → Type ℓR) (_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
  : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    (πS : ∀ {a} → R a → S a) (𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S)
    (πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r'))
    → Typeω
  where

  fields: : DUAFields 𝒮-A R _≅R⟨_⟩_ (λ _ → tt) (𝒮ᴰ-Unit 𝒮-A) (λ _ → tt)

  _basic[_∣_∣_] : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → ∀ {ℓF ℓ≅F} {F : A → Type ℓF}
    (πF : ∀ {a} → (r : R a) → F a)
    (𝒮ᴰ-F : DUARel 𝒮-A F ℓ≅F)
    (πF≅ : ∀ {a} {r : R a} {e} {r' : R a} (p : r ≅R⟨ e ⟩ r') → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-F (πF r) e (πF r'))
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (𝒮ᴰ-S ×𝒮ᴰ 𝒮ᴰ-F) (λ p → πS≅ p , πF≅ p)

  _dep[_∣_∣_] : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → ∀ {ℓF ℓ≅F} {F : (a : A) → S a → Type ℓF}
    (πF : ∀ {a} → (r : R a) → F a (πS r))
    (𝒮ᴰ-F : DUARel (∫ 𝒮ᴰ-S) (uncurry F) ℓ≅F)
    (πF≅ : ∀ {a} {r : R a} {e} {r' : R a} (p : r ≅R⟨ e ⟩ r') → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-F (πF r) (e , πS≅ p) (πF r'))
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (splitTotal-𝒮ᴰ 𝒮-A 𝒮ᴰ-S 𝒮ᴰ-F) (λ p → πS≅ p , πF≅ p)

  _prop[_∣_] : ∀ {ℓS ℓ≅S} {S : A → Type ℓS}
    {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
    {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
    → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → ∀ {ℓF} {F : (a : A) → S a → Type ℓF}
    (πF : ∀ {a} → (r : R a) → F a (πS r))
    (propF : ∀ a s → isProp (F a s))
    → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ r → πS r , πF r) (𝒮ᴰ-Axioms 𝒮-A 𝒮ᴰ-S F propF) (λ p → πS≅ p)

fields[_∣_∣_]: : ∀ {ℓA ℓ≅A ℓR ℓ≅R} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  (R : A → Type ℓR) (_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R)
  → DUAFields 𝒮-A R _≅R⟨_⟩_ (λ _ → tt) (𝒮ᴰ-Unit 𝒮-A) (λ _ → tt)
fields[ _ ∣ _ ∣ _ ]: = fields:

private
  variable
    ℓA ℓ≅A ℓR ℓ≅R ℓF ℓ≅F ℓS ℓ≅S ℓP : Level

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {R : A → Type ℓR} {_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R}
  {ℓS ℓ≅S} {S : A → Type ℓS} {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
  {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-S

  𝒮ᴰ-R : (fs : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅)
    (e : ∀ {a} → S a ≃ R a)
    (e≅ : ∀ {a a'} (r : R a) p (r' : R a') → r ≅R⟨ p ⟩ r' ≃ (invEq e r ≅ᴰ⟨ p ⟩ invEq e r'))
    → DUARel 𝒮-A R ℓ≅R
  DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-R _ e e≅) r p r' = r ≅R⟨ p ⟩ r'
  DUARel.uaᴰ (𝒮ᴰ-R _ e e≅) r p r' =
    compEquiv
      (e≅ r p r')
      (compEquiv
        (uaᴰ (invEq e r) p (invEq e r'))
        (invEquiv (congPathEquiv λ i → invEquiv e)))

module Internal where

  findName : R.Term → R.TC R.Name
  findName (R.def name _) = R.returnTC name
  findName (R.lam R.hidden (R.abs _ t)) = findName t
  findName t = R.typeError (R.strErr "Not a name + spine: " ∷ R.termErr t ∷ [])

  -- ℓA ℓ≅A ℓR ℓ≅R A 𝒮-A R _≅R⟨_⟩_
  pattern family∷ hole = _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ hole

  -- ℓS ℓ≅S S πS 𝒮ᴰ-S πS≅
  pattern indices∷ hole = _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ hole

  parseFields : R.Term → R.TC (List R.Name × List R.Name)
  parseFields (R.con (quote fields:) _) = R.returnTC ([] , [])
  parseFields (R.con (quote _basic[_∣_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ ℓ≅F h∷ F h∷ πF v∷ 𝒮ᴰ-F v∷ πF≅ v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    findName πF≅ >>= λ f≅ →
    R.returnTC (f ∷ fs , f≅ ∷ f≅s)
  parseFields (R.con (quote _dep[_∣_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ ℓ≅F h∷ F h∷ πF v∷ 𝒮ᴰ-F v∷ πF≅ v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    findName πF≅ >>= λ f≅ →
    R.returnTC (fs ∷ʳ f , f≅s ∷ʳ f≅)
  parseFields (R.con (quote _prop[_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ F h∷ πF v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    R.returnTC (f ∷ fs , f≅s)
  parseFields t = R.typeError (R.strErr "Malformed specification (1): " ∷ R.termErr t ∷ [])

  List→LeftAssoc : List R.Name → RE.Assoc
  List→LeftAssoc xs = RE.Internal.ΣFormat→Assoc (go xs)
    where
    go : List R.Name → RE.ΣFormat
    go [] = RE.unit
    go (x ∷ xs) = go xs RE., RE.leaf x

  frame : ∀ {ℓA ℓ≅A} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
    {ℓR ℓ≅R} {R : A → Type ℓR} {≅R : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R}
    {ℓS ℓ≅S} {S : A → Type ℓS} (𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S)
    (er : ∀ {a} → S a ≃ R a)
    (el : ∀ {a a'} (r : R a) p (r' : R a') → ≅R r p r' ≃ DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (invEq er r) p (invEq er r'))
    → DUARel 𝒮-A R ℓ≅R
  DUARel._≅ᴰ⟨_⟩_ (frame {≅R = ≅R} 𝒮ᴰ-S er el) = ≅R
  DUARel.uaᴰ (frame 𝒮ᴰ-S er el) r p r' =
    compEquiv
      (el r p r')
      (compEquiv
        (DUARel.uaᴰ 𝒮ᴰ-S (invEq er r) p (invEq er r'))
        (invEquiv (congPathEquiv λ i → invEquiv er)))

  𝒮ᴰ-RecordMacro : R.Term → R.Term → R.TC Unit
  𝒮ᴰ-RecordMacro spec hole =
    R.normalise spec >>= parseFields >>= λ (fs , f≅s) →
    wit3 (newMeta R.unknown) >>= λ f≅sEquiv →
    wit (newMeta R.unknown) >>= λ fsEquiv →
    R.unify hole
      (R.def (quote 𝒮ᴰ-R)
        (spec v∷ hlam "_" fsEquiv v∷ hlam "a" (hlam "a'" (vlam "r" (vlam "p" (vlam "r'" f≅sEquiv)))) v∷ [])) >>
    wit (I.equivMacro (List→LeftAssoc fs) fsEquiv) >>
    wit3 (I.equivMacro (I.flipAssoc (List→LeftAssoc f≅s)) f≅sEquiv)
    where
    module I = RE.Internal

    wit : ∀ {A : Type} → R.TC A → R.TC A
    wit = R.extendContext (varg R.unknown)

    hwit : ∀ {A : Type} → R.TC A → R.TC A
    hwit = R.extendContext (harg R.unknown)

    wit3 : ∀ {A : Type} → R.TC A → R.TC A
    wit3 t = wit (wit (wit (hwit (hwit t))))

macro
  𝒮ᴰ-Record : R.Term → R.Term → R.TC Unit
  𝒮ᴰ-Record = Internal.𝒮ᴰ-RecordMacro

module Example where

  record Example (A : Type) : Type where
    field
      dog : A
      cat : Unit

  record ExampleEquiv {A B : Type} (x : Example A) (e : A ≃ B) (x' : Example B) : Type where
    field
      dogEq : e .fst (Example.dog x) ≡ Example.dog x'

  example : DUARel (𝒮-univ ℓ-zero) Example ℓ-zero
  example =
    𝒮ᴰ-Record
      (fields[ 𝒮-univ ℓ-zero ∣ Example ∣ ExampleEquiv ]:
        basic[ Example.dog ∣ 𝒮ᴰ-element ℓ-zero ∣ ExampleEquiv.dogEq ]
        prop[ Example.cat ∣ (λ _ _ → isPropUnit) ])
