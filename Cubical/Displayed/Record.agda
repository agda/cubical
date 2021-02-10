{-

Tooling to generate univalent reflexive graph characterizations for record types

-}
{-# OPTIONS --cubical --no-exact-split --no-import-sorts #-} -- --safe #-}
module Cubical.Displayed.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List as List
open import Cubical.Data.Vec as Vec
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Sum
open import Cubical.Structures.Auto

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base
import Cubical.Reflection.RecordEquiv as RE

postulate
  congEquivPathP⁻ : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
    (e : ∀ i → A i ≃ B i) {b₀ : B i0} {b₁ : B i1}
    → PathP A (invEq (e i0) b₀) (invEq (e i1) b₁) ≃ PathP B b₀ b₁
-- congEquivPathP⁻ {A = A} {B} e {b₀} {b₁} =
--   isoToEquiv is
--   where
--   is : Iso (PathP A (invEq (e i0) b₀) (invEq (e i1) b₁)) (PathP B b₀ b₁)
--   Iso.fun is p i =
--     hcomp
--       (λ j → λ
--         { (i = i0) → retEq (e i0) b₀ j
--         ; (i = i1) → retEq (e i1) b₁ j
--         })
--       (e i .fst (p i))
--   Iso.inv is q i = invEq (e i) (q i)
--   Iso.rightInv is q k i =
--     hcomp
--       (λ j → λ
--         { (i = i0) → retEq (e i0) b₀ (j ∨ k)
--         ; (i = i1) → retEq (e i1) b₁ (j ∨ k)
--         ; (k = i1) → q i
--         })
--       (retEq (e i) (q i) k)
--   Iso.leftInv is p k i =
--     {!!}

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


private
  variable
    ℓA ℓ≅A ℓR ℓ≅R ℓF ℓ≅F ℓS ℓ≅S ℓP : Level

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {R : A → Type ℓR} {_≅R⟨_⟩_ : {a a' : A} → R a → UARel._≅_ 𝒮-A a a' → R a' → Type ℓ≅R}
  {ℓS ℓ≅S} {S : A → Type ℓS} {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
  {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
  where

  open UARel 𝒮-A

  𝒮ᴰ-Σ : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅ → DUARel 𝒮-A S ℓ≅S
  𝒮ᴰ-Σ _ = 𝒮ᴰ-S

  equiv-Σ : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
    → {a a' : A} → S a → UARel._≅_ 𝒮-A a a' → S a' → Type ℓ≅S
  equiv-Σ fs = DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Σ fs)

  uaᴰ-Σ : (fs : DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅)
    → {a a' : A} (b : S a) (p : a ≅ a') (b' : S a') → equiv-Σ fs b p b' ≃ PathP (λ i → S (≅→≡ p i)) b b'
  uaᴰ-Σ fs = DUARel.uaᴰ (𝒮ᴰ-Σ fs)

  -- 𝒮ᴰ-Σ : ∀ {ℓS ℓ≅S} {S : A → Type ℓS} 
  --   {πS : ∀ {a} → R a → S a} {𝒮ᴰ-S : DUARel 𝒮-A S ℓ≅S}
  --   {πS≅ : ∀ {a} {r : R a} {e} {r' : R a} → r ≅R⟨ e ⟩ r' → DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-S (πS r) e (πS r')}
  --   → DUAFields 𝒮-A R _≅R⟨_⟩_ πS 𝒮ᴰ-S πS≅
  --   → DUARel 𝒮-A S ℓ≅S
  -- 𝒮ᴰ-Σ {𝒮ᴰ-S = 𝒮ᴰ-S} _ = 𝒮ᴰ-S

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
    R.returnTC (fs ∷ʳ f , f≅s ∷ʳ f≅)
  parseFields (R.con (quote _dep[_∣_∣_]) (family∷ (indices∷ (fs v∷ ℓF h∷ ℓ≅F h∷ F h∷ πF v∷ 𝒮ᴰ-F v∷ πF≅ v∷ _)))) =
    parseFields fs >>= λ (fs , f≅s) →
    findName πF >>= λ f →
    findName πF≅ >>= λ f≅ →
    R.returnTC (fs ∷ʳ f , f≅s ∷ʳ f≅)
  parseFields t = R.typeError (R.strErr "Malformed specification (1): " ∷ R.termErr t ∷ [])

  private
    frame : ∀ {ℓA ℓB ℓC ℓD} {A : Type ℓA} {B : Type ℓB} {C : I → Type ℓC} {D : I → Type ℓD}
      {d₀ : D i0} {d₁ : D i1}
      (el : A ≃ B) (er : (i : I) → C i ≃ D i)
      (e : B ≃ PathP (λ i → C i) (invEq (er i0) d₀) (invEq (er i1) d₁))
      → A ≃ PathP (λ i → D i) d₀ d₁
    frame el er e = compEquiv el (compEquiv e (congEquivPathP⁻ er))

  List→LeftAssoc : List R.Name → RE.Assoc
  List→LeftAssoc xs = RE.Internal.ΣFormat→Assoc (go RE.unit xs)
    where
    go : RE.ΣFormat → List R.Name → RE.ΣFormat
    go acc [] = acc
    go acc (x ∷ xs) = go (acc RE., RE.leaf x) xs

  uaᴰRecordMacro : R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
  uaᴰRecordMacro spec r p r' hole =
    R.normalise spec >>= parseFields >>= λ (fs , f≅s) →
    newMeta R.unknown >>= λ f≅sEquiv →
    withI (newMeta R.unknown) >>= λ fsEquiv → 
    newMeta R.unknown >>= λ equiv →
    R.unify hole (R.def (quote frame) (f≅sEquiv v∷ vlam "_" fsEquiv v∷ equiv v∷ [])) >>
    RE.Internal.equivMacro (I.flipAssoc (List→LeftAssoc f≅s)) f≅sEquiv >>
    R.typeError [ R.termErr (RE.Internal.convertFun (I.flipAssoc (List→LeftAssoc f≅s))) ] >>
    R.unify equiv (R.def (quote uaᴰ-Σ) (spec v∷ R.unknown v∷ p v∷ R.unknown v∷ [])) >>
    withI (RE.Internal.equivMacro (List→LeftAssoc fs) fsEquiv) >>
    -- R.reduce hole >>= λ out → R.typeError [ R.termErr out ] >>
    R.returnTC tt
    where
    withI : ∀ {A : Type} → R.TC A → R.TC A
    withI = R.extendContext (varg (R.def (quote I) []))

    module I = RE.Internal

macro
  uaᴰRecord : R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
  uaᴰRecord = Internal.uaᴰRecordMacro

module Example where

  record Example (A : Type) : Type where
    field
      dog : A
      cat : Unit

  record ExampleEquiv {A B : Type} (x : Example A) (e : A ≃ B) (x' : Example B) : Type where
    field
      dogEq : e .fst (Example.dog x) ≡ Example.dog x'
      catEq : Example.cat x ≡ Example.cat x'

  test : DUAFields (𝒮-univ ℓ-zero) Example ExampleEquiv _ _ _
  test =
    fields:
    basic[ Example.dog ∣ 𝒮ᴰ-element ℓ-zero ∣ ExampleEquiv.dogEq ]
    basic[ Example.cat ∣ 𝒮ᴰ-const _ (𝒮-type Unit) ∣ ExampleEquiv.catEq ]

  example : DUARel (𝒮-univ ℓ-zero) Example ℓ-zero
  DUARel._≅ᴰ⟨_⟩_ example = ExampleEquiv
  DUARel.uaᴰ example x e x' =
   uaᴰRecord test x e x'
