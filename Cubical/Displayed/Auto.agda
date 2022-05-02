{-

  - Automatically generate UARel and DUARel instances

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Displayed.Auto where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Morphism

open import Cubical.Displayed.Constant
open import Cubical.Displayed.Function
open import Cubical.Displayed.Generic
open import Cubical.Displayed.Sigma
open import Cubical.Displayed.Unit
open import Cubical.Displayed.Universe

open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Unit.Base

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

-- Descriptor language

mutual
  data UARelDesc : ∀ {ℓA ℓ≅A} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) → Typeω where

    generic : ∀ {ℓA} {A : Type ℓA} → UARelDesc (𝒮-generic A)

    univ : ∀ ℓU → UARelDesc (𝒮-Univ ℓU)

    sigma : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} (dA : UARelDesc 𝒮-A)
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B} (dB : DUARelDesc 𝒮-A 𝒮ᴰ-B)
      → UARelDesc (∫ 𝒮ᴰ-B)

    param : ∀ {ℓA ℓB ℓ≅B} (A : Type ℓA)
      {B : Type ℓB} {𝒮-B : UARel B ℓ≅B} (dB : UARelDesc 𝒮-B)
      → UARelDesc (A →𝒮 𝒮-B)

    pi : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} (dA : UARelDesc 𝒮-A)
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B} (dB : DUARelDesc 𝒮-A 𝒮ᴰ-B)
      → UARelDesc (𝒮-Π 𝒮-A 𝒮ᴰ-B)

    unit : UARelDesc 𝒮-Unit

  -- Projections from one UARel to another
  data UARelReindex : ∀ {ℓA ℓ≅A ℓC ℓ≅C}
    {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
    {C : Type ℓC} {𝒮-C : UARel C ℓ≅C}
    (f : UARelHom 𝒮-A 𝒮-C)
    → Typeω
    where

    id : ∀ {ℓA ℓ≅A} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      → UARelReindex (𝒮-id 𝒮-A)

    ∘fst : ∀ {ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B}
      {C : Type ℓC} {𝒮-C : UARel C ℓ≅C}
      {f : UARelHom 𝒮-A 𝒮-C}
      → UARelReindex f
      → UARelReindex (𝒮-∘ f (𝒮-fst {𝒮ᴰ-B = 𝒮ᴰ-B}))

    ∘snd : ∀ {ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
      {C : Type ℓC} {𝒮-C : UARel C ℓ≅C}
      {f : UARelHom 𝒮-B 𝒮-C}
      → UARelReindex f
      → UARelReindex (𝒮-∘ f (𝒮-snd {𝒮-A = 𝒮-A}))

    ∘app : ∀ {ℓA ℓB ℓ≅B ℓC ℓ≅C}
      {A : Type ℓA}
      {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
      {C : Type ℓC} {𝒮-C : UARel C ℓ≅C}
      {f : UARelHom 𝒮-B 𝒮-C}
      → UARelReindex f
      → (a : A) → UARelReindex (𝒮-∘ f (𝒮-app a))

  data SubstRelDesc : ∀ {ℓA ℓ≅A ℓB}
    {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
    {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B) → Typeω
    where

    generic : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
      → SubstRelDesc 𝒮-A (𝒮ˢ-generic 𝒮-A B)

    constant : ∀ {ℓA ℓ≅A ℓB}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB}
      → SubstRelDesc 𝒮-A (𝒮ˢ-const 𝒮-A B)

    -- We have an element DUARel over any 𝒮-A with a proejction to a universe
    -- that can be described with UARelReindex
    el : ∀ {ℓA ℓ≅A ℓU} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {f : UARelHom 𝒮-A (𝒮-Univ ℓU)}
      → UARelReindex f
      → SubstRelDesc 𝒮-A (𝒮ˢ-reindex f (𝒮ˢ-El ℓU))

    sigma : ∀ {ℓA ℓ≅A ℓB ℓC}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ˢ-B : SubstRel 𝒮-A B} (dB : SubstRelDesc 𝒮-A 𝒮ˢ-B)
      {C : Σ A B → Type ℓC} {𝒮ˢ-C : SubstRel (∫ˢ 𝒮ˢ-B) C} (dC : SubstRelDesc (∫ˢ 𝒮ˢ-B) 𝒮ˢ-C)
      → SubstRelDesc 𝒮-A (𝒮ˢ-Σ 𝒮ˢ-B 𝒮ˢ-C)

    pi : ∀ {ℓA ℓ≅A ℓB ℓC}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ˢ-B : SubstRel 𝒮-A B} (dB : SubstRelDesc 𝒮-A 𝒮ˢ-B)
      {C : Σ A B → Type ℓC} {𝒮ˢ-C : SubstRel (∫ˢ 𝒮ˢ-B) C} (dC : SubstRelDesc (∫ˢ 𝒮ˢ-B) 𝒮ˢ-C)
      → SubstRelDesc 𝒮-A (𝒮ˢ-Π 𝒮ˢ-B 𝒮ˢ-C)

  data DUARelDesc : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
    {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
    {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B) → Typeω
    where

    generic : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
      → DUARelDesc 𝒮-A (𝒮ᴰ-generic 𝒮-A B)

    constant : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : Type ℓB} {𝒮-B : UARel B ℓ≅B}
      → UARelDesc 𝒮-B
      → DUARelDesc 𝒮-A (𝒮ᴰ-const 𝒮-A 𝒮-B)

    el : ∀ {ℓA ℓ≅A ℓU} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {f : UARelHom 𝒮-A (𝒮-Univ ℓU)}
      → UARelReindex f
      → DUARelDesc 𝒮-A (𝒮ᴰ-reindex f (𝒮ᴰ-El ℓU))

    sigma : ∀ {ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B} (dB : DUARelDesc 𝒮-A 𝒮ᴰ-B)
      {C : Σ A B → Type ℓC} {𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) C ℓ≅C} (dC : DUARelDesc (∫ 𝒮ᴰ-B) 𝒮ᴰ-C)
      → DUARelDesc 𝒮-A (𝒮ᴰ-Σ 𝒮ᴰ-B 𝒮ᴰ-C)

    pi : ∀ {ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B} (dB : DUARelDesc 𝒮-A 𝒮ᴰ-B)
      {C : Σ A B → Type ℓC} {𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) C ℓ≅C} (dC : DUARelDesc (∫ 𝒮ᴰ-B) 𝒮ᴰ-C)
      → DUARelDesc 𝒮-A (𝒮ᴰ-Π 𝒮ᴰ-B 𝒮ᴰ-C)

    piˢ : ∀ {ℓA ℓ≅A ℓB ℓC ℓ≅C}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
      {B : A → Type ℓB} {𝒮ˢ-B : SubstRel 𝒮-A B} (dB : SubstRelDesc 𝒮-A 𝒮ˢ-B)
      {C : Σ A B → Type ℓC} {𝒮ᴰ-C : DUARel (∫ˢ 𝒮ˢ-B) C ℓ≅C} (dC : DUARelDesc (∫ˢ 𝒮ˢ-B) 𝒮ᴰ-C)
      → DUARelDesc 𝒮-A (𝒮ᴰ-Πˢ 𝒮ˢ-B 𝒮ᴰ-C)

private
  getUARel : ∀ {ℓA ℓ≅A} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
    → UARelDesc 𝒮-A → UARel A ℓ≅A
  getUARel {𝒮-A = 𝒮-A} _ = 𝒮-A

  getDUARel : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
    {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
    {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B}
    → DUARelDesc 𝒮-A 𝒮ᴰ-B → DUARel 𝒮-A B ℓ≅B
  getDUARel {𝒮ᴰ-B = 𝒮ᴰ-B} _ = 𝒮ᴰ-B

-- Magic number
private
  FUEL = 10000

mutual
  autoUARelDesc : ℕ → R.Term → R.TC Unit
  autoUARelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoUARelDesc (suc n) hole =
    tryUniv <|> trySigma <|> tryParam <|> tryPi <|> tryUnit <|> useGeneric
    where
    tryUniv : R.TC Unit
    tryUniv = R.unify (R.con (quote UARelDesc.univ) [ varg R.unknown ]) hole

    tryBinary : R.Name → R.TC Unit
    tryBinary name =
      newMeta R.unknown >>= λ hole₁ →
      newMeta R.unknown >>= λ hole₂ →
      R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
      autoUARelDesc n hole₁ >>
      autoDUARelDesc n hole₂

    tryParam : R.TC Unit
    tryParam =
      newMeta R.unknown >>= λ paramTy →
      newMeta R.unknown >>= λ hole₁ →
      R.unify (R.con (quote UARelDesc.param) (paramTy v∷ hole₁ v∷ [])) hole >>
      autoUARelDesc n hole₁

    trySigma = tryBinary (quote UARelDesc.sigma)
    tryPi = tryBinary (quote UARelDesc.pi)

    tryUnit : R.TC Unit
    tryUnit = R.unify (R.con (quote UARelDesc.unit) []) hole

    useGeneric : R.TC Unit
    useGeneric = R.unify (R.con (quote UARelDesc.generic) []) hole

  autoUARelReindex : ℕ → R.Term → R.TC Unit
  autoUARelReindex zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoUARelReindex (suc n) hole =
    tryId <|> tryFst <|> trySnd <|> tryApp
    where
    tryId : R.TC Unit
    tryId = R.unify (R.con (quote UARelReindex.id) []) hole

    tryUnary : R.Name → R.TC Unit
    tryUnary name =
      newMeta R.unknown >>= λ hole₁ →
      R.unify (R.con name [ varg hole₁ ]) hole >>
      autoUARelReindex n hole₁

    tryFst = tryUnary (quote UARelReindex.∘fst)
    trySnd = tryUnary (quote UARelReindex.∘snd)

    tryApp : R.TC Unit
    tryApp =
      newMeta R.unknown >>= λ hole₁ →
      newMeta R.unknown >>= λ param →
      R.unify (R.con (quote UARelReindex.∘app) (hole₁ v∷ param v∷ [])) hole >>
      autoUARelReindex n hole₁

  autoSubstRelDesc : ℕ → R.Term → R.TC Unit
  autoSubstRelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoSubstRelDesc (suc n) hole =
    tryConstant <|> tryEl <|> tryEl <|> trySigma <|> tryPi <|> useGeneric
    where
    tryConstant : R.TC Unit
    tryConstant =
      R.unify (R.con (quote SubstRelDesc.constant) []) hole

    tryEl : R.TC Unit
    tryEl =
      newMeta R.unknown >>= λ hole₁ →
      R.unify (R.con (quote SubstRelDesc.el) [ varg hole₁ ]) hole >>
      autoUARelReindex n hole₁

    tryBinary : R.Name → R.TC Unit
    tryBinary name =
      newMeta R.unknown >>= λ hole₁ →
      newMeta R.unknown >>= λ hole₂ →
      R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
      autoSubstRelDesc n hole₁ >>
      autoSubstRelDesc n hole₂

    trySigma = tryBinary (quote SubstRelDesc.sigma)
    tryPi = tryBinary (quote SubstRelDesc.pi)

    useGeneric : R.TC Unit
    useGeneric = R.unify (R.con (quote SubstRelDesc.generic) []) hole

  autoDUARelDesc : ℕ → R.Term → R.TC Unit
  autoDUARelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoDUARelDesc (suc n) hole =
    tryConstant <|> tryEl <|> trySigma <|> tryPiˢ <|> tryPi <|> useGeneric
    where
    tryConstant : R.TC Unit
    tryConstant =
      newMeta R.unknown >>= λ hole₁ →
      R.unify (R.con (quote DUARelDesc.constant) [ varg hole₁ ]) hole >>
      autoUARelDesc n hole₁

    tryEl : R.TC Unit
    tryEl =
      newMeta R.unknown >>= λ hole₁ →
      R.unify (R.con (quote DUARelDesc.el) [ varg hole₁ ]) hole >>
      autoUARelReindex n hole₁

    tryBinary : R.Name → R.TC Unit
    tryBinary name =
      newMeta R.unknown >>= λ hole₁ →
      newMeta R.unknown >>= λ hole₂ →
      R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
      autoDUARelDesc n hole₁ >>
      autoDUARelDesc n hole₂

    trySigma = tryBinary (quote DUARelDesc.sigma)
    tryPi = tryBinary (quote DUARelDesc.pi)

    tryPiˢ : R.TC Unit
    tryPiˢ =
      newMeta R.unknown >>= λ hole₁ →
      newMeta R.unknown >>= λ hole₂ →
      R.unify (R.con (quote DUARelDesc.piˢ) (hole₁ v∷ hole₂ v∷ [])) hole >>
      autoSubstRelDesc n hole₁ >>
      autoDUARelDesc n hole₂

    useGeneric : R.TC Unit
    useGeneric = R.unify (R.con (quote DUARelDesc.generic) []) hole

module DisplayedAutoMacro where
  autoUARel : ∀ {ℓA} (A : Type ℓA) → ℕ → R.Term → R.TC Unit
  autoUARel A n hole =
    R.quoteTC A >>= λ `A` →
    newMeta R.unknown >>= λ desc →
    makeAuxiliaryDef "autoUA"
      (R.def (quote UARel) (`A` v∷ R.unknown v∷ []))
      (R.def (quote getUARel) [ varg desc ])
      >>= λ uaTerm →
    R.unify hole uaTerm >>
    autoUARelDesc n desc

  autoDUARel : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB)
    → ℕ → R.Term → R.TC Unit
  autoDUARel 𝒮-A B n hole =
    R.quoteTC 𝒮-A >>= λ `𝒮-A` →
    R.quoteTC B >>= λ `B` →
    newMeta R.unknown >>= λ desc →
    makeAuxiliaryDef "autoDUA"
      (R.def (quote DUARel) (`𝒮-A` v∷ `B` v∷ R.unknown v∷ []))
      (R.def (quote getDUARel) [ varg desc ])
      >>= λ duaTerm →
    R.unify hole duaTerm >>
    autoDUARelDesc n desc

macro
  autoUARel : ∀ {ℓA} (A : Type ℓA) → R.Term → R.TC Unit
  autoUARel A = DisplayedAutoMacro.autoUARel A FUEL

  autoDUARel : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB)
    → R.Term → R.TC Unit
  autoDUARel 𝒮-A B = DisplayedAutoMacro.autoDUARel 𝒮-A B FUEL

private
  module Example (A : Type) (a₀ : A) where

    example0 : DUARel (autoUARel Type) (λ X → X → A × X) ℓ-zero
    example0 = autoDUARel _ _

    example0' : {X Y : Type} (e : X ≃ Y)
      (f : X → A × X) (g : Y → A × Y)
      → (∀ x → (f x .fst ≡ g (e .fst x) .fst) × (e .fst (f x .snd) ≡ g (e .fst x) .snd))
      → PathP (λ i → ua e i → A × ua e i) f g
    example0' e f g = example0 .DUARel.uaᴰ f e g .fst

    -- An example where a DUARel is parameterized over a pair of types

    example1 : DUARel (autoUARel (Type × Type)) (λ (X , Z) → X → Z) ℓ-zero
    example1 = autoDUARel _ _

    example1' : {X Y : Type} (e : X ≃ Y) {Z W : Type} (h : Z ≃ W)
      (f : X → Z) (g : Y → W)
      → (∀ x → h .fst (f x) ≡ g (e .fst x))
      → PathP (λ i → ua e i → ua h i) f g
    example1' e h f g = example1 .DUARel.uaᴰ f (e , h) g .fst

    -- An example where a DUARel is parameterized over a family of types

    example2 : DUARel (autoUARel (A → Type)) (λ B → B a₀) ℓ-zero
    example2 = autoDUARel _ _

    example2' : {B C : A → Type} (e : (a : A) → B a ≃ C a)
      (b : B a₀) (c : C a₀)
      → e a₀ .fst b ≡ c
      → PathP (λ i → ua (e a₀) i) b c
    example2' e b c = example2 .DUARel.uaᴰ b e c .fst
