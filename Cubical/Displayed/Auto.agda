{-

  - Automatically generate UARel and DUARel instances

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
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
open import Cubical.Displayed.Universe

open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base
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

    pi : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} (dA : UARelDesc 𝒮-A)
      {B : A → Type ℓB} {𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B} (dB : DUARelDesc 𝒮-A 𝒮ᴰ-B)
      → UARelDesc (𝒮-Π 𝒮-A 𝒮ᴰ-B)

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


  data SubstRelDesc : ∀ {ℓA ℓ≅A ℓB}
    {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
    {B : A → Type ℓB} (𝒮ˢ-B : SubstRel 𝒮-A B) → Typeω
    where

    generic : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
      → SubstRelDesc 𝒮-A (𝒮ˢ-generic 𝒮-A B)

    constant : ∀ {ℓA ℓ≅A ℓB}
      {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : Type ℓB}
      → SubstRelDesc 𝒮-A (𝒮ˢ-const 𝒮-A B)

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

private
  module _
    (rec : R.Term → R.TC Unit)
    (recᴿ : R.Term → R.TC Unit)
    (recˢ : R.Term → R.TC Unit)
    (recᴰ : R.Term → R.TC Unit)
    (hole : R.Term)
    where

    module UA where
      tryUniv : R.TC Unit
      tryUniv = R.unify (R.con (quote UARelDesc.univ) [ varg R.unknown ]) hole

      tryBinary : R.Name → R.TC Unit
      tryBinary name =
        newMeta R.unknown >>= λ hole₁ →
        newMeta R.unknown >>= λ hole₂ →
        R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
        rec hole₁ >>
        recᴰ hole₂

      trySigma = tryBinary (quote UARelDesc.sigma)
      tryPi = tryBinary (quote UARelDesc.pi)

      useGeneric : R.TC Unit
      useGeneric = R.unify (R.con (quote UARelDesc.generic) []) hole

    module Reindex where
      tryId : R.TC Unit
      tryId = R.unify (R.con (quote UARelReindex.id) []) hole

      tryUnary : R.Name → R.TC Unit
      tryUnary name =
        newMeta R.unknown >>= λ hole₁ →
        R.unify (R.con name [ varg hole₁ ]) hole >>
        recᴿ hole₁

      tryFst = tryUnary (quote UARelReindex.∘fst)
      trySnd = tryUnary (quote UARelReindex.∘snd)

    module Subst where

      tryConstant : R.TC Unit
      tryConstant =
        R.unify (R.con (quote SubstRelDesc.constant) []) hole

      tryEl : R.TC Unit
      tryEl =
        newMeta R.unknown >>= λ hole₁ →
        R.unify (R.con (quote SubstRelDesc.el) [ varg hole₁ ]) hole >>
        recᴿ hole₁

      tryBinary : R.Name → R.TC Unit
      tryBinary name =
        newMeta R.unknown >>= λ hole₁ →
        newMeta R.unknown >>= λ hole₂ →
        R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
        recˢ hole₁ >>
        recˢ hole₂

      trySigma = tryBinary (quote SubstRelDesc.sigma)
      tryPi = tryBinary (quote SubstRelDesc.pi)

      useGeneric : R.TC Unit
      useGeneric = R.unify (R.con (quote SubstRelDesc.generic) []) hole

    module DUA where

      tryConstant : R.TC Unit
      tryConstant =
        newMeta R.unknown >>= λ hole₁ →
        R.unify (R.con (quote DUARelDesc.constant) [ varg hole₁ ]) hole >>
        rec hole₁

      tryEl : R.TC Unit
      tryEl =
        newMeta R.unknown >>= λ hole₁ →
        R.unify (R.con (quote DUARelDesc.el) [ varg hole₁ ]) hole >>
        recᴿ hole₁

      tryBinary : R.Name → R.TC Unit
      tryBinary name =
        newMeta R.unknown >>= λ hole₁ →
        newMeta R.unknown >>= λ hole₂ →
        R.unify (R.con name (hole₁ v∷ hole₂ v∷ [])) hole >>
        recᴰ hole₁ >>
        recᴰ hole₂

      trySigma = tryBinary (quote DUARelDesc.sigma)
      tryPi = tryBinary (quote DUARelDesc.pi)

      tryPiˢ : R.TC Unit
      tryPiˢ =
        newMeta R.unknown >>= λ hole₁ →
        newMeta R.unknown >>= λ hole₂ →
        R.unify (R.con (quote DUARelDesc.piˢ) (hole₁ v∷ hole₂ v∷ [])) hole >>
        recˢ hole₁ >>
        recᴰ hole₂

      useGeneric : R.TC Unit
      useGeneric = R.unify (R.con (quote DUARelDesc.generic) []) hole

mutual
  autoUARelDesc : ℕ → R.Term → R.TC Unit
  autoUARelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoUARelDesc (suc n) hole =
    tryUniv <|> trySigma <|> tryPi <|> useGeneric
    where
    open UA (autoUARelDesc n) (autoUARelReindex n) (autoSubstRelDesc n) (autoDUARelDesc n) hole

  autoUARelReindex : ℕ → R.Term → R.TC Unit
  autoUARelReindex zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoUARelReindex (suc n) hole =
    tryId <|> tryFst <|> trySnd
    where
    open Reindex (autoUARelDesc n) (autoUARelReindex n) (autoSubstRelDesc n) (autoDUARelDesc n) hole

  autoSubstRelDesc : ℕ → R.Term → R.TC Unit
  autoSubstRelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoSubstRelDesc (suc n) hole =
    tryConstant <|> tryEl <|> tryEl <|> trySigma <|> tryPi <|> useGeneric
    where
    open Subst (autoUARelDesc n) (autoUARelReindex n) (autoSubstRelDesc n) (autoDUARelDesc n) hole

  autoDUARelDesc : ℕ → R.Term → R.TC Unit
  autoDUARelDesc zero hole = R.typeError [ R.strErr "Out of fuel" ]
  autoDUARelDesc (suc n) hole =
    tryConstant <|> tryEl <|> trySigma <|> tryPiˢ <|> tryPi <|> useGeneric
    where
    open DUA (autoUARelDesc n) (autoUARelReindex n) (autoSubstRelDesc n) (autoDUARelDesc n) hole

autoUARelMacro : ∀ {ℓA} {A : Type ℓA} → ℕ → R.Term → R.TC Unit
autoUARelMacro {A = A} n hole =
  R.quoteTC A >>= λ `A` →
  R.checkType hole (R.def (quote UARel) (`A` v∷ R.unknown v∷ [])) >>
  newMeta R.unknown >>= λ desc →
  R.unify hole (R.def (quote getUARel) [ varg desc ]) >>
  autoUARelDesc n desc

autoDUARelMacro : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
  → ℕ → R.Term → R.TC Unit
autoDUARelMacro {𝒮-A = 𝒮-A} {B = B} n hole =
  R.quoteTC 𝒮-A >>= λ `𝒮-A` →
  R.quoteTC B >>= λ `B` →
  R.checkType hole (R.def (quote DUARel) (`𝒮-A` v∷ `B` v∷ R.unknown v∷ [])) >>
  newMeta R.unknown >>= λ desc →
  R.unify hole (R.def (quote getDUARel) [ varg desc ]) >>
  autoDUARelDesc n desc

macro
  autoUARel : ∀ {ℓA} {A : Type ℓA} → R.Term → R.TC Unit
  autoUARel {A = A} = autoUARelMacro {A = A} FUEL

  autoDUARel : ∀ {ℓA ℓ≅A ℓB} {A : Type ℓA} {𝒮-A : UARel A ℓ≅A} {B : A → Type ℓB}
    → R.Term → R.TC Unit
  autoDUARel {𝒮-A = 𝒮-A} {B = B} = autoDUARelMacro {𝒮-A = 𝒮-A} {B = B} FUEL
