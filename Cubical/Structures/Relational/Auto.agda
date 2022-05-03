{-

Macros (autoDesc, AutoStructure, AutoEquivStr, autoUnivalentStr) for automatically generating structure definitions.

For example:

  autoDesc (λ (X : Type₀) → X → X × ℕ)   ↦   function+ var (var , constant ℕ)

We prefer to use the constant structure whenever possible, e.g., [autoDesc (λ (X : Type₀) → ℕ → ℕ)]
is [constant (ℕ → ℕ)] rather than [function (constant ℕ) (constant ℕ)].

Writing [auto* (λ X → ⋯)] doesn't seem to work, but [auto* (λ (X : Type ℓ) → ⋯)] does.

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Structures.Relational.Auto where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Cubical.Structures.Relational.Macro as Macro

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

-- Magic number
private
  FUEL = 10000

-- Mark a constant type with a proof it is a set
abstract
  Const[_] : ∀ {ℓ} → hSet ℓ → Type ℓ
  Const[ A ] = A .fst

-- Some reflection utilities
private
  tLevel = R.def (quote Level) []

  tType : R.Term → R.Term
  tType ℓ = R.def (quote Type) [ varg ℓ ]

  thSet : R.Term → R.Term
  thSet ℓ = R.def (quote hSet) [ varg ℓ ]

  tPosRelDesc : R.Term → R.Term → R.Term
  tPosRelDesc ℓ ℓ₁ = R.def (quote PosRelDesc) (ℓ v∷ ℓ₁ v∷ [])

  tRelDesc : R.Term → R.Term → R.Term → R.Term
  tRelDesc ℓ ℓ₁ ℓ₁' = R.def (quote RelDesc) (ℓ v∷ ℓ₁ v∷ ℓ₁' v∷ [])

  func : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  func ℓ ℓ' = Type ℓ → Type ℓ'

  tStruct : R.Term → R.Term → R.Term
  tStruct ℓ ℓ' = R.def (quote func) (varg ℓ ∷ varg ℓ' ∷ [])

-- We try to build a descriptor by unifying the provided structure with combinators we're aware of. We
-- redefine the structure combinators as the *Shape terms below so that we don't depend on the specific way
-- these are defined in other files (order of implicit arguments and so on); the syntactic analysis that goes
-- on here means that we would get mysterious errors if those changed.
private
  constantShape : ∀ {ℓ'} (ℓ : Level) (A : hSet ℓ') → (Type ℓ → Type ℓ')
  constantShape _ A _ = Const[ A ]

  pointedShape : (ℓ : Level) → Type ℓ → Type ℓ
  pointedShape _ X = X

  productShape : ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  productShape _ A₀ A₁ X = A₀ X × A₁ X

  paramShape : ∀ {ℓ₀ ℓ'} (ℓ : Level)
    → Type ℓ' → (Type ℓ → Type ℓ₀) → Type ℓ → Type (ℓ-max ℓ' ℓ₀)
  paramShape _ A A₀ X = A → A₀ X

  functionShape :  ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  functionShape _ A₀ A₁ X = A₀ X → A₁ X

  maybeShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type ℓ₀
  maybeShape _ A₀ X = Maybe (A₀ X)

private
  -- Build transport structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildPosRelDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildPosRelDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildPosRelDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryMaybe t <|>
    R.typeError (R.strErr "Can't automatically generate a positive structure for\n" ∷ R.termErr t ∷ [])
    where
    tryConstant : R.Term → R.TC R.Term
    tryConstant t =
      newMeta (thSet ℓ') >>= λ A →
      R.unify t (R.def (quote constantShape) (varg ℓ ∷ varg A ∷ [])) >>
      R.returnTC (R.con (quote PosRelDesc.constant) (varg A ∷ []))

    tryPointed : R.Term → R.TC R.Term
    tryPointed t =
      R.unify t (R.def (quote pointedShape) (varg ℓ ∷ [])) >>
      R.returnTC (R.con (quote PosRelDesc.var) [])

    tryProduct : R.Term → R.TC R.Term
    tryProduct t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote productShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildPosRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildPosRelDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote PosRelDesc._,_) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildPosRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote PosRelDesc.maybe) (varg d₀ ∷ []))

  autoPosRelDesc' : R.Term → R.Term → R.TC Unit
  autoPosRelDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tPosRelDesc ℓ ℓ') H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildPosRelDesc FUEL ℓ ℓ' t >>= R.unify hole

  -- Build structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildRelDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildRelDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildRelDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryParam t <|> tryFunction t <|>
    tryMaybe t <|>
    R.typeError (R.strErr "Can't automatically generate a structure for\n" ∷ R.termErr t ∷ [])
    where
    tryConstant : R.Term → R.TC R.Term
    tryConstant t =
      newMeta (thSet ℓ') >>= λ A →
      R.unify t (R.def (quote constantShape) (varg ℓ ∷ varg A ∷ [])) >>
      R.returnTC (R.con (quote RelDesc.constant) (varg A ∷ []))

    tryPointed : R.Term → R.TC R.Term
    tryPointed t =
      R.unify t (R.def (quote pointedShape) (varg ℓ ∷ [])) >>
      R.returnTC (R.con (quote RelDesc.var) [])

    tryProduct : R.Term → R.TC R.Term
    tryProduct t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote productShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildRelDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote RelDesc._,_) (varg d₀ ∷ varg d₁ ∷ []))

    tryParam : R.Term → R.TC R.Term
    tryParam t =
      newMeta (tType R.unknown) >>= λ A →
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote paramShape) (varg ℓ ∷ varg A ∷ varg A₀ ∷ [])) >>
      buildRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote RelDesc.param) (varg A ∷ varg d₀ ∷ []))

    tryFunction : R.Term → R.TC R.Term
    tryFunction t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote functionShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildPosRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildRelDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote RelDesc.function+) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildRelDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote RelDesc.maybe) (varg d₀ ∷ []))

  autoRelDesc' : R.Term → R.Term → R.TC Unit
  autoRelDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tRelDesc ℓ ℓ' R.unknown) H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildRelDesc FUEL ℓ ℓ' t >>= R.unify hole

macro
  -- (Type ℓ → Type ℓ₁) → PosRelDesc ℓ
  autoPosRelDesc : R.Term → R.Term → R.TC Unit
  autoPosRelDesc = autoPosRelDesc'

  -- (S : Type ℓ → Type ℓ₁) → RelDesc ℓ
  autoRelDesc : R.Term → R.Term → R.TC Unit
  autoRelDesc = autoRelDesc'

  -- (S : Type ℓ → Type ℓ₁) → (Type ℓ → Type ℓ₁)
  -- Sanity check: should be the identity
  AutoStructure : R.Term → R.Term → R.TC Unit
  AutoStructure t hole =
    newMeta (tRelDesc R.unknown R.unknown R.unknown) >>= λ d →
    R.unify hole (R.def (quote RelMacroStructure) [ varg d ]) >>
    autoRelDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → StrRel S _
  AutoRelStr : R.Term → R.Term → R.TC Unit
  AutoRelStr t hole =
    newMeta (tRelDesc R.unknown R.unknown R.unknown) >>= λ d →
    R.unify hole (R.def (quote RelMacroRelStr) [ varg d ]) >>
    autoRelDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → SuitableStrRel S (AutoStrRel S)
  autoSuitableRel : R.Term → R.Term → R.TC Unit
  autoSuitableRel t hole =
    newMeta (tRelDesc R.unknown R.unknown R.unknown) >>= λ d →
    R.unify hole (R.def (quote relMacroSuitableRel) [ varg d ]) >>
    autoRelDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → StrRelMatchesEquiv (AutoRelStr S) (AutoEquivStr S)
  autoMatchesEquiv : R.Term → R.Term → R.TC Unit
  autoMatchesEquiv t hole =
    newMeta (tRelDesc R.unknown R.unknown R.unknown) >>= λ d →
    R.unify hole (R.def (quote relMacroMatchesEquiv) [ varg d ]) >>
    autoRelDesc' t d
