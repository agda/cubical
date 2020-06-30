{-

Macros (autoDesc, AutoStructure, AutoEquivStr, autoUnivalentStr) for automatically generating structure definitions.

For example:

  autoDesc (λ (X : Type₀) → X → X × ℕ)   ↦   recvar (var , constant ℕ)

We prefer to use the constant structure whenever possible, e.g., [autoDesc (λ (X : Type₀) → ℕ → ℕ)]
is [constant (ℕ → ℕ)] rather than [param ℕ (constant ℕ)].

Writing [auto* (λ X → ⋯)] doesn't seem to work, but [auto* (λ (X : Type ℓ) → ⋯)] does.

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Auto where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Cubical.Structures.Macro as Macro

import Agda.Builtin.Reflection as R

-- Magic number
private
  FUEL = 10000

-- Mark part of a structure definition as functorial
abstract
  Funct[_] : ∀ {ℓ} → Type ℓ → Type ℓ
  Funct[ A ] = A

-- Some reflection utilities
private
  _>>=_ = R.bindTC
  _<|>_ = R.catchTC

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
  f >> g = f >>= λ _ → g

  infixl 4 _>>=_ _>>_ _<|>_

  varg : ∀ {ℓ} {A : Type ℓ} → A → R.Arg A
  varg = R.arg (R.arg-info R.visible R.relevant)

  tLevel = R.def (quote Level) []

  tType : R.Term → R.Term
  tType ℓ = R.def (quote Type) [ varg ℓ ]

  tFuncDesc : R.Term → R.Term
  tFuncDesc ℓ = R.def (quote FuncDesc) [ varg ℓ ]

  tDesc : R.Term → R.Term
  tDesc ℓ = R.def (quote Desc) [ varg ℓ ]

  func : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  func ℓ ℓ' = Type ℓ → Type ℓ'

  tStruct : R.Term → R.Term → R.Term
  tStruct ℓ ℓ' = R.def (quote func) (varg ℓ ∷ varg ℓ' ∷ [])

  newMeta = R.checkType R.unknown

-- We try to build a descriptor by unifying the provided structure with combinators we're aware of. We
-- redefine the structure combinators as the *Shape terms below so that we don't depend on the specific way
-- these are defined in other files (order of implicit arguments and so on); the syntactic analysis that goes
-- on here means that we would get mysterious errors if those changed.
private
  constantShape : ∀ {ℓ'} (ℓ : Level) (A : Type ℓ') → (Type ℓ → Type ℓ')
  constantShape _ A _ = A

  pointedShape : (ℓ : Level) → Type ℓ → Type ℓ
  pointedShape _ X = X

  productShape : ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  productShape _ A₀ A₁ X = A₀ X × A₁ X

  paramShape : ∀ {ℓ₀ ℓ'} (ℓ : Level)
    → Type ℓ' → (Type ℓ → Type ℓ₀) → Type ℓ → Type (ℓ-max ℓ' ℓ₀)
  paramShape _ A A₀ X = A → A₀ X

  recvarShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type (ℓ-max ℓ ℓ₀)
  recvarShape _ A₀ X = X → A₀ X

  functionShape :  ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  functionShape _ A₀ A₁ X = A₀ X → A₁ X

  maybeShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type ℓ₀
  maybeShape _ A₀ X = Maybe (A₀ X)

  functorialShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type ℓ₀
  functorialShape _ A₀ X = Funct[ A₀ X ]

private
  -- Build functorial structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildFuncDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildFuncDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildFuncDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryParam t <|> tryMaybe t <|>
    R.typeError (R.strErr "Can't automatically generate a functorial structure for\n" ∷ R.termErr t ∷ [])
    where
    tryConstant : R.Term → R.TC R.Term
    tryConstant t =
      newMeta (tType ℓ') >>= λ A →
      R.unify t (R.def (quote constantShape) (varg ℓ ∷ varg A ∷ [])) >>
      R.returnTC (R.con (quote FuncDesc.constant) (varg A ∷ []))

    tryPointed : R.Term → R.TC R.Term
    tryPointed t =
      R.unify t (R.def (quote pointedShape) (varg ℓ ∷ [])) >>
      R.returnTC (R.con (quote FuncDesc.var) [])

    tryParam : R.Term → R.TC R.Term
    tryParam t =
      newMeta (tType R.unknown) >>= λ A →
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote paramShape) (varg ℓ ∷ varg A ∷ varg A₀ ∷ [])) >>
      buildFuncDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote FuncDesc.param) (varg A ∷ varg d₀ ∷ []))

    tryProduct : R.Term → R.TC R.Term
    tryProduct t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote productShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildFuncDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildFuncDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote FuncDesc._,_) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildFuncDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote FuncDesc.maybe) (varg d₀ ∷ []))

  autoFuncDesc' : R.Term → R.Term → R.TC Unit
  autoFuncDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tFuncDesc ℓ) H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildFuncDesc FUEL ℓ ℓ' t >>= R.unify hole

  -- Build structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryFunction+ t <|>
    tryFunction t <|> tryMaybe t <|> tryFunct t <|>
    R.typeError (R.strErr "Can't automatically generate a structure for\n" ∷ R.termErr t ∷ [])
    where
    tryConstant : R.Term → R.TC R.Term
    tryConstant t =
      newMeta (tType ℓ') >>= λ A →
      R.unify t (R.def (quote constantShape) (varg ℓ ∷ varg A ∷ [])) >>
      R.returnTC (R.con (quote Desc.constant) (varg A ∷ []))

    tryPointed : R.Term → R.TC R.Term
    tryPointed t =
      R.unify t (R.def (quote pointedShape) (varg ℓ ∷ [])) >>
      R.returnTC (R.con (quote Desc.var) [])

    tryProduct : R.Term → R.TC R.Term
    tryProduct t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote productShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote Desc._,_) (varg d₀ ∷ varg d₁ ∷ []))

    tryFunction+ : R.Term → R.TC R.Term
    tryFunction+ t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote functionShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildFuncDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote Desc.function+) (varg d₀ ∷ varg d₁ ∷ []))

    tryFunction : R.Term → R.TC R.Term
    tryFunction t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote functionShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote Desc.function) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote Desc.maybe) (varg d₀ ∷ []))

    tryFunct : R.Term → R.TC R.Term
    tryFunct t =
      newMeta (tStruct ℓ ℓ') >>= λ A₀ →
      R.unify t (R.def (quote functorialShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildFuncDesc fuel ℓ ℓ' A₀ >>= λ d₀ →
      R.returnTC (R.con (quote Desc.functorial) (varg d₀ ∷ []))

  autoDesc' : R.Term → R.Term → R.TC Unit
  autoDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tDesc ℓ) H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildDesc FUEL ℓ ℓ' t >>= R.unify hole

macro
  -- (Type ℓ → Type ℓ₁) → FuncDesc ℓ
  autoFuncDesc : R.Term → R.Term → R.TC Unit
  autoFuncDesc = autoFuncDesc'

  -- (S : Type ℓ → Type ℓ₁) → ∀ {X Y} → (X → Y) → (S X → S Y)
  autoFuncAction : R.Term → R.Term → R.TC Unit
  autoFuncAction t hole =
    newMeta (tFuncDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote funcMacroAction) [ varg d ]) >>
    autoFuncDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → ∀ {X} s → autoFuncAction S (idfun X) s ≡ s
  autoFuncId : R.Term → R.Term → R.TC Unit
  autoFuncId t hole =
    newMeta (tFuncDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote funcMacroId) [ varg d ]) >>
    autoFuncDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → Desc ℓ
  autoDesc : R.Term → R.Term → R.TC Unit
  autoDesc = autoDesc'

  -- (S : Type ℓ → Type ℓ₁) → (Type ℓ → Type ℓ₁)
  -- Removes Funct[_] annotations
  AutoStructure : R.Term → R.Term → R.TC Unit
  AutoStructure t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroStructure) [ varg d ]) >>
    autoDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → StrIso (AutoStructure S) _
  AutoEquivStr : R.Term → R.Term → R.TC Unit
  AutoEquivStr t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroEquivStr) [ varg d ]) >>
    autoDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → SNS (AutoStructure S) (AutoEquivStr S)
  autoUnivalentStr : R.Term → R.Term → R.TC Unit
  autoUnivalentStr t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroUnivalentStr) [ varg d ]) >>
    autoDesc' t d
