{-

Macros (autoDesc, AutoStructure, AutoEquivStr, autoUnivalentStr) for automatically generating structure definitions.

For example:

  autoDesc (λ (X : Type₀) → X → X × ℕ)   ↦   function+ var (var , constant ℕ)

We prefer to use the constant structure whenever possible, e.g., [autoDesc (λ (X : Type₀) → ℕ → ℕ)]
is [constant (ℕ → ℕ)] rather than [function (constant ℕ) (constant ℕ)].

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

-- Mark part of a structure definition to use transport-based structured equivalences
abstract
  Transp[_] : ∀ {ℓ} → Type ℓ → Type ℓ
  Transp[ A ] = A

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

  tTranspDesc : R.Term → R.Term
  tTranspDesc ℓ = R.def (quote TranspDesc) [ varg ℓ ]

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

  functionShape :  ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  functionShape _ A₀ A₁ X = A₀ X → A₁ X

  maybeShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type ℓ₀
  maybeShape _ A₀ X = Maybe (A₀ X)

  transpShape : ∀ {ℓ₀} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → Type ℓ → Type ℓ₀
  transpShape _ A₀ X = Transp[ A₀ X ]

private
  -- Build transport structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildTranspDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildTranspDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildTranspDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryFunction t <|> tryMaybe t <|>
    R.typeError (R.strErr "Can't automatically generate a transp structure for\n" ∷ R.termErr t ∷ [])
    where
    tryConstant : R.Term → R.TC R.Term
    tryConstant t =
      newMeta (tType ℓ') >>= λ A →
      R.unify t (R.def (quote constantShape) (varg ℓ ∷ varg A ∷ [])) >>
      R.returnTC (R.con (quote TranspDesc.constant) (varg A ∷ []))

    tryPointed : R.Term → R.TC R.Term
    tryPointed t =
      R.unify t (R.def (quote pointedShape) (varg ℓ ∷ [])) >>
      R.returnTC (R.con (quote TranspDesc.var) [])

    tryFunction : R.Term → R.TC R.Term
    tryFunction t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote functionShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildTranspDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildTranspDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote TranspDesc.function) (varg d₀ ∷ varg d₁ ∷ []))

    tryProduct : R.Term → R.TC R.Term
    tryProduct t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote productShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildTranspDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildTranspDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote TranspDesc._,_) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildTranspDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote TranspDesc.maybe) (varg d₀ ∷ []))

  autoTranspDesc' : R.Term → R.Term → R.TC Unit
  autoTranspDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tTranspDesc ℓ) H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildTranspDesc FUEL ℓ ℓ' t >>= R.unify hole

  -- Build structure descriptor from a function [t : Type ℓ → Type ℓ']
  buildDesc : ℕ → R.Term → R.Term → R.Term → R.TC R.Term
  buildDesc zero ℓ ℓ' t = R.typeError (R.strErr "Ran out of fuel! at \n" ∷ R.termErr t ∷ [])
  buildDesc (suc fuel) ℓ ℓ' t =
    tryConstant t <|> tryPointed t <|> tryProduct t <|> tryFunction t <|>
    tryMaybe t <|> tryTransp t <|>
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

    tryFunction : R.Term → R.TC R.Term
    tryFunction t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta tLevel >>= λ ℓ₁ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      newMeta (tStruct ℓ ℓ₁) >>= λ A₁ →
      R.unify t (R.def (quote functionShape) (varg ℓ ∷ varg A₀ ∷ varg A₁ ∷ [])) >>
      buildTranspDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      buildDesc fuel ℓ ℓ₁ A₁ >>= λ d₁ →
      R.returnTC (R.con (quote Desc.function+) (varg d₀ ∷ varg d₁ ∷ []))

    tryMaybe : R.Term → R.TC R.Term
    tryMaybe t =
      newMeta tLevel >>= λ ℓ₀ →
      newMeta (tStruct ℓ ℓ₀) >>= λ A₀ →
      R.unify t (R.def (quote maybeShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildDesc fuel ℓ ℓ₀ A₀ >>= λ d₀ →
      R.returnTC (R.con (quote Desc.maybe) (varg d₀ ∷ []))

    tryTransp : R.Term → R.TC R.Term
    tryTransp t =
      newMeta (tStruct ℓ ℓ') >>= λ A₀ →
      R.unify t (R.def (quote transpShape) (varg ℓ ∷ varg A₀ ∷ [])) >>
      buildTranspDesc fuel ℓ ℓ' A₀ >>= λ d₀ →
      R.returnTC (R.con (quote Desc.transpDesc) (varg d₀ ∷ []))

  autoDesc' : R.Term → R.Term → R.TC Unit
  autoDesc' t hole =
    R.inferType hole >>= λ H →
    newMeta tLevel >>= λ ℓ →
    newMeta tLevel >>= λ ℓ' →
    R.unify (tDesc ℓ) H >>
    R.checkType t (tStruct ℓ ℓ') >>
    buildDesc FUEL ℓ ℓ' t >>= R.unify hole

macro
  -- (Type ℓ → Type ℓ₁) → TranspDesc ℓ
  autoTranspDesc : R.Term → R.Term → R.TC Unit
  autoTranspDesc = autoTranspDesc'

  -- (S : Type ℓ → Type ℓ₁) → EquivAction (AutoStructure S)
  autoEquivAction : R.Term → R.Term → R.TC Unit
  autoEquivAction t hole =
    newMeta (tTranspDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote transpMacroAction) [ varg d ]) >>
    autoTranspDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → TransportStr (autoEquivAction S)
  autoTransportStr : R.Term → R.Term → R.TC Unit
  autoTransportStr t hole =
    newMeta (tTranspDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote transpMacroTransportStr) [ varg d ]) >>
    autoTranspDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → Desc ℓ
  autoDesc : R.Term → R.Term → R.TC Unit
  autoDesc = autoDesc'

  -- (S : Type ℓ → Type ℓ₁) → (Type ℓ → Type ℓ₁)
  -- Removes Transp[_] annotations
  AutoStructure : R.Term → R.Term → R.TC Unit
  AutoStructure t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroStructure) [ varg d ]) >>
    autoDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → StrEquiv (AutoStructure S) _
  AutoEquivStr : R.Term → R.Term → R.TC Unit
  AutoEquivStr t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroEquivStr) [ varg d ]) >>
    autoDesc' t d

  -- (S : Type ℓ → Type ℓ₁) → UnivalentStr (AutoStructure S) (AutoEquivStr S)
  autoUnivalentStr : R.Term → R.Term → R.TC Unit
  autoUnivalentStr t hole =
    newMeta (tDesc R.unknown) >>= λ d →
    R.unify hole (R.def (quote MacroUnivalentStr) [ varg d ]) >>
    autoDesc' t d
