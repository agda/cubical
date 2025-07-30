{-

Some basic utilities for reflection

-}
{-# OPTIONS --no-exact-split #-}
module Cubical.Reflection.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base

import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

_>>=_ = R.bindTC
_<|>_ = R.catchTC

_>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
f >> g = f >>= λ _ → g

infixl 4 _>>=_ _>>_ _<|>_

liftTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → R.TC A → R.TC B
liftTC f ta = ta >>= λ a → R.returnTC (f a)

v : ℕ → R.Term
v n = R.var n []

pattern varg t = R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) t
pattern harg {q = q} t = R.arg (R.arg-info R.hidden (R.modality R.relevant q)) t
pattern _v∷_ a l = varg a ∷ l
pattern _h∷_ a l = harg a ∷ l

infixr 5 _v∷_ _h∷_

vlam : String → R.Term → R.Term
vlam str t = R.lam R.visible (R.abs str t)

hlam : String → R.Term → R.Term
hlam str t = R.lam R.hidden (R.abs str t)

newMeta = R.checkType R.unknown

makeAuxiliaryDef : String → R.Type → R.Term → R.TC R.Term
makeAuxiliaryDef s ty term =
  R.freshName s >>= λ name →
  R.declareDef (varg name) ty >>
  R.defineFun name [ R.clause [] [] term ] >>
  R.returnTC (R.def name [])
