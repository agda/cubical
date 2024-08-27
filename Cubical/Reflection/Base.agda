{-

Some basic utilities for reflection

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base

open import Cubical.Reflection.Sugar.Base public

import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

instance
 RawApplicativeTC : RawApplicative R.TC
 RawApplicative._<$>_ RawApplicativeTC f x = R.bindTC x λ y → R.returnTC (f y)
 RawApplicative.pure RawApplicativeTC = R.returnTC
 RawApplicative._<*>_ RawApplicativeTC f x = R.bindTC f λ f → R.bindTC x λ x → R.returnTC (f x)

instance
 RawMonadTC : RawMonad R.TC
 RawMonad._>>=_ RawMonadTC = R.bindTC
 RawMonad._>>_ RawMonadTC x y = R.bindTC x (λ _ → y)

instance
 RawMonadFailTC : RawMonadFail R.TC (List R.ErrorPart)
 RawMonadFail.fail RawMonadFailTC = R.typeError
 RawMonadFail._<|>_ RawMonadFailTC = R.catchTC

liftTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → R.TC A → R.TC B
liftTC f ta = ta >>= λ a → R.returnTC (f a)

v : ℕ → R.Term
v n = R.var n []

pattern varg t = R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) t
pattern harg {q = q} t = R.arg (R.arg-info R.hidden (R.modality R.relevant q)) t
pattern _v∷_ a l = varg a ∷ l
pattern _h∷_ a l = harg a ∷ l

pattern v[_] a = varg a ∷ []

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
