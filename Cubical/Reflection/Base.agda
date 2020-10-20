{-

Some basic utilities for reflection

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Reflection.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat

import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

_>>=_ = R.bindTC
_<|>_ = R.catchTC

_$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
f $ a = f a

_>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
f >> g = f >>= λ _ → g

infixl 4 _>>=_ _>>_ _<|>_
infixr 3 _$_

liftTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → R.TC A → R.TC B
liftTC f ta = ta >>= λ a → R.returnTC (f a)

v : ℕ → R.Term
v n = R.var n []

pattern varg t = R.arg (R.arg-info R.visible R.relevant) t
pattern harg t = R.arg (R.arg-info R.hidden R.relevant) t
pattern _v∷_ a l = varg a ∷ l
pattern _h∷_ a l = harg a ∷ l

infixr 5 _v∷_ _h∷_

vlam : String → R.Term → R.Term
vlam str t = R.lam R.visible (R.abs str t)

newMeta = R.checkType R.unknown

