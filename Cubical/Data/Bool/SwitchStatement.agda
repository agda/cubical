{-# OPTIONS --safe #-}
module Cubical.Data.Bool.SwitchStatement where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool.Base
open import Cubical.Data.Nat

{-
  Switch-case:

    _==_ : A → A → Bool

    _ : B
    _ = switch (λ x → x == fixedValue) cases
           case value1 ⇒ result1 break
           case value2 ⇒ result2 break
           ...
           case valueN ⇒ resultN break
           default⇒ defaultResult
-}


private
  variable
    ℓ ℓ' : Level


infixr 6 default⇒_
infixr 5 case_⇒_break_
infixr 4 switch_cases_

switch_cases_ : {A : Type ℓ} {B : Type ℓ'} → (A → Bool) → ((A → Bool) → B) → B
switch caseIndicator cases caseData = caseData caseIndicator

case_⇒_break_ : {A : Type ℓ} {B : Type ℓ'} → A → B → (otherCases : (A → Bool) → B) → (A → Bool) → B
case forValue ⇒ result break otherCases = λ caseIndicator → if (caseIndicator forValue) then result else (otherCases caseIndicator)

default⇒_ : {A : Type ℓ} {B : Type ℓ'} → B → (A → Bool) → B
default⇒_ value caseIndicator = value
