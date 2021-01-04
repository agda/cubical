{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Bool.SwitchStatement where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool.Base
open import Cubical.Data.Nat

{-
  Switch-case:

     _ : Bool → Bool
     _ = switch (λ x → x) cases
            case true ⇒ false break
            case false ⇒ true break
            default⇒ false
-}


private
  variable
    ℓ ℓ′ : Level


infixr 6 default⇒_
infixr 5 case_⇒_break_
infixr 4 switch_cases_

switch_cases_ : {A : Type ℓ} {B : Type ℓ′} → (A → Bool) → ((A → Bool) → A → B) → A → B
switch_cases_ caseIndicator caseData = caseData caseIndicator

case_⇒_break_ : {A : Type ℓ} {B : Type ℓ′} → A → B → (otherCases : (A → Bool) → A → B) → (A → Bool) → A → B
case_⇒_break_ forValue result otherCases = λ caseIndicator a → if (caseIndicator forValue) then result else (otherCases caseIndicator a)

default⇒_ : {A : Type ℓ} {B : Type ℓ′} → B → (A → Bool) → A → B
default⇒_ value caseIndicator _ = value
