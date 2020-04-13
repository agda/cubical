{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.NAryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ ℓ' : Level

-- TODO: generalize to different target type?
nAryFunStructure : (n : ℕ) → Type (ℓ-max (ℓ-suc ℓ) (nAryLevel ℓ ℓ n))
nAryFunStructure {ℓ = ℓ} n = TypeWithStr _ (λ (X : Type ℓ) → nAryOp n X X)

-- iso for n-ary functions
nAryFunIso : (n : ℕ) → StrIso (λ (X : Type ℓ) → nAryOp n X X) ℓ
nAryFunIso n (X , fX) (Y , fY) f =
  (xs : Vec X n) → equivFun f (fX $ⁿ xs) ≡ fY $ⁿ map (equivFun f) xs

nAry-is-SNS : (n : ℕ) → SNS {ℓ} _ (nAryFunIso n)
nAry-is-SNS n = SNS-≡→SNS-PathP (nAryFunIso n) (nAryFunExtEquiv n)


