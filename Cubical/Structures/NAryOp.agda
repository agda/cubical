{-# OPTIONS --cubical --no-import-sorts --safe #-}
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

nAryFunSNS : (n : ℕ) → SNS {ℓ} _ (nAryFunIso n)
nAryFunSNS n = SNS-≡→SNS-PathP (nAryFunIso n) (nAryFunExtEquiv n)

-- Some specializations that are not used at the moment, but kept as
-- they might become useful later.
private

  -- unary
  unaryFunIso : StrIso  (λ (X : Type ℓ) → nAryOp 1 X X) ℓ
  unaryFunIso (A , f) (B , g) e =
    (x : A) → equivFun e (f x) ≡ g (equivFun e x)

  unaryFunSNS : SNS {ℓ} _ unaryFunIso
  unaryFunSNS = SNS-≡→SNS-PathP unaryFunIso (λ s t → compEquiv lem (nAryFunExtEquiv 1 s t))
    where
    lem : ∀ {X} → {s t : X → X} →
            ((x : X) → s x ≡ t x) ≃
            ((xs : Vec X 1) → (s $ⁿ xs) ≡ (t $ⁿ map (λ x → x) xs))
    lem {X} {s} {t} = isoToEquiv f
      where
      f : Iso ((x : X) → s x ≡ t x)
              ((xs : Vec X 1) → (s $ⁿ xs) ≡ (t $ⁿ map (λ x → x) xs))
      Iso.fun f p (x ∷ [])           = p x
      Iso.inv f p x                  = p (x ∷ [])
      Iso.rightInv f p _ xs@(x ∷ []) = p xs
      Iso.leftInv f p _              = p

  -- binary
  binaryFunIso : StrIso  (λ (X : Type ℓ) → nAryOp 2 X X) ℓ
  binaryFunIso (A , f) (B , g) e =
    (x y : A) → equivFun e (f x y) ≡ g (equivFun e x) (equivFun e y)

  binaryFunSNS : SNS {ℓ} _ binaryFunIso
  binaryFunSNS = SNS-≡→SNS-PathP binaryFunIso (λ s t → compEquiv lem (nAryFunExtEquiv 2 s t))
    where
    lem : ∀ {X} → {s t : X → X → X} →
            ((x y : X) → s x y ≡ t x y) ≃
            ((xs : Vec X 2) → (s $ⁿ xs) ≡ (t $ⁿ map (λ x → x) xs))
    lem {X} {s} {t} = isoToEquiv f
      where
      f : Iso ((x y : X) → s x y ≡ t x y)
              ((xs : Vec X 2) → (s $ⁿ xs) ≡ (t $ⁿ map (λ x → x) xs))
      Iso.fun f p (x ∷ y ∷ [])           = p x y
      Iso.inv f p x y                    = p (x ∷ y ∷ [])
      Iso.rightInv f p _ xs@(x ∷ y ∷ []) = p xs
      Iso.leftInv f p _                  = p
