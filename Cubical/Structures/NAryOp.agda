{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.NAryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.Vec

module _ {ℓ₁ ℓ₂ : Level} where

  nAryFun-structure : (n : ℕ) (S : Type ℓ₁ → Type ℓ₂)
    → Type ℓ₁ → Type (nAryLevel ℓ₁ ℓ₂ n)
  nAryFun-structure n S X = nAryOp n X (S X)

  -- iso for n-ary functions
  nAryFunIso : (n : ℕ) {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrIso S ℓ₃)
    → StrIso (nAryFun-structure n S) (ℓ-max ℓ₁ ℓ₃)
  nAryFunIso n ι (X , fX) (Y , fY) e =
    (xs : Vec X n) → ι (X , fX $ⁿ xs) (Y , fY $ⁿ map (equivFun e) xs) e


  nAryFunSNS : {S : Type ℓ₁ → Type ℓ₂} (n : ℕ) {ℓ₃ : Level}
    (ι : StrIso S ℓ₃) (θ : SNS S ι)
    → SNS (nAryFun-structure n S) (nAryFunIso n ι)
  nAryFunSNS n ι θ =
    SNS-≡→SNS-PathP (nAryFunIso n ι) λ fX fY →
    compEquiv
      (equivPi λ xs → SNS-PathP→SNS-≡ _ ι θ _ _)
      (nAryFunExtEquiv n fX fY)

module _ {ℓ₁ ℓ₂ : Level} where
  -- unary
  unaryFunIso : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrIso S ℓ₃)
    → StrIso (nAryFun-structure 1 S) (ℓ-max ℓ₁ ℓ₃)
  unaryFunIso ι (A , f) (B , g) e =
    (x : A) → ι (A , f x) (B , g (equivFun e x)) e

  unaryFunSNS : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : StrIso S ℓ₃) (θ : SNS S ι)
    → SNS (nAryFun-structure 1 S) (unaryFunIso ι)
  unaryFunSNS ι θ =
    SNS-≡→SNS-PathP (unaryFunIso ι) λ fX fY →
    compEquiv (equivPi λ _ → SNS-PathP→SNS-≡ _ ι θ _ _) funExtEquiv

  -- binary
  binaryFunIso : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrIso S ℓ₃)
    → StrIso (nAryFun-structure 2 S) (ℓ-max ℓ₁ ℓ₃)
  binaryFunIso ι (A , f) (B , g) e =
    (x y : A) → ι (A , f x y) (B , g (equivFun e x) (equivFun e y)) e

  binaryFunSNS : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : StrIso S ℓ₃) (θ : SNS S ι)
    → SNS (nAryFun-structure 2 S) (binaryFunIso ι)
  binaryFunSNS ι θ =
    SNS-≡→SNS-PathP (binaryFunIso ι) λ fX fY →
    compEquiv (equivPi λ _ → equivPi λ _ → SNS-PathP→SNS-≡ _ ι θ _ _) funExt₂Equiv
