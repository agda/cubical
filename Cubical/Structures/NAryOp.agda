{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.NAryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.Vec

module _ {ℓ₁ ℓ₂ : Level} where

  NAryFunStructure : (n : ℕ) (S : Type ℓ₁ → Type ℓ₂)
    → Type ℓ₁ → Type (nAryLevel ℓ₁ ℓ₂ n)
  NAryFunStructure n S X = nAryOp n X (S X)

  -- iso for n-ary functions
  NAryFunEquivStr : (n : ℕ) {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrEquiv S ℓ₃)
    → StrEquiv (NAryFunStructure n S) (ℓ-max ℓ₁ ℓ₃)
  NAryFunEquivStr n ι (X , fX) (Y , fY) e =
    (xs : Vec X n) → ι (X , fX $ⁿ xs) (Y , fY $ⁿ map (equivFun e) xs) e

  nAryFunUnivalentStr : {S : Type ℓ₁ → Type ℓ₂} (n : ℕ) {ℓ₃ : Level}
    (ι : StrEquiv S ℓ₃) (θ : UnivalentStr S ι)
    → UnivalentStr (NAryFunStructure n S) (NAryFunEquivStr n ι)
  nAryFunUnivalentStr n ι θ =
    SNS→UnivalentStr (NAryFunEquivStr n ι) λ fX fY →
    compEquiv
      (equivPi λ xs → UnivalentStr→SNS _ ι θ _ _)
      (nAryFunExtEquiv n fX fY)

module _ {ℓ₁ ℓ₂ : Level} where

  -- unary
  UnaryFunEquivStr : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrEquiv S ℓ₃)
    → StrEquiv (NAryFunStructure 1 S) (ℓ-max ℓ₁ ℓ₃)
  UnaryFunEquivStr ι (A , f) (B , g) e =
    (x : A) → ι (A , f x) (B , g (equivFun e x)) e

  unaryFunUnivalentStr : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : StrEquiv S ℓ₃) (θ : UnivalentStr S ι)
    → UnivalentStr (NAryFunStructure 1 S) (UnaryFunEquivStr ι)
  unaryFunUnivalentStr ι θ =
    SNS→UnivalentStr (UnaryFunEquivStr ι) λ fX fY →
    compEquiv (equivPi λ _ → UnivalentStr→SNS _ ι θ _ _) funExtEquiv

  -- binary
  BinaryFunEquivStr : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level} (ι : StrEquiv S ℓ₃)
    → StrEquiv (NAryFunStructure 2 S) (ℓ-max ℓ₁ ℓ₃)
  BinaryFunEquivStr ι (A , f) (B , g) e =
    (x y : A) → ι (A , f x y) (B , g (equivFun e x) (equivFun e y)) e

  binaryFunUnivalentStr : {S : Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : StrEquiv S ℓ₃) (θ : UnivalentStr S ι)
    → UnivalentStr (NAryFunStructure 2 S) (BinaryFunEquivStr ι)
  binaryFunUnivalentStr ι θ =
    SNS→UnivalentStr (BinaryFunEquivStr ι) λ fX fY →
    compEquiv (equivPi λ _ → equivPi λ _ → UnivalentStr→SNS _ ι θ _ _) funExt₂Equiv
