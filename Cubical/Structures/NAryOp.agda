{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.NAryOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.List

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ ℓ' ℓ'' : Level

nAryOp : ℕ → Type ℓ → Type ℓ
nAryOp zero X = X
nAryOp (suc n) X = X → nAryOp n X

nAryFunStructure : ℕ → Type (ℓ-suc ℓ)
nAryFunStructure {ℓ} n = TypeWithStr ℓ (nAryOp n)

-- We need vectors to define n-ary application

infixr 5 _∷_

data Vec (X : Type ℓ) : ℕ → Type ℓ where
  []  : Vec X zero
  _∷_ : ∀ {n} (x : X) (xs : Vec X n) → Vec X (suc n)

_$ⁿ_ : ∀ {X : Type ℓ} {n} → nAryOp n X → (Vec X n → X)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

map : ∀ {A : Type ℓ} {B : Type ℓ'} {n} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs


-- iso for n-ary functions
nAryFunIso : (n : ℕ) → StrIso (nAryOp n) ℓ
nAryFunIso n (X , fX) (Y , fY) f =
  (xs : Vec X n) → equivFun f (fX $ⁿ xs) ≡ (fY $ⁿ map (equivFun f) xs)

-- n-ary funext
nAryFunExt : (n : ℕ) {X : Type ℓ} (fX fY : nAryOp n X)
           → ((xs : Vec X n) → (fX $ⁿ xs) ≡ (fY $ⁿ map (λ x → x) xs))
           → fX ≡ fY
nAryFunExt zero fX fY p i = p [] i
nAryFunExt (suc n) fX fY p i x = nAryFunExt n (fX x) (fY x) (λ xs → p (x ∷ xs)) i

-- n-ary funext⁻
nAryFunExt⁻ : (n : ℕ) {X : Type ℓ} (fX fY : nAryOp n X) → fX ≡ fY
            → ((xs : Vec X n) → (fX $ⁿ xs) ≡ (fY $ⁿ map (λ x → x) xs))
nAryFunExt⁻ zero fX fY p [] = p
nAryFunExt⁻ (suc n) fX fY p (x ∷ xs) = nAryFunExt⁻ n (fX x) (fY x) (λ i → p i x) xs

nAryFunExtEquiv : (n : ℕ) {X : Type ℓ} (fX fY : nAryOp n X)
                → nAryFunIso n (X , fX) (X , fY) (idEquiv X) ≃ (fX ≡ fY)
nAryFunExtEquiv n {X} fX fY = isoToEquiv (iso (nAryFunExt n fX fY) (nAryFunExt⁻ n fX fY)
                                              (linv n fX fY) (rinv n fX fY))
  where
  linv : (n : ℕ) (fX fY : nAryOp n X) (p : fX ≡ fY)
       → nAryFunExt n fX fY (nAryFunExt⁻ n fX fY p) ≡ p
  linv zero fX fY p = refl
  linv (suc n) fX fY p i j x = linv n (fX x) (fY x) (λ k → p k x) i j

  rinv : (n : ℕ) (fX fY : nAryOp n X)
         (p : (xs : Vec X n) → (fX $ⁿ xs) ≡ (fY $ⁿ map (λ x → x) xs))
       → nAryFunExt⁻ n fX fY (nAryFunExt n fX fY p) ≡ p
  rinv zero fX fY p i [] = p []
  rinv (suc n) fX fY p i (x ∷ xs) = rinv n (fX x) (fY x) (λ ys i → p (x ∷ ys) i) i xs


nAry-is-SNS : (n : ℕ) → SNS {ℓ} _ (nAryFunIso n)
nAry-is-SNS n = SNS-≡→SNS-PathP (nAryFunIso n) (λ fX fY → nAryFunExtEquiv n fX fY)


-- Test


∞-magma-structure' : Type ℓ → Type ℓ
∞-magma-structure' X = nAryOp 2 X

∞-Magma' : Type (ℓ-suc ℓ)
∞-Magma' {ℓ} = TypeWithStr ℓ ∞-magma-structure'

∞-magma-iso' : StrIso ∞-magma-structure' ℓ
∞-magma-iso' = nAryFunIso 2

∞-magma-is-SNS' : SNS {ℓ} ∞-magma-structure' ∞-magma-iso'
∞-magma-is-SNS' = nAry-is-SNS 2


∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ} = TypeWithStr ℓ ∞-magma-structure

∞-magma-iso : StrIso ∞-magma-structure ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f =
  (x x' : X) → equivFun f (x · x') ≡ equivFun f x ∗ equivFun f x'

∞-magma-is-SNS : SNS {ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS = SNS-≡→SNS-PathP ∞-magma-iso (λ _ _ → funExt₂Equiv)

test1 : (X : Type ℓ) → ∞-magma-structure' X ≡ ∞-magma-structure X
test1 X = refl

test2 : ∞-Magma' {ℓ} ≡ ∞-Magma
test2 = refl

-- Not refl, but can be proved using currying
-- test3 : ∞-magma-iso' {ℓ} ≡ ∞-magma-iso
-- test3 i (X , fX) (Y , fY) f = {!!}
