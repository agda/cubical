{-

This file contains:

- The definition of the type of n-cubes;

- Some basic operations.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.Base where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ


-- The Type of n-Cubes

-- P.S.
-- Only the definitions of `∂Cube` and `CubeRel` essentially use mutual recursion.
-- The case of `Cube` is designed to gain more definitional equality.

interleaved mutual

  Cube    : (n : ℕ) (A : Type ℓ) → Type ℓ
  ∂Cube₀₁ : (n : ℕ) (A : Type ℓ) (a₀ a₁ : Cube n A) → Type ℓ
  ∂Cube   : (n : ℕ) (A : Type ℓ) → Type ℓ
  CubeRel : (n : ℕ) (A : Type ℓ) → ∂Cube n A → Type ℓ

  Cube    0 A = A
  Cube    (suc n) A = Σ[ ∂ ∈ ∂Cube (suc n) A ] CubeRel (suc n) A ∂

  ∂Cube₀₁ 0 A _ _ = Unit*
  ∂Cube₀₁ (suc n) A a₀ a₁ = a₀ .fst ≡ a₁ .fst

  ∂Cube   0 A = Unit*
  ∂Cube   1 A = A × A
  ∂Cube   (suc (suc n)) A = Σ[ a₀ ∈ Cube (suc n) A ] Σ[ a₁ ∈ Cube (suc n) A ] ∂Cube₀₁ (suc n) A a₀ a₁

  CubeRel 0 A _ = A
  CubeRel 1 A ∂ = ∂ .fst ≡ ∂ .snd
  CubeRel (suc (suc n)) A (a₀ , a₁ , ∂₋) = PathP (λ i → CubeRel (suc n) A (∂₋ i)) (a₀ .snd) (a₁ .snd)


-- Some basic operations

∂_ : {n : ℕ}{A : Type ℓ} → Cube n A → ∂Cube n A
∂_ {n = 0} _ = tt*
∂_ {n = suc n} = fst

∂₀ : {n : ℕ}{A : Type ℓ} → Cube (suc n) A → Cube n A
∂₀ {n = 0} (_ , p) = p i0
∂₀ {n = suc n} (_ , p) = _ , p i0

∂₁ : {n : ℕ}{A : Type ℓ} → Cube (suc n) A → Cube n A
∂₁ {n = 0} (_ , p) = p i1
∂₁ {n = suc n} (_ , p) = _ , p i1

∂ᵇ₀ : {n : ℕ}{A : Type ℓ} → ∂Cube (suc n) A → Cube n A
∂ᵇ₀ {n = 0} (a₀ , a₁) = a₀
∂ᵇ₀ {n = suc n} (a₀ , a₁ , ∂₋) = a₀

∂ᵇ₁ : {n : ℕ}{A : Type ℓ} → ∂Cube (suc n) A → Cube n A
∂ᵇ₁ {n = 0} (a₀ , a₁) = a₁
∂ᵇ₁ {n = suc n} (a₀ , a₁ , ∂₋) = a₁


make∂ : {n : ℕ}{A : Type ℓ}{∂₀ ∂₁ : ∂Cube n A} → ∂₀ ≡ ∂₁ → CubeRel n A ∂₀ → CubeRel n A ∂₁ → ∂Cube (suc n) A
make∂ {n = 0} _ a b = a , b
make∂ {n = suc n} ∂₋ a₀ a₁ = (_ , a₀) , (_ , a₁) , ∂₋

makeCube : {n : ℕ}{A : Type ℓ}{a₀ a₁ : Cube n A} → a₀ ≡ a₁ → Cube (suc n) A
makeCube {n = 0} a₋ = _ , a₋
makeCube {n = suc n} a₋ = _ , λ i → a₋ i .snd

-- A cube is just a path of cubes of one-lower-dimension.
-- Unfortunately the following function cannot begin at 0,
-- because Agda doesn't support pattern matching on ℕ towards pre-types.
-- P.S. It will be fixed in Agda 2.6.3 when I → A becomes fibrant.
pathCube : (n : ℕ) → (I → Cube (suc n) A) → Cube (suc (suc n)) A
pathCube n p = _ , λ i → p i .snd


∂Cube₀₁→∂Cube : {n : ℕ}{A : Type ℓ}{a₀ a₁ : Cube n A} → ∂Cube₀₁ n A a₀ a₁ → ∂Cube (suc n) A
∂Cube₀₁→∂Cube {n = 0} {a₀ = a₀} {a₁} _ = a₀ , a₁
∂Cube₀₁→∂Cube {n = suc n} {a₀ = a₀} {a₁} ∂ = a₀ , a₁ , ∂

CubeRel→Cube : {n : ℕ}{A : Type ℓ}{∂ : ∂Cube n A} → CubeRel n A ∂ → Cube n A
CubeRel→Cube {n = 0} a = a
CubeRel→Cube {n = suc n} cube = _ , cube


-- Composition of internal cubes, with specified boundary

hcomp∂ :
  {n : ℕ} {A : Type ℓ}
  {∂₀ ∂₁ : ∂Cube n A} (∂₋ : ∂₀ ≡ ∂₁)
  (a₀ : CubeRel n A ∂₀)
  → CubeRel n A ∂₁
hcomp∂ ∂₋ = transport (λ i → CubeRel _ _ (∂₋ i))

hfill∂ :
  {n : ℕ} {A : Type ℓ}
  {∂₀ ∂₁ : ∂Cube n A} (∂₋ : ∂₀ ≡ ∂₁)
  (a₀ : CubeRel n A ∂₀)
  → CubeRel (suc n) A (make∂ ∂₋ a₀ (hcomp∂ ∂₋ a₀))
hfill∂ {n = 0} ∂₋ a₀ i = transportRefl a₀ (~ i)
hfill∂ {n = suc n} ∂₋  = transport-filler (λ i → CubeRel _ _ (∂₋ i))


-- Constant path of n-cube as (n+1)-cube

constCube : {n : ℕ}{A : Type ℓ} → Cube n A → Cube (suc n) A
constCube {n = 0} a = _ , λ i → a
constCube {n = suc n} (∂ , cube) = _ , λ i → cube

retConst : {n : ℕ}{A : Type ℓ} → (cube : Cube n A) → ∂₀ (constCube {n = n} cube) ≡ cube
retConst {n = 0} _ = refl
retConst {n = suc n} _ = refl

secConst : {n : ℕ}{A : Type ℓ} → (cube : Cube (suc n) A) → constCube (∂₀ cube) ≡ cube
secConst {n = 0} (_ , p) i = _ , λ j → p (i ∧ j)
secConst {n = suc n} (_ , p) i  = _ , λ j → p (i ∧ j)

isEquivConstCube : {n : ℕ}{A : Type ℓ} → isEquiv (constCube {n = n} {A = A})
isEquivConstCube {n = n} = isoToEquiv (iso constCube ∂₀ secConst (retConst {n = n})) .snd


-- Constant cubes

const : (n : ℕ){A : Type ℓ} → A → Cube n A
const 0 a = a
const (suc n) a = constCube (const n a)

isEquivConst : {n : ℕ}{A : Type ℓ} → isEquiv (const n {A = A})
isEquivConst {n = 0} = idIsEquiv _
isEquivConst {n = suc n} = compEquiv (_ , isEquivConst) (_ , isEquivConstCube) .snd

cubeEquiv : {n : ℕ}{A : Type ℓ} → A ≃ Cube n A
cubeEquiv = _ , isEquivConst

makeConst : {n : ℕ}{A : Type ℓ} → (cube : Cube n A) → Σ[ a ∈ A ] cube ≡ const n a
makeConst {n = n} cube = invEq cubeEquiv cube , sym (secEq (cubeEquiv {n = n}) cube)

makeConstUniq : {n : ℕ}{A : Type ℓ} → (a : A) → makeConst (const n a) ≡ (a , refl)
makeConstUniq {n = n} a i .fst   = isEquivConst .equiv-proof (const n a) .snd (a , refl) i .fst
makeConstUniq {n = n} a i .snd j = isEquivConst .equiv-proof (const n a) .snd (a , refl) i .snd (~ j)


-- Cube with constant boundary

const∂ : (n : ℕ){A : Type ℓ} → A → ∂Cube n A
const∂ n a = ∂ (const n a)


-- J-rule for n-cubes,
-- in some sense a generalization of the usual (symmetric form of) J-rule,
-- which is equivalent to the case n=1.

module _ {n : ℕ} {A : Type ℓ}
  (P : Cube n A → Type ℓ') (d : (a : A) → P (const _ a)) where

  JCube : (a₋ : Cube n A) → P a₋
  JCube a₋ =
    let c-path = makeConst {n = n} a₋ in
    transport (λ i → P (c-path .snd (~ i))) (d (c-path .fst))

  JCubeβ : (a : A) → JCube (const _ a) ≡ d a
  JCubeβ a i =
    let c-square = makeConstUniq {n = n} a in
    let c-path = transport-filler (λ i → P (c-square i0 .snd (~ i))) (d (c-square i0 .fst)) in
    comp (λ j → P (c-square j .snd i))
    (λ j → λ
      { (i = i0) → c-path i1
      ; (i = i1) → d _ })
    (c-path (~ i))
