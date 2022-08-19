{-

This file contains:

- Some cases of internal cubical subtypes;

- Cubes with a pair of fixed constant opposite faces is equivalent to cubes in the path type;

- Every cubes can be deformed to have (a pair of) fixed constant opposite faces,
  and this procedure gives an equivalence.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.Subtypes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Univalence.Dependent
open import Cubical.Foundations.Cubes.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ : Level
    A : Type ℓ


{-

  Cubical Subtypes

-}


-- Cubes with a pair of specified opposite faces

Cube∂₀₁ : (n : ℕ)(A : Type ℓ) → (a₀ a₁ : Cube n A) → Type ℓ
Cube∂₀₁ 0 A a₀ a₁ = a₀ ≡ a₁
Cube∂₀₁ (suc n) A a₀ a₁ = Σ[ ∂₋ ∈ a₀ .fst ≡ a₁ .fst ] CubeRel (suc (suc n)) A (a₀ , a₁ , ∂₋)

∂Cube∂₀₁ : (n : ℕ)(A : Type ℓ) → (a₀ a₁ : Cube n A) → Type ℓ
∂Cube∂₀₁ 0 A a₀ a₁ = Unit*
∂Cube∂₀₁ (suc n) A a₀ a₁ = a₀ .fst ≡ a₁ .fst

∂Cube∂₀₁→∂Cube : {n : ℕ}{A : Type ℓ}{a₀ a₁ : Cube n A} → ∂Cube∂₀₁ n A a₀ a₁ → ∂Cube (suc n) A
∂Cube∂₀₁→∂Cube {n = 0} {a₀ = a₀} {a₁} _ = a₀ , a₁
∂Cube∂₀₁→∂Cube {n = suc n} {a₀ = a₀} {a₁} ∂₋ = a₀ , a₁ , ∂₋

CubeRel∂₀₁ : (n : ℕ)(A : Type ℓ){a₀ a₁ : Cube n A} → ∂Cube∂₀₁ n A a₀ a₁ → Type ℓ
CubeRel∂₀₁ n A ∂₀₁ = CubeRel (suc n) A (∂Cube∂₀₁→∂Cube ∂₀₁)


-- Basic operations

Cube∂₀₁→Cube : {n : ℕ}{A : Type ℓ}{a₀ a₁ : Cube n A} → Cube∂₀₁ n A a₀ a₁ → Cube (suc n) A
Cube∂₀₁→Cube {n = 0} p = _ , p
Cube∂₀₁→Cube {n = suc n} (_ , cube) = _ , cube

Cube→Cube∂₀₁ : {n : ℕ}{A : Type ℓ} → (cube : Cube (suc n) A) → Cube∂₀₁ n A (∂₀ cube) (∂₁ cube)
Cube→Cube∂₀₁ {n = 0} (_ , p) = p
Cube→Cube∂₀₁ {n = suc n} (_ , cube) = _ , cube

∂₀₁ : {n : ℕ}{A : Type ℓ}{a₀ a₁ : Cube n A} → Cube∂₀₁ n A a₀ a₁ → ∂Cube∂₀₁ n A a₀ a₁
∂₀₁ {n = 0} p = tt*
∂₀₁ {n = suc n} (p , _) = p

∂Cube→∂Cube∂₀₁ : {n : ℕ}{A : Type ℓ} → (a : ∂Cube (suc n) A) → ∂Cube∂₀₁ n A (∂ᵇ₀ a) (∂ᵇ₁ a)
∂Cube→∂Cube∂₀₁ {n = 0} _ = tt*
∂Cube→∂Cube∂₀₁ {n = suc n} (a₀ , a₁ , ∂₋) = ∂₋


-- Cubes with a pair of specified constant opposite faces

∂Cube₀₁ : (n : ℕ)(A : Type ℓ) → (a₀ a₁ : A) → Type ℓ
∂Cube₀₁ n A a₀ a₁ = ∂Cube∂₀₁ n A (const _ a₀) (const _ a₁)

CubeRel₀₁ : (n : ℕ)(A : Type ℓ){a₀ a₁ : A} → ∂Cube₀₁ n A a₀ a₁ → Type ℓ
CubeRel₀₁ n A ∂ = CubeRel∂₀₁ n A ∂

Cube₀₁ : (n : ℕ)(A : Type ℓ) → Type ℓ
Cube₀₁ n A = Σ[ a₀ ∈ A ] Σ[ a₁ ∈ A ] Σ[ ∂ ∈ ∂Cube₀₁ n A a₀ a₁ ] (CubeRel₀₁ n A ∂)



{-

  The equivalence of cubes with fixed constant opposite faces and cubes in the path type

-}


interleaved mutual

  ∂Cube₀₁→∂CubePath :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
    → ∂Cube₀₁ n A a₀ a₁ → ∂Cube n (a₀ ≡ a₁)

  CubeRel₀₁→CubeRelPath :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}{∂₀₁ : ∂Cube₀₁ n A a₀ a₁}
    → CubeRel₀₁ n A ∂₀₁ → CubeRel n (a₀ ≡ a₁) (∂Cube₀₁→∂CubePath ∂₀₁)

  ∂Cube₀₁→∂CubePath {n = 0} _ = tt*
  ∂Cube₀₁→∂CubePath {n = 1} p = cong fst p , cong snd p
  ∂Cube₀₁→∂CubePath {n = suc (suc n)} {A} {a₀} {a₁} ∂₀₁ =
    (_ , CubeRel₀₁→CubeRelPath (λ i → ∂₀₁ i .fst .snd)) ,
    (_ , CubeRel₀₁→CubeRelPath (λ i → ∂₀₁ i .snd .fst .snd)) ,
    λ i → ∂Cube₀₁→∂CubePath (λ j → ∂₀₁ j .snd .snd i)

  CubeRel₀₁→CubeRelPath {n = 0} p = p
  CubeRel₀₁→CubeRelPath {n = 1} a₋ i j = a₋ j i
  CubeRel₀₁→CubeRelPath {n = suc (suc n)} {A} {a₀} {a₁} a₋ i =
    CubeRel₀₁→CubeRelPath (λ j → a₋ j i)


interleaved mutual

  ∂CubePath→∂Cube₀₁ :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
    → ∂Cube n (a₀ ≡ a₁) → ∂Cube₀₁ n A a₀ a₁

  CubeRelPath→CubeRel₀₁ :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}{∂ : ∂Cube n (a₀ ≡ a₁)}
    → CubeRel n (a₀ ≡ a₁) ∂ → CubeRel₀₁ n A (∂CubePath→∂Cube₀₁ ∂)

  ∂CubePath→∂Cube₀₁ {n = 0} _ = tt*
  ∂CubePath→∂Cube₀₁ {n = 1} (p , q) i = p i , q i
  ∂CubePath→∂Cube₀₁ {n = suc (suc n)} (a₀ , a₁ , ∂₋) i =
    (_ , CubeRelPath→CubeRel₀₁ (a₀ .snd) i) ,
    (_ , CubeRelPath→CubeRel₀₁ (a₁ .snd) i) ,
    λ j → ∂CubePath→∂Cube₀₁ (∂₋ j) i

  CubeRelPath→CubeRel₀₁ {n = 0} p = p
  CubeRelPath→CubeRel₀₁ {n = 1} a₋ i j = a₋ j i
  CubeRelPath→CubeRel₀₁ {n = suc (suc n)} a₋ i j = CubeRelPath→CubeRel₀₁ (a₋ j) i


interleaved mutual

  ∂Cube₀₁→∂CubePath→∂Cube₀₁ :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
    (∂₀₁ : ∂Cube₀₁ n A a₀ a₁)
    → ∂CubePath→∂Cube₀₁ (∂Cube₀₁→∂CubePath ∂₀₁) ≡ ∂₀₁

  CubeRel₀₁→CubeRelPath→CubeRel₀₁ :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}{∂₀₁ : ∂Cube₀₁ n A a₀ a₁}
    (a₋ : CubeRel₀₁ n A ∂₀₁)
    → PathP (λ i → CubeRel₀₁ n A (∂Cube₀₁→∂CubePath→∂Cube₀₁ ∂₀₁ i))
      (CubeRelPath→CubeRel₀₁ {n = n} (CubeRel₀₁→CubeRelPath a₋)) a₋

  ∂Cube₀₁→∂CubePath→∂Cube₀₁ {n = 0} _ = refl
  ∂Cube₀₁→∂CubePath→∂Cube₀₁ {n = 1} _ = refl
  ∂Cube₀₁→∂CubePath→∂Cube₀₁ {n = suc (suc n)} ∂₀₁ i j =
    (_ , CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = suc n} (λ i → ∂₀₁ i .fst .snd) i j) ,
    (_ , CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = suc n} (λ i → ∂₀₁ i .snd .fst .snd) i j) ,
    λ t → ∂Cube₀₁→∂CubePath→∂Cube₀₁ {n = suc n} (λ j → ∂₀₁ j .snd .snd t) i j

  CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = 0} _ = refl
  CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = 1} _ = refl
  CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = suc (suc n)} a₋ i j k =
    CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = suc n} (λ j → a₋ j k) i j


interleaved mutual

  ∂CubePath→∂Cube₀₁→∂CubePath :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
    (∂ : ∂Cube n (a₀ ≡ a₁))
    → ∂Cube₀₁→∂CubePath (∂CubePath→∂Cube₀₁ ∂) ≡ ∂

  CubeRelPath→CubeRel₀₁→CubeRelPath :
    {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}{∂ : ∂Cube n (a₀ ≡ a₁)}
    (a₋ : CubeRel n (a₀ ≡ a₁) ∂)
    → PathP (λ i → CubeRel n (a₀ ≡ a₁) (∂CubePath→∂Cube₀₁→∂CubePath ∂ i))
      (CubeRel₀₁→CubeRelPath {n = n} (CubeRelPath→CubeRel₀₁ a₋)) a₋

  ∂CubePath→∂Cube₀₁→∂CubePath {n = 0} _ = refl
  ∂CubePath→∂Cube₀₁→∂CubePath {n = 1} _ = refl
  ∂CubePath→∂Cube₀₁→∂CubePath {n = suc (suc n)} (a₀ , a₁ , ∂₋) i =
    (_ , CubeRelPath→CubeRel₀₁→CubeRelPath (a₀ .snd) i) ,
    (_ , CubeRelPath→CubeRel₀₁→CubeRelPath (a₁ .snd) i) ,
    λ t → ∂CubePath→∂Cube₀₁→∂CubePath {n = suc n} (∂₋ t) i

  CubeRelPath→CubeRel₀₁→CubeRelPath {n = 0} _ = refl
  CubeRelPath→CubeRel₀₁→CubeRelPath {n = 1} _ = refl
  CubeRelPath→CubeRel₀₁→CubeRelPath {n = suc (suc n)} a₋ i j =
    CubeRelPath→CubeRel₀₁→CubeRelPath {n = suc n} (a₋ j) i


open isHAEquiv hiding (g)

Iso-∂Cube₀₁-∂CubePath : {n : ℕ}{A : Type ℓ}{a₀ a₁ : A} → Iso (∂Cube₀₁ n A a₀ a₁) (∂Cube n (a₀ ≡ a₁))
Iso-∂Cube₀₁-∂CubePath =
  iso ∂Cube₀₁→∂CubePath ∂CubePath→∂Cube₀₁ ∂CubePath→∂Cube₀₁→∂CubePath ∂Cube₀₁→∂CubePath→∂Cube₀₁

-- The iso defined above seems automatically half-adjoint,
-- but I don't want to write more crazy paths...

HAEquiv-∂Cube₀₁-∂CubePath : {n : ℕ}{A : Type ℓ}{a₀ a₁ : A} → HAEquiv (∂Cube₀₁ n A a₀ a₁) (∂Cube n (a₀ ≡ a₁))
HAEquiv-∂Cube₀₁-∂CubePath = iso→HAEquiv Iso-∂Cube₀₁-∂CubePath

IsoOver-CubeRel₀₁-CubeRelPath : {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
  → IsoOver Iso-∂Cube₀₁-∂CubePath (CubeRel₀₁ n A) (CubeRel n (a₀ ≡ a₁))
IsoOver-CubeRel₀₁-CubeRelPath {n = n} =
  isoover (λ _ → CubeRel₀₁→CubeRelPath) (λ _ → CubeRelPath→CubeRel₀₁)
    (λ _ → CubeRelPath→CubeRel₀₁→CubeRelPath) (λ _ → CubeRel₀₁→CubeRelPath→CubeRel₀₁ {n = n})

∂Cube₀₁≡∂CubePath : {n : ℕ}{A : Type ℓ}{a₀ a₁ : A} → ∂Cube₀₁ n A a₀ a₁ ≡ ∂Cube n (a₀ ≡ a₁)
∂Cube₀₁≡∂CubePath = ua (_ , isHAEquiv→isEquiv (HAEquiv-∂Cube₀₁-∂CubePath .snd))

CubeRel₀₁≡CubeRelPath : {n : ℕ}{A : Type ℓ}{a₀ a₁ : A}
  → PathP (λ i → ∂Cube₀₁≡∂CubePath {n = n} {A} {a₀} {a₁} i → Type ℓ) (CubeRel₀₁ n A) (CubeRel n (a₀ ≡ a₁))
CubeRel₀₁≡CubeRelPath = isoToPathOver _ _ (iso→HAEquivOver IsoOver-CubeRel₀₁-CubeRelPath)




{-

  All cubes can be deformed to cubes with fixed constant opposite faces

-}


-- Cubes with a pair of fixed constant opposite faces

∂CubeConst₀₁ : (n : ℕ)(A : Type ℓ) → Type ℓ
∂CubeConst₀₁ 0 A = A × A
∂CubeConst₀₁ (suc n) A = Σ[ a₀ ∈ A ] Σ[ a₁ ∈ A ] ∂Cube₀₁ (suc n) A a₀ a₁

CubeRelConst₀₁ : (n : ℕ)(A : Type ℓ) → ∂CubeConst₀₁ n A → Type ℓ
CubeRelConst₀₁ 0 A (a₀ , a₁) = a₀ ≡ a₁
CubeRelConst₀₁ (suc n) A ∂₀₁ = CubeRel₀₁ (suc n) A (∂₀₁ .snd .snd)


-- The equivalence between fixed/not-fixed-faces cubes


-- Some preliminary lemmas
private

  path1 : (n : ℕ) → ∂Cube (suc (suc n)) A → I → ∂Cube (suc (suc n)) A
  path1 {A = A} n (a₀ , a₁ , ∂₋) i =
    const₀ .snd i , const₁ .snd i ,
    transport-filler (λ i → ∂Cube∂₀₁ (suc n) A (const₀ .snd i) (const₁ .snd i)) ∂₋ i
    where
    const₀ = makeConst {n = suc n} a₀
    const₁ = makeConst {n = suc n} a₁

  square1 : (n : ℕ) → ∂CubeConst₀₁ (suc n) A → I → I → ∂CubeConst₀₁ (suc n) A
  square1 {A = A} n (a₀ , a₁ , ∂₋) i j =
    _ , _ ,
    hfill (λ j → λ
      { (i = i0) → transport (λ t → ∂Cube∂₀₁ (suc n) A (cu₀ i0 .snd t) (cu₁ i0 .snd t)) ∂₋
      ; (i = i1) → transportRefl ∂₋ j })
    (inS (transport (λ t → ∂Cube∂₀₁ (suc n) A (cu₀ i .snd t) (cu₁ i .snd t)) ∂₋)) j
    where
    cu₀ = makeConstUniq {n = suc n} a₀
    cu₁ = makeConstUniq {n = suc n} a₁


∂CubeConst₀₁→∂Cube : {n : ℕ}{A : Type ℓ} → ∂CubeConst₀₁ n A → ∂Cube (suc n) A
∂CubeConst₀₁→∂Cube {n = 0} x = x
∂CubeConst₀₁→∂Cube {n = suc n} (a₀ , a₁ , ∂₋) = const _ a₀ , const _ a₁ , ∂₋

∂Cube→∂CubeConst₀₁ : {n : ℕ}{A : Type ℓ} → ∂Cube (suc n) A → ∂CubeConst₀₁ n A
∂Cube→∂CubeConst₀₁ {n = 0} (a₀ , a₁) = a₀ , a₁
∂Cube→∂CubeConst₀₁ {n = suc n} ∂ = _ , _ , path1 n ∂ i1 .snd .snd

∂Cube→∂CubeConst₀₁→∂Cube : {n : ℕ}{A : Type ℓ}
  → (∂ : ∂Cube (suc n) A) → ∂CubeConst₀₁→∂Cube (∂Cube→∂CubeConst₀₁ ∂) ≡ ∂
∂Cube→∂CubeConst₀₁→∂Cube {n = 0} _ = refl
∂Cube→∂CubeConst₀₁→∂Cube {n = suc n} ∂₀₁ i = path1 n ∂₀₁ (~ i)

∂CubeConst₀₁→∂Cube→∂CubeConst₀₁ : {n : ℕ}{A : Type ℓ}
  → (∂₀₁ : ∂CubeConst₀₁ n A) → ∂Cube→∂CubeConst₀₁ (∂CubeConst₀₁→∂Cube ∂₀₁) ≡ ∂₀₁
∂CubeConst₀₁→∂Cube→∂CubeConst₀₁ {n = 0} _ = refl
∂CubeConst₀₁→∂Cube→∂CubeConst₀₁ {n = suc n} ∂₀₁ i = square1 n ∂₀₁ i i1


-- Some preliminary lemmas
private

  path2 : (n : ℕ) {∂ : ∂Cube (suc (suc n)) A}
    → (a₋ : CubeRel (suc (suc n)) A ∂)
    → (i : I) → CubeRel (suc (suc n)) A (path1 n ∂ i)
  path2 {A = A} n {∂} a₋ i =
    transport-filler (λ i → CubeRel (suc (suc n)) A (path1 n ∂ i)) a₋ i


CubeRelConst₀₁→CubeRel : {n : ℕ}{A : Type ℓ}
  → (∂₀₁ : ∂CubeConst₀₁ n A) → CubeRelConst₀₁ n A ∂₀₁ → CubeRel (suc n) A (∂CubeConst₀₁→∂Cube ∂₀₁)
CubeRelConst₀₁→CubeRel {n = 0} _ p = p
CubeRelConst₀₁→CubeRel {n = suc n} _ a₋ = a₋

CubeRel→CubeRelConst₀₁ : {n : ℕ}{A : Type ℓ}
  → (∂ : ∂Cube (suc n) A) → CubeRel (suc n) A ∂ → CubeRelConst₀₁ n A (∂Cube→∂CubeConst₀₁ ∂)
CubeRel→CubeRelConst₀₁ {n = 0} _ p = p
CubeRel→CubeRelConst₀₁ {n = suc n} _ a₋ = path2 n a₋ i1

CubeRel→CubeRelConst₀₁→CubeRel : {n : ℕ} {A : Type ℓ}
  → (∂ : ∂Cube (suc n) A) (a : CubeRel (suc n) A ∂)
  → PathP (λ i → CubeRel (suc n) A (∂Cube→∂CubeConst₀₁→∂Cube ∂ i))
    (CubeRelConst₀₁→CubeRel (∂Cube→∂CubeConst₀₁ ∂) (CubeRel→CubeRelConst₀₁ ∂ a)) a
CubeRel→CubeRelConst₀₁→CubeRel {n = 0} _ _ = refl
CubeRel→CubeRelConst₀₁→CubeRel {n = suc n} _ a₋ i = path2 n a₋ (~ i)

CubeRelConst₀₁→CubeRel→CubeRelConst₀₁ : {n : ℕ} {A : Type ℓ}
  → (∂₀₁ : ∂CubeConst₀₁ n A) (a : CubeRelConst₀₁ n A ∂₀₁)
  → PathP (λ i → CubeRelConst₀₁ n A (∂CubeConst₀₁→∂Cube→∂CubeConst₀₁ ∂₀₁ i))
    (CubeRel→CubeRelConst₀₁ (∂CubeConst₀₁→∂Cube ∂₀₁) (CubeRelConst₀₁→CubeRel ∂₀₁ a)) a
CubeRelConst₀₁→CubeRel→CubeRelConst₀₁ {n = 0} _ _ = refl
CubeRelConst₀₁→CubeRel→CubeRelConst₀₁ {n = suc n} {A} ∂₀₁@(a₀ , a₁ , ∂₋) a₋ i =
  comp (λ j → CubeRelConst₀₁ (suc n) A (square1 n ∂₀₁ i j))
  (λ j → λ
    { (i = i0) → path i0
    ; (i = i1) → tp-refl j })
  (path i)
  where
  cu₀ = makeConstUniq {n = suc n} a₀
  cu₁ = makeConstUniq {n = suc n} a₁

  ∂path : (i t : I) → ∂Cube∂₀₁ (suc n) A (cu₀ i .snd t) (cu₁ i .snd t)
  ∂path i t = transport-filler (λ t → ∂Cube∂₀₁ (suc n) A (cu₀ i .snd t) (cu₁ i .snd t)) ∂₋ t

  path : (i : I) → CubeRel (suc (suc n)) A (cu₀ i .snd i1 , cu₁ i .snd i1 , ∂path i i1)
  path i = transport (λ t → CubeRel (suc (suc n)) A (cu₀ i .snd t , cu₁ i .snd t , ∂path i t)) a₋

  tp-refl : PathP (λ i → CubeRelConst₀₁ (suc n) A (_ , _ , transportRefl ∂₋ i)) (path i1) a₋
  tp-refl i = transport-filler (λ t → CubeRel (suc (suc n)) A (const _ a₀ , const _ a₁ , ∂path i1 t)) a₋ (~ i)


Iso-∂CubeConst₀₁-∂Cube : {n : ℕ}{A : Type ℓ} → Iso (∂CubeConst₀₁ n A) (∂Cube (suc n) A)
Iso-∂CubeConst₀₁-∂Cube =
  iso ∂CubeConst₀₁→∂Cube ∂Cube→∂CubeConst₀₁ ∂Cube→∂CubeConst₀₁→∂Cube ∂CubeConst₀₁→∂Cube→∂CubeConst₀₁

-- The iso defined above seems automatically half-adjoint,
-- but I don't want to write more crazy paths...

HAEquiv-∂CubeConst₀₁-∂Cube : {n : ℕ}{A : Type ℓ} → HAEquiv (∂CubeConst₀₁ n A) (∂Cube (suc n) A)
HAEquiv-∂CubeConst₀₁-∂Cube = iso→HAEquiv Iso-∂CubeConst₀₁-∂Cube

IsoOver-CubeRelConst₀₁-CubeRel₀₁ : {n : ℕ}{A : Type ℓ}
  → IsoOver Iso-∂CubeConst₀₁-∂Cube (CubeRelConst₀₁ n A) (CubeRel (suc n) A)
IsoOver-CubeRelConst₀₁-CubeRel₀₁ =
  isoover CubeRelConst₀₁→CubeRel CubeRel→CubeRelConst₀₁
    CubeRel→CubeRelConst₀₁→CubeRel CubeRelConst₀₁→CubeRel→CubeRelConst₀₁

∂CubeConst₀₁≡∂Cube : {n : ℕ}{A : Type ℓ} → ∂CubeConst₀₁ n A ≡ ∂Cube (suc n) A
∂CubeConst₀₁≡∂Cube =
  ua (_ , isHAEquiv→isEquiv (HAEquiv-∂CubeConst₀₁-∂Cube .snd))

CubeRelConst₀₁≡CubeRel₀₁ : {n : ℕ}{A : Type ℓ}
  → PathP (λ i → ∂CubeConst₀₁≡∂Cube {n = n} i → Type ℓ) (CubeRelConst₀₁ n A) (CubeRel (suc n) A)
CubeRelConst₀₁≡CubeRel₀₁ =
  isoToPathOver _ _ (iso→HAEquivOver IsoOver-CubeRelConst₀₁-CubeRel₀₁)
