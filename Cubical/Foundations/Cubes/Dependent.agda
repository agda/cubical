{-

Cubes over Cubes

This file contains:

- The definition of the type of dependent n-cubes;

- Dependent cubes over a constant cube is equivalent to the (non-dependent) cubes in the fiber.

-}
module Cubical.Foundations.Cubes.Dependent where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
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
    ℓ ℓ' : Level
    n : ℕ
    A : Type ℓ


-- The Type of Dependent n-Cubes

interleaved mutual

  CubeDep    : {A : Type ℓ} (B : A → Type ℓ') →  Cube n A → Type ℓ'
  ∂CubeDep   : {A : Type ℓ} (B : A → Type ℓ') → ∂Cube n A → Type ℓ'
  CubeDepRel : {A : Type ℓ} {B : A → Type ℓ'} (a₋ : Cube n A) → ∂CubeDep {n = n} B (∂ a₋) → Type ℓ'

  CubeDep  {n = 0} B a = B a
  CubeDep  {n = suc n} B a₋ = Σ[ ∂b ∈ ∂CubeDep B (∂ a₋) ] CubeDepRel a₋ ∂b

  ∂CubeDep {n = 0} B _ = Unit*
  ∂CubeDep {n = 1} B (a₀ , a₁) = B a₀ × B a₁
  ∂CubeDep {n = suc (suc n)} B (a₀ , a₁ , ∂a₋) =
    Σ[ b₀ ∈ CubeDep B a₀ ] Σ[ b₁ ∈ CubeDep B a₁ ] PathP (λ i → ∂CubeDep B (∂a₋ i)) (b₀ .fst) (b₁ .fst)

  CubeDepRel {n = 0} {B = B} a _ = B a
  CubeDepRel {n = 1} {B = B} a₋ (b₀ , b₁) = PathP (λ i → B (a₋ .snd i)) b₀ b₁ --∂ .fst ≡ ∂ .snd
  CubeDepRel {n = suc (suc n)} a₋ (b₀ , b₁ , ∂₋) =
    PathP (λ i → CubeDepRel {n = suc n} (_ , a₋ .snd i) (∂₋ i)) (b₀ .snd) (b₁ .snd)


-- Cubes over constant cube

∂CubeDepConst : (n : ℕ) (B : A → Type ℓ') (a : A) → Type ℓ'
∂CubeDepConst n B a = ∂CubeDep {n = n} B (∂ (const n a))

CubeDepConstRel : {n : ℕ} {B : A → Type ℓ'} {a : A} → ∂CubeDepConst n B a → Type ℓ'
CubeDepConstRel {n = n} {a = a} ∂ = CubeDepRel {n = n} (const n a) ∂


-- The equivalence between cubes over constant cube and cubes in the fiber.

interleaved mutual

  ∂CubeDepConst→∂Cube : (n : ℕ) (B : A → Type ℓ') (a : A) → ∂CubeDepConst n B a → ∂Cube n (B a)

  CubeDepConstRel→CubeRel : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂CubeDepConst n B a) → CubeDepConstRel ∂ → CubeRel n (B a) (∂CubeDepConst→∂Cube n B a ∂)

  ∂CubeDepConst→∂Cube 0 B a b = b
  ∂CubeDepConst→∂Cube 1 B a (b₀ , b₁) = b₀ , b₁
  ∂CubeDepConst→∂Cube (suc (suc n)) B a (b₀ , b₁ , ∂b₋) =
    (_ , CubeDepConstRel→CubeRel (suc n) B a _ (b₀ .snd)) ,
    (_ , CubeDepConstRel→CubeRel (suc n) B a _ (b₁ .snd)) ,
    λ t → ∂CubeDepConst→∂Cube (suc n) B a (∂b₋ t)

  CubeDepConstRel→CubeRel 0 B a _ b  = b
  CubeDepConstRel→CubeRel 1 B a _ b₋ = b₋
  CubeDepConstRel→CubeRel (suc (suc n)) B a _ b₋ i =
    CubeDepConstRel→CubeRel (suc n) B a _ (b₋ i)


interleaved mutual

  ∂Cube→∂CubeDepConst : (n : ℕ) (B : A → Type ℓ') (a : A) → ∂Cube n (B a) → ∂CubeDepConst n B a

  CubeRel→CubeDepConstRel : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂Cube n (B a)) → CubeRel n (B a) ∂ → CubeDepConstRel (∂Cube→∂CubeDepConst n B a ∂)

  ∂Cube→∂CubeDepConst 0 B a b = b
  ∂Cube→∂CubeDepConst 1 B a (b₀ , b₁) = b₀ , b₁
  ∂Cube→∂CubeDepConst (suc (suc n)) B a (b₀ , b₁ , ∂b₋) =
    (_ , CubeRel→CubeDepConstRel (suc n) B a _ (b₀ .snd)) ,
    (_ , CubeRel→CubeDepConstRel (suc n) B a _ (b₁ .snd)) ,
    λ t → ∂Cube→∂CubeDepConst (suc n) B a (∂b₋ t)

  CubeRel→CubeDepConstRel 0 B a _ b  = b
  CubeRel→CubeDepConstRel 1 B a _ b₋ = b₋
  CubeRel→CubeDepConstRel (suc (suc n)) B a _ b₋ i =
    CubeRel→CubeDepConstRel (suc n) B a _ (b₋ i)


interleaved mutual

  ∂CubeDepConst→∂Cube→∂CubeDepConst : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂CubeDepConst n B a) → ∂Cube→∂CubeDepConst n B a (∂CubeDepConst→∂Cube n B a ∂) ≡ ∂

  CubeDepConstRel→CubeRel→CubeDepConstRel : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂CubeDepConst n B a) (b₋ : CubeDepConstRel ∂)
    → PathP (λ i → CubeDepConstRel (∂CubeDepConst→∂Cube→∂CubeDepConst n B a ∂ i))
      (CubeRel→CubeDepConstRel n B a _ (CubeDepConstRel→CubeRel n B a _ b₋)) b₋

  ∂CubeDepConst→∂Cube→∂CubeDepConst 0 B a _ = refl
  ∂CubeDepConst→∂Cube→∂CubeDepConst 1 B a _ = refl
  ∂CubeDepConst→∂Cube→∂CubeDepConst (suc (suc n)) B a (b₀ , b₁ , ∂b₋) i =
    (_ , CubeDepConstRel→CubeRel→CubeDepConstRel (suc n) B a _ (b₀ .snd) i) ,
    (_ , CubeDepConstRel→CubeRel→CubeDepConstRel (suc n) B a _ (b₁ .snd) i) ,
    λ t → ∂CubeDepConst→∂Cube→∂CubeDepConst (suc n) B a (∂b₋ t) i

  CubeDepConstRel→CubeRel→CubeDepConstRel 0 B a _ _ = refl
  CubeDepConstRel→CubeRel→CubeDepConstRel 1 B a _ _ = refl
  CubeDepConstRel→CubeRel→CubeDepConstRel (suc (suc n)) B a _ b₋ i j =
    CubeDepConstRel→CubeRel→CubeDepConstRel (suc n) B a _ (b₋ j) i


interleaved mutual

  ∂Cube→∂CubeDepConst→∂Cube : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂Cube n (B a)) →  ∂CubeDepConst→∂Cube n B a (∂Cube→∂CubeDepConst n B a ∂) ≡ ∂

  CubeRel→CubeDepConstRel→CubeDepConstRel : (n : ℕ) (B : A → Type ℓ') (a : A)
    → (∂ : ∂Cube n (B a)) (b₋ : CubeRel n (B a) ∂)
    → PathP (λ i → CubeRel n (B a) (∂Cube→∂CubeDepConst→∂Cube n B a ∂ i))
      (CubeDepConstRel→CubeRel n B a _ (CubeRel→CubeDepConstRel n B a _ b₋)) b₋

  ∂Cube→∂CubeDepConst→∂Cube 0 B a _ = refl
  ∂Cube→∂CubeDepConst→∂Cube 1 B a _ = refl
  ∂Cube→∂CubeDepConst→∂Cube (suc (suc n)) B a (b₀ , b₁ , ∂b₋) i =
    (_ , CubeRel→CubeDepConstRel→CubeDepConstRel (suc n) B a _ (b₀ .snd) i) ,
    (_ , CubeRel→CubeDepConstRel→CubeDepConstRel (suc n) B a _ (b₁ .snd) i) ,
    λ t → ∂Cube→∂CubeDepConst→∂Cube (suc n) B a (∂b₋ t) i

  CubeRel→CubeDepConstRel→CubeDepConstRel 0 B a _ _ = refl
  CubeRel→CubeDepConstRel→CubeDepConstRel 1 B a _ _ = refl
  CubeRel→CubeDepConstRel→CubeDepConstRel (suc (suc n)) B a _ b₋ i j =
    CubeRel→CubeDepConstRel→CubeDepConstRel (suc n) B a _ (b₋ j) i


open isHAEquiv

Iso-∂CubeDepConst-∂Cube : (n : ℕ) (B : A → Type ℓ') (a : A) → Iso (∂CubeDepConst n B a) (∂Cube n (B a))
Iso-∂CubeDepConst-∂Cube _ _ _ =
  iso (∂CubeDepConst→∂Cube _ _ _) (∂Cube→∂CubeDepConst _ _ _)
      (∂Cube→∂CubeDepConst→∂Cube _ _ _) (∂CubeDepConst→∂Cube→∂CubeDepConst _ _ _)

-- The iso defined above seems automatically half-adjoint,
-- but I don't want to write more crazy paths...

HAEquiv-∂CubeDepConst-∂Cube : (n : ℕ) (B : A → Type ℓ') (a : A) → HAEquiv (∂CubeDepConst n B a) (∂Cube n (B a))
HAEquiv-∂CubeDepConst-∂Cube _ _ _ = iso→HAEquiv (Iso-∂CubeDepConst-∂Cube _ _ _)

IsoOver-CubeDepConstRel-CubeRel : (n : ℕ) (B : A → Type ℓ') (a : A)
  → IsoOver (Iso-∂CubeDepConst-∂Cube n B a) CubeDepConstRel (CubeRel n (B a))
IsoOver-CubeDepConstRel-CubeRel _ _ _ =
  isoover (CubeDepConstRel→CubeRel _ _ _) (CubeRel→CubeDepConstRel _ _ _)
    (CubeRel→CubeDepConstRel→CubeDepConstRel _ _ _) (CubeDepConstRel→CubeRel→CubeDepConstRel _ _ _)

∂CubeDepConst≡∂Cube : (n : ℕ) (B : A → Type ℓ') (a : A) → ∂CubeDepConst n B a ≡ ∂Cube n (B a)
∂CubeDepConst≡∂Cube _ _ _ = ua (_ , isHAEquiv→isEquiv (HAEquiv-∂CubeDepConst-∂Cube _ _ _ .snd))

CubeDepConstRel≡CubeRel : (n : ℕ) (B : A → Type ℓ') (a : A)
  → PathP (λ i → ∂CubeDepConst≡∂Cube n B a i → Type ℓ') CubeDepConstRel (CubeRel n (B a))
CubeDepConstRel≡CubeRel _ _ _ = isoToPathOver _ _ (IsoOverIso→IsoOverHAEquiv (IsoOver-CubeDepConstRel-CubeRel _ _ _))
