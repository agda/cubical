{-

External Cubes, and Their Relations with the Internal Ones

This file contains:

- The definitions of non-dependent and dependent external n-cubes, in both curried/uncurried forms;

- Transformation between external/internal cubes;

- Transformation between curried/uncurried external cubes.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.External where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Cubes.Base
open import Cubical.Foundations.Cubes.Dependent
open import Cubical.Data.Nat.Base

open import Cubical.Foundations.2LTT

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'


{- Something about manipulating partial elements and cubical subtypes -}

-- Restrict (full) elements to some cofibrations

res : {A : Type ℓ} (φ : I) (u : A) → Partial φ A
res φ u (φ = i1) = u

resη : {A : Type ℓ} (φ : I) (u : A) → A [ _ ↦ res φ u ]
resη φ u = inS u

resP : {A : Type ℓ} (B : A → Type ℓ')
  (φ : I) {u : Partial φ A} (a : A [ _ ↦ u ])
  (b : B (outS a))
  → PartialP φ (λ o → B (u o))
resP B φ a b (φ = i1) = b


-- From dependent partial element to partial element

part :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : Partial φ A} (a : A [ _ ↦ u ])
  → PartialP φ (λ o → B (u o))
  → Partial  φ (B (outS a))
part B {φ} a u' (φ = i1) = u' 1=1

-- Reverse it

partP :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : Partial φ A} (a : A [ _ ↦ u ])
  → Partial  φ (B (outS a))
  → PartialP φ (λ o → B (u o))
partP B {φ} a u' (φ = i1) = u' 1=1

-- An η-rule about forming partial element
-- This and other η-rules below are needed,
-- because Cubical Agda gets stuck where the dimension variable has neutral terms.

partη :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : Partial φ A} (a : A [ _ ↦ u ])
  (b : B (outS a))
  → B (outS a) [ _ ↦ part B a (resP B φ a b) ]
partη B a b = inS b

partP-part :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : Partial φ A} (a : A [ _ ↦ u ])
  {v : Partial φ (B (outS a))} (b : B (outS a) [ _ ↦ v ])
  → B (outS a) [ _ ↦ part B a (partP B a v) ]
partP-part B a b = b


-- Concatenate two sides and parts in between to get a partial element.

concat :
  {φ : I} (a₋ : (i : I) → Partial φ A)
  (a₀ : A [ φ ↦ a₋ i0 ]) (a₁ : A [ φ ↦ a₋ i1 ])
  (i : I) → Partial (i ∨ ~ i ∨ φ) A
concat {φ = φ} a₋ a₀ a₁ i =
  λ { (i = i0) → outS a₀
    ; (i = i1) → outS a₁
    ; (φ = i1) → a₋ i 1=1 }

concatP :
  (B : A → Type ℓ')
  {φ : I} {a₋ : (i : I) → Partial φ A}
  {a₀ : A [ φ ↦ a₋ i0 ]} {a₁ : A [ φ ↦ a₋ i1 ]}
  (b₋ : (i : I) → PartialP φ (λ o → B (a₋ i o)))
  (b₀ : B (outS a₀) [ φ ↦ part B a₀ (b₋ i0) ])
  (b₁ : B (outS a₁) [ φ ↦ part B a₁ (b₋ i1) ])
  (i : I) → PartialP (i ∨ ~ i ∨ φ) (λ o → B (concat a₋ a₀ a₁ i o))
concatP B {φ = φ} b₋ b₀ b₁ i =
  λ { (i = i0) → outS b₀
    ; (i = i1) → outS b₁
    ; (φ = i1) → b₋ i 1=1 }


-- η-rule for concat

concatη :
  {φ : I} {u : (i : I) → Partial φ A}
  (a : (i : I) → A [ _ ↦ u i ])
  (i : I) → A [ _ ↦ concat u (a i0) (a i1) i ]
concatη {φ = φ} a i = inS (outS (a i))

concatPη :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : (i : I) → Partial φ A}
  {a : (i : I) → A [ _ ↦ u i ]}
  {v : (i : I) → PartialP φ (λ o → B (u i o))}
  (b : (i : I) → B (outS (a i)) [ _ ↦ part B (a i) (v i) ])
  (i : I) → B (outS (a i)) [ _ ↦ part B (concatη a i) (concatP B v (b i0) (b i1) i) ]
concatPη B b i = inS (outS (b i))


-- And the reverse procedure.

module _ (φ : I)
  (a₋ : (i : I) → Partial (i ∨ ~ i ∨ φ) A) where

  detach₋ : (i : I) → Partial φ A
  detach₋ i (φ = i1) = a₋ i 1=1

  detach₀ : A [ _ ↦ detach₋ i0 ]
  detach₀ = inS (a₋ i0 1=1)

  detach₁ : A [ _ ↦ detach₋ i1 ]
  detach₁ = inS (a₋ i1 1=1)


module _ {A : Type ℓ} (B : A → Type ℓ') (φ : I)
  {a₋ : (i : I) → Partial (i ∨ ~ i ∨ φ) A}
  (b₋ : (i : I) → PartialP _ (λ o → B (a₋ i o))) where

  detachP₋ : (i : I) → PartialP φ (λ o → B (detach₋ φ a₋ i o))
  detachP₋ i (φ = i1) = b₋ i 1=1

  detachP₀ : B (outS (detach₀ φ a₋)) [ _ ↦ part B (detach₀ φ a₋) (detachP₋ i0) ]
  detachP₀ = inS (b₋ i0 1=1)

  detachP₁ : B (outS (detach₁ φ a₋)) [ _ ↦ part B (detach₁ φ a₋) (detachP₋ i1) ]
  detachP₁ = inS (b₋ i1 1=1)


-- η-rule for detach

detachη :
  {φ : I} {u : (i : I) → Partial (i ∨ ~ i ∨ φ) A}
  (a : (i : I) → A [ _ ↦ u i ])
  (i : I) → A [ _ ↦ detach₋ φ u i ]
detachη a i = inS (outS (a i))

detachPη :
  {A : Type ℓ} (B : A → Type ℓ')
  {φ : I} {u : (i : I) → Partial (i ∨ ~ i ∨ φ) A}
  {a : (i : I) → A [ _ ↦ u i ]}
  {v : (i : I) → PartialP (i ∨ ~ i ∨ φ) (λ o → B (u i o))}
  (b : (i : I) → B (outS (a i)) [ _ ↦ part B (a i) (v i) ])
  (i : I) → B (outS (a i)) [ _ ↦ part B (detachη a i) (detachP₋ B φ v i) ]
detachPη B b i = inS (outS (b i))


{- External and Internal Cubes Back and Forth -}

-- The External n-Cubes
-- This one is THE CUBE, not the cubes in some types.

Iˣ : (n : ℕᵉ) → Typeᵉ
Iˣ 0ᵉ = Unitᵉ
Iˣ 1ᵉ = I
Iˣ (suc (suc n)) = I ×ᵉ Iˣ (suc n)

-- Boundary of THE CUBE

∂Iˣ : {n : ℕᵉ} → Iˣ n → I
∂Iˣ {n = 0ᵉ} _ = i0
∂Iˣ {n = 1ᵉ} i = i ∨ ~ i
∂Iˣ {n = suc (suc n)} (i , φ) = i ∨ ~ i ∨ ∂Iˣ φ


-- The type of curried functions from Iˣ n

CurryIˣFun : {n : ℕᵉ} (P : Iˣ n → Type ℓ) → Typeᵉ ℓ
CurryIˣFun {n = 0ᵉ} P = Exo (P tt)
CurryIˣFun {n = 1ᵉ} P = (i : I) → P i
CurryIˣFun {n = suc (suc n)} P = (i : I) → CurryIˣFun (λ φ → P (i , φ))

CurryIˣFunᵉ : {n : ℕᵉ} (P : Iˣ n → Typeᵉ ℓ) → Typeᵉ ℓ
CurryIˣFunᵉ {n = 0ᵉ} P = P tt
CurryIˣFunᵉ {n = 1ᵉ} P = (i : I) → P i
CurryIˣFunᵉ {n = suc (suc n)} P = (i : I) → CurryIˣFunᵉ (λ φ → P (i , φ))


-- Currying and uncurrying of Iˣ n

curryIˣ : {n : ℕᵉ} {P : Iˣ n → Type ℓ} → ((φ : Iˣ n) → P φ) → CurryIˣFun P
curryIˣ {n = 0ᵉ} p = exo (p tt)
curryIˣ {n = 1ᵉ} p = p
curryIˣ {n = suc (suc n)} p i = curryIˣ λ φ → p (i , φ)

curryIˣᵉ : {n : ℕᵉ} {P : Iˣ n → Typeᵉ ℓ} → ((φ : Iˣ n) → P φ) → CurryIˣFunᵉ P
curryIˣᵉ {n = 0ᵉ} p = p tt
curryIˣᵉ {n = 1ᵉ} p = p
curryIˣᵉ {n = suc (suc n)} p i = curryIˣᵉ λ φ → p (i , φ)

uncurryIˣ : {n : ℕᵉ} {P : Iˣ n → Type ℓ} → CurryIˣFun P → (φ : Iˣ n) → P φ
uncurryIˣ {n = 0ᵉ} (exo p) tt = p
uncurryIˣ {n = 1ᵉ} p = p
uncurryIˣ {n = suc (suc n)} p (i , φ) = uncurryIˣ (p i) φ

uncurryIˣᵉ : {n : ℕᵉ} {P : Iˣ n → Typeᵉ ℓ} → CurryIˣFunᵉ P → (φ : Iˣ n) → P φ
uncurryIˣᵉ {n = 0ᵉ} p tt = p
uncurryIˣᵉ {n = 1ᵉ} p = p
uncurryIˣᵉ {n = suc (suc n)} p (i , φ) = uncurryIˣᵉ (p i) φ

-- We don't have funExt supported for Typeᵉ in Cubical Agda at present,
-- so their equivalence can only be decribed in a weak form.

retcurryˣ : {n : ℕᵉ} {P : Iˣ n → Type ℓ} (f : (φ : Iˣ n) → P φ) → (φ : Iˣ n) → uncurryIˣ (curryIˣ f) φ ≡ f φ
retcurryˣ {n = 0ᵉ} f tt = refl
retcurryˣ {n = 1ᵉ} f _  = refl
retcurryˣ {n = suc (suc n)} p (i , _) = retcurryˣ (λ φ → p (i , φ)) _

retcurryˣᵉ : {n : ℕᵉ} {P : Iˣ n → Typeᵉ ℓ} (f : (φ : Iˣ n) → P φ) → (φ : Iˣ n) → uncurryIˣᵉ (curryIˣᵉ f) φ ≡ᵉ f φ
retcurryˣᵉ {n = 0ᵉ} f tt = reflᵉ
retcurryˣᵉ {n = 1ᵉ} f _  = reflᵉ
retcurryˣᵉ {n = suc (suc n)} p (i , _) = retcurryˣᵉ (λ φ → p (i , φ)) _

-- This is needed also because of no funExt.
-- Luckily enough, we don't really have to use funExt so far.

substCurryIˣFun :  {n : ℕᵉ} {P Q : Iˣ n → Type ℓ} → ((φ : Iˣ n) → P φ ≡ Q φ) → CurryIˣFun P → CurryIˣFun Q
substCurryIˣFun p f = curryIˣ λ φ → transport (p φ) (uncurryIˣ f φ)

substCurryIˣFunᵉ :  {n : ℕᵉ} {P Q : Iˣ n → Typeᵉ ℓ} → ((φ : Iˣ n) → P φ ≡ᵉ Q φ) → CurryIˣFunᵉ P → CurryIˣFunᵉ Q
substCurryIˣFunᵉ p f = curryIˣᵉ λ φ → transportᵉ (p φ) (uncurryIˣᵉ f φ)


{-

  Non-Dependent External Cubes

-}

-- The external cubes, using I, partial elements and cubical subtype.
-- Notice that it's in the uncurried form, not the usually used curried form.
-- The latter and the transformation between them are given at the end of this file.

∂Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
∂Cubeᵉ 0ᵉ _ = Unit*ᵉ
∂Cubeᵉ (suc n) A = (φ : Iˣ (suc n)) → Partial (∂Iˣ φ) A

CubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂Cubeᵉ n A → Typeᵉ ℓ
CubeRelᵉ 0ᵉ A _ = Exo A
CubeRelᵉ (suc n) A ∂ᵉ = (φ : Iˣ (suc n)) → A [ _ ↦ ∂ᵉ φ ]

Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
Cubeᵉ 0ᵉ A = Exo A
Cubeᵉ (suc n) A = Σᵉ[ ∂a ∈ ∂Cubeᵉ (suc n) A ] CubeRelᵉ (suc n) A ∂a

-- Taking the boundary of cubes

∂ᵉ : {n : ℕᵉ} {A : Type ℓ} → Cubeᵉ n A → ∂Cubeᵉ n A
∂ᵉ {n = 0ᵉ} _ = tt*ᵉ
∂ᵉ {n = suc n} = fst


-- Equivalence between external/internal cubes

interleaved mutual

  Cube→Cubeᵉ   : (n : ℕᵉ) →  Cube (ℕᵉ→ℕ n) A →  Cubeᵉ n A
  ∂Cube→∂Cubeᵉ : (n : ℕᵉ) → ∂Cube (ℕᵉ→ℕ n) A → ∂Cubeᵉ n A
  CubeRel→CubeRelᵉ : (n : ℕᵉ) {∂ : ∂Cube (ℕᵉ→ℕ n) A}
    → CubeRel (ℕᵉ→ℕ n) A ∂ → CubeRelᵉ n A (∂Cube→∂Cubeᵉ n ∂)

  Cube→Cubeᵉ 0ᵉ a = exo a
  Cube→Cubeᵉ (suc n) (∂ , a) = ∂Cube→∂Cubeᵉ _ ∂ , CubeRel→CubeRelᵉ _ {∂ = ∂} a

  ∂Cube→∂Cubeᵉ 0ᵉ _ = tt*ᵉ
  ∂Cube→∂Cubeᵉ 1ᵉ (a₀ , a₁) i = λ { (i = i0) → a₀ ; (i = i1) → a₁ }
  ∂Cube→∂Cubeᵉ (suc (suc n)) (a₀ , a₁ , ∂₋) (i , φ) =
    concat (λ t → ∂Cube→∂Cubeᵉ (suc n) (∂₋ t) φ)
      (Cube→Cubeᵉ (suc n) a₀ .snd φ) (Cube→Cubeᵉ (suc n) a₁ .snd φ) i

  CubeRel→CubeRelᵉ 0ᵉ a = exo a
  CubeRel→CubeRelᵉ 1ᵉ p i = inS (p i)
  CubeRel→CubeRelᵉ (suc (suc n)) a₋ (i , φ) =
    concatη (λ t → CubeRel→CubeRelᵉ (suc n) (a₋ t) φ) i


interleaved mutual

  Cubeᵉ→Cube   : (n : ℕᵉ) →  Cubeᵉ n A →  Cube (ℕᵉ→ℕ n) A
  ∂Cubeᵉ→∂Cube : (n : ℕᵉ) → ∂Cubeᵉ n A → ∂Cube (ℕᵉ→ℕ n) A
  CubeRelᵉ→CubeRel : (n : ℕᵉ) {∂ : ∂Cubeᵉ n A}
    → CubeRelᵉ n A ∂ → CubeRel (ℕᵉ→ℕ n) A (∂Cubeᵉ→∂Cube n ∂)

  Cubeᵉ→Cube 0ᵉ (exo a) = a
  Cubeᵉ→Cube (suc n) (∂ᵉ , aᵉ) = ∂Cubeᵉ→∂Cube _ ∂ᵉ , CubeRelᵉ→CubeRel _ {∂ = ∂ᵉ} aᵉ

  ∂Cubeᵉ→∂Cube 0ᵉ _ = tt*
  ∂Cubeᵉ→∂Cube 1ᵉ p = p i0 1=1 , p i1 1=1
  ∂Cubeᵉ→∂Cube (suc (suc n)) p =
    Cubeᵉ→Cube (suc n) (_ , λ φ → detach₀ (∂Iˣ φ) (λ i → p (i , φ))) ,
    Cubeᵉ→Cube (suc n) (_ , λ φ → detach₁ (∂Iˣ φ) (λ i → p (i , φ))) ,
    λ i → ∂Cubeᵉ→∂Cube (suc n) (λ φ → detach₋ (∂Iˣ φ) (λ i → p (i , φ)) i)

  CubeRelᵉ→CubeRel 0ᵉ (exo a) = a
  CubeRelᵉ→CubeRel 1ᵉ p i = outS (p i)
  CubeRelᵉ→CubeRel (suc (suc n)) a₋ i =
    CubeRelᵉ→CubeRel (suc n) (λ φ → detachη (λ i → a₋ (i , φ)) i)


-- External n-cubes, in curried form

ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
ΠCubeᵉ 0ᵉ A = Exo A
ΠCubeᵉ (suc n) A = CurryIˣFun {n = suc n} (λ _ → A)

∂ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
∂ΠCubeᵉ 0ᵉ A = Unit*ᵉ
∂ΠCubeᵉ (suc n) A = CurryIˣFunᵉ {n = suc n} (λ φ → Partial (∂Iˣ φ) A)

ΠCubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂ΠCubeᵉ n A → Typeᵉ ℓ
ΠCubeRelᵉ 0ᵉ A _ = Exo A
ΠCubeRelᵉ (suc n) A ∂ᵉ = CurryIˣFunᵉ (λ φ → A [ _ ↦ uncurryIˣᵉ {n = suc n} ∂ᵉ φ ])


-- Transformation between curried/uncurried external cubes

curryCubeᵉ : {n : ℕᵉ} → Cubeᵉ n A → ΠCubeᵉ n A
curryCubeᵉ {n = 0ᵉ}  a = a
curryCubeᵉ {n = suc n} a = curryIˣ (λ φ → outS (a .snd φ))

uncurryCubeᵉ : {n : ℕᵉ} → ΠCubeᵉ n A → Cubeᵉ n A
uncurryCubeᵉ {n = 0ᵉ}  a = a
uncurryCubeᵉ {n = suc n} a = _ , λ φ → inS (uncurryIˣ a φ)

curry∂Cubeᵉ : {n : ℕᵉ} → ∂Cubeᵉ n A → ∂ΠCubeᵉ n A
curry∂Cubeᵉ {n = 0ᵉ}  a = a
curry∂Cubeᵉ {n = suc n} a = curryIˣᵉ a

uncurry∂Cubeᵉ : {n : ℕᵉ} → ∂ΠCubeᵉ n A → ∂Cubeᵉ n A
uncurry∂Cubeᵉ {n = 0ᵉ}  a = a
uncurry∂Cubeᵉ {n = suc n} a = uncurryIˣᵉ a


-- Direct transformation between curried external cubes and internal cubes

Cube→ΠCubeᵉ : (n : ℕᵉ) → Cube (ℕᵉ→ℕ n) A → ΠCubeᵉ n A
Cube→ΠCubeᵉ n p = curryCubeᵉ (Cube→Cubeᵉ n p)

ΠCubeᵉ→Cube : (n : ℕᵉ) → ΠCubeᵉ n A → Cube (ℕᵉ→ℕ n) A
ΠCubeᵉ→Cube n p = Cubeᵉ→Cube n (uncurryCubeᵉ p)

∂Cube→∂ΠCubeᵉ : (n : ℕᵉ) → ∂Cube (ℕᵉ→ℕ n) A → ∂ΠCubeᵉ n A
∂Cube→∂ΠCubeᵉ n p = curry∂Cubeᵉ (∂Cube→∂Cubeᵉ n p)

∂ΠCubeᵉ→∂Cube : (n : ℕᵉ) → ∂ΠCubeᵉ n A → ∂Cube (ℕᵉ→ℕ n) A
∂ΠCubeᵉ→∂Cube n p = ∂Cubeᵉ→∂Cube n (uncurry∂Cubeᵉ p)

CubeRel→ΠCubeRelᵉ : (n : ℕᵉ) (∂ : ∂Cube (ℕᵉ→ℕ n) A) → CubeRel (ℕᵉ→ℕ n) A ∂ → ΠCubeRelᵉ n A (∂Cube→∂ΠCubeᵉ n ∂)
CubeRel→ΠCubeRelᵉ 0ᵉ _ a = exo a
CubeRel→ΠCubeRelᵉ {A = A} (suc n) ∂ a =
  substCurryIˣFunᵉ
    (λ φ → congᵉ (λ u → A [ _ ↦ u ]) (symᵉ (retcurryˣᵉ (∂Cube→∂Cubeᵉ _ ∂) φ)))
    (curryIˣᵉ (Cube→Cubeᵉ (suc n) (∂ , a) .snd))


{-

  Dependent External Cubes

-}

-- The external dependent cubes, in uncurried form

∂CubeDepᵉ : {n : ℕᵉ} {A : Type ℓ} (B : A → Type ℓ') → ∂Cubeᵉ n A → Typeᵉ ℓ'
∂CubeDepᵉ {n = 0ᵉ} _ _ = Unit*ᵉ
∂CubeDepᵉ {n = suc n} B ∂a = (φ : Iˣ (suc n)) → PartialP (∂Iˣ φ) (λ o → B (∂a φ o))

CubeDepRelᵉ : {n : ℕᵉ} {A : Type ℓ} (B : A → Type ℓ') (a₋ : Cubeᵉ n A) → ∂CubeDepᵉ B (∂ᵉ a₋) → Typeᵉ ℓ'
CubeDepRelᵉ {n = 0ᵉ} B (exo a) _ = Exo (B a)
CubeDepRelᵉ {n = suc n} B a₋ ∂ᵉ = (φ : Iˣ (suc n)) → B (outS (a₋ .snd φ)) [ _ ↦ part B (a₋ .snd φ) (∂ᵉ φ) ]

CubeDepᵉ : {n : ℕᵉ} {A : Type ℓ} (B : A → Type ℓ') → Cubeᵉ n A → Typeᵉ ℓ'
CubeDepᵉ {n = 0ᵉ} B (exo a) = Exo (B a)
CubeDepᵉ {n = suc n} B a₋ = Σᵉ[ ∂b ∈ ∂CubeDepᵉ B (a₋ .fst) ] CubeDepRelᵉ B a₋ ∂b


interleaved mutual

  CubeDep→CubeDepᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {a : Cube (ℕᵉ→ℕ n) A} → CubeDep B a → CubeDepᵉ B (Cube→Cubeᵉ n a)
  ∂CubeDep→∂CubeDepᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {∂a : ∂Cube (ℕᵉ→ℕ n) A} → ∂CubeDep B ∂a → ∂CubeDepᵉ B (∂Cube→∂Cubeᵉ n ∂a)
  -- Begin with n=1 to avoid awkward substᵉ along ∂ᵉ ∘ Cube→Cubeᵉ ≡ᵉ ∂Cube→∂Cubeᵉ ∘ ∂
  CubeDepRel→CubeDepRelᵉSuc : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {a : Cube (ℕᵉ→ℕ (suc n)) A} {∂b : ∂CubeDep {n = ℕᵉ→ℕ (suc n)} B (∂ a)}
    → CubeDepRel a ∂b → CubeDepRelᵉ B (Cube→Cubeᵉ (suc n) a) (∂CubeDep→∂CubeDepᵉ (suc n) B ∂b)

  CubeDep→CubeDepᵉ 0ᵉ B b = exo b
  CubeDep→CubeDepᵉ (suc n) B (∂b , b₋) =
    ∂CubeDep→∂CubeDepᵉ (suc n) B ∂b , CubeDepRel→CubeDepRelᵉSuc n B b₋

  ∂CubeDep→∂CubeDepᵉ 0ᵉ B _ = tt*ᵉ
  ∂CubeDep→∂CubeDepᵉ 1ᵉ B (b₀ , b₁) i = λ { (i = i0) → b₀ ; (i = i1) → b₁ }
  ∂CubeDep→∂CubeDepᵉ (suc (suc n)) B (b₀ , b₁ , ∂b₋) (i , φ) =
    concatP B (λ t → ∂CubeDep→∂CubeDepᵉ (suc n) B (∂b₋ t) φ)
      (CubeDep→CubeDepᵉ (suc n) B b₀ .snd φ) (CubeDep→CubeDepᵉ (suc n) B b₁ .snd φ) i

  CubeDepRel→CubeDepRelᵉSuc 0ᵉ B p i = inS (p i)
  CubeDepRel→CubeDepRelᵉSuc (suc n) B b (i , φ) =
    concatPη B (λ t → CubeDepRel→CubeDepRelᵉSuc n B (b t) φ) i


interleaved mutual

  CubeDepᵉ→CubeDep : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {a : Cubeᵉ n A} → CubeDepᵉ B a → CubeDep B (Cubeᵉ→Cube n a)
  ∂CubeDepᵉ→∂CubeDep : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {∂a : ∂Cubeᵉ n A} → ∂CubeDepᵉ B ∂a → ∂CubeDep B (∂Cubeᵉ→∂Cube n ∂a)
  -- Begin with n=1 to avoid awkward substᵉ along ∂ᵉ ∘ Cube→Cubeᵉ ≡ᵉ ∂Cube→∂Cubeᵉ ∘ ∂
  CubeDepRelᵉ→CubeDepRelSuc : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
    {a : Cubeᵉ (suc n) A} {∂b : ∂CubeDepᵉ {n = suc n} B (∂ᵉ a)}
    → CubeDepRelᵉ B a ∂b → CubeDepRel (Cubeᵉ→Cube (suc n) a) (∂CubeDepᵉ→∂CubeDep (suc n) B ∂b)

  CubeDepᵉ→CubeDep 0ᵉ B {a = exo a} (exo b) = b
  CubeDepᵉ→CubeDep (suc n) B (∂b , b₋) =
    ∂CubeDepᵉ→∂CubeDep (suc n) B ∂b , CubeDepRelᵉ→CubeDepRelSuc n B b₋

  ∂CubeDepᵉ→∂CubeDep 0ᵉ B _ = tt*
  ∂CubeDepᵉ→∂CubeDep 1ᵉ B p = p i0 1=1 , p i1 1=1
  ∂CubeDepᵉ→∂CubeDep (suc (suc n)) B p =
    CubeDepᵉ→CubeDep (suc n) B (_ , λ φ → detachP₀ B (∂Iˣ φ) (λ i → p (i , φ))) ,
    CubeDepᵉ→CubeDep (suc n) B (_ , λ φ → detachP₁ B (∂Iˣ φ) (λ i → p (i , φ))) ,
    λ i → ∂CubeDepᵉ→∂CubeDep (suc n) B (λ φ → detachP₋ B (∂Iˣ φ) (λ i → p (i , φ)) i)

  CubeDepRelᵉ→CubeDepRelSuc 0ᵉ B p i = outS (p i)
  CubeDepRelᵉ→CubeDepRelSuc (suc n) B b₋ i =
    CubeDepRelᵉ→CubeDepRelSuc n B (λ φ → detachPη B (λ i → b₋ (i , φ)) i)


-- External n-cubes, in curried form

ΠCubeDepᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ') → ΠCubeᵉ n A → Typeᵉ ℓ'
ΠCubeDepᵉ 0ᵉ B (exo a) = Exo (B a)
ΠCubeDepᵉ (suc n) B a = CurryIˣFun {n = suc n} (λ φ → B (uncurryIˣ a φ))

∂ΠCubeDepᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ') → ∂ΠCubeᵉ n A → Typeᵉ ℓ'
∂ΠCubeDepᵉ 0ᵉ B _ = Unit*ᵉ
∂ΠCubeDepᵉ (suc n) B ∂a = CurryIˣFunᵉ {n = suc n} (λ φ → PartialP (∂Iˣ φ) (λ o → B (uncurryIˣᵉ ∂a φ o)))


-- Transformation between curried/uncurried dependent external cubes

curryCubeDepᵉ : {n : ℕᵉ} (B : A → Type ℓ') (a : Cubeᵉ n A) → CubeDepᵉ B a → ΠCubeDepᵉ n B (curryCubeᵉ a)
curryCubeDepᵉ {n = 0ᵉ} B (exo a) b = b
curryCubeDepᵉ {n = suc n} B a b =
  -- Here it seems a `transport refl` occurs inevitably, even if two terms morally represent the same syntax.
  substCurryIˣFun
    (λ φ → cong (λ u → B u) (sym (retcurryˣ (λ φ → outS (a .snd φ)) φ)))
    (curryIˣ (λ φ → outS (b .snd φ)))

uncurryCubeDepᵉ : {n : ℕᵉ} (B : A → Type ℓ') (a : ΠCubeᵉ n A) → ΠCubeDepᵉ n B a → CubeDepᵉ {n = n} B (uncurryCubeᵉ a)
uncurryCubeDepᵉ {n = 0ᵉ} B (exo a) b = b
uncurryCubeDepᵉ {n = suc n} B a b = _ , λ φ → partη B _ (uncurryIˣ b φ)

curry∂CubeDepᵉ : {n : ℕᵉ} (B : A → Type ℓ') (∂a : ∂Cubeᵉ n A) → ∂CubeDepᵉ B ∂a → ∂ΠCubeDepᵉ n B (curry∂Cubeᵉ ∂a)
curry∂CubeDepᵉ {n = 0ᵉ} B _ _ = tt*ᵉ
curry∂CubeDepᵉ {n = suc n} B ∂a ∂b =
  substCurryIˣFunᵉ
    (λ φ → congᵉ (λ u → PartialP (∂Iˣ φ) (λ o → B (u o))) (symᵉ (retcurryˣᵉ ∂a φ)))
    (curryIˣᵉ ∂b)

uncurry∂CubeDepᵉ : {n : ℕᵉ} (B : A → Type ℓ') (∂a : ∂ΠCubeᵉ n A)
  → ∂ΠCubeDepᵉ n B ∂a → ∂CubeDepᵉ {n = n} B (uncurry∂Cubeᵉ ∂a)
uncurry∂CubeDepᵉ {n = 0ᵉ} B _ _ = tt*ᵉ
uncurry∂CubeDepᵉ {n = suc n} B _ ∂b = uncurryIˣᵉ ∂b


-- Direct transformation between curried external dependent cubes and internal cubes

CubeDep→ΠCubeDepᵉ : {A : Type ℓ} (n : ℕᵉ) (B : A → Type ℓ')
  (a : Cube (ℕᵉ→ℕ n) A) → CubeDep B a → ΠCubeDepᵉ n B (Cube→ΠCubeᵉ n a)
CubeDep→ΠCubeDepᵉ n B _ b = curryCubeDepᵉ B _ (CubeDep→CubeDepᵉ n B b)

ΠCubeDepᵉ→CubeDep : {A : Type ℓ} (n : ℕᵉ) (B : A → Type ℓ')
  (a : ΠCubeᵉ n A) → ΠCubeDepᵉ n B a → CubeDep B (ΠCubeᵉ→Cube n a)
ΠCubeDepᵉ→CubeDep n B _ b = CubeDepᵉ→CubeDep n B (uncurryCubeDepᵉ B _ b)

∂CubeDep→∂ΠCubeDepᵉ : (n : ℕᵉ) (B : A → Type ℓ')
  (∂a : ∂Cube (ℕᵉ→ℕ n) A) → ∂CubeDep B ∂a → ∂ΠCubeDepᵉ n B (∂Cube→∂ΠCubeᵉ n ∂a)
∂CubeDep→∂ΠCubeDepᵉ n B _ ∂b = curry∂CubeDepᵉ B _ (∂CubeDep→∂CubeDepᵉ n B ∂b)

∂ΠCubeDepᵉ→∂CubeDep : (n : ℕᵉ) (B : A → Type ℓ')
  (∂a : ∂ΠCubeᵉ n A) → ∂ΠCubeDepᵉ n B ∂a → ∂CubeDep B (∂ΠCubeᵉ→∂Cube n ∂a)
∂ΠCubeDepᵉ→∂CubeDep n B _ ∂b = ∂CubeDepᵉ→∂CubeDep n B (uncurry∂CubeDepᵉ B _ ∂b)


{-

  Types that encode the dependent cube-filling problems

-}

ΠCubeLiftᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ') → ΠCubeᵉ n A → Typeᵉ ℓ'
ΠCubeLiftᵉ 0ᵉ B (exo a) = Unit*ᵉ
ΠCubeLiftᵉ (suc n) B a  = CurryIˣFunᵉ {n = suc n} (λ φ → Partial (∂Iˣ φ) (B (uncurryIˣ a φ)))

ΠCubeLiftedᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ') (a : ΠCubeᵉ n A) → ΠCubeLiftᵉ n B a → Typeᵉ ℓ'
ΠCubeLiftedᵉ 0ᵉ B (exo a) _ = Exo (B a)
ΠCubeLiftedᵉ (suc n) B a ∂b = CurryIˣFunᵉ {n = suc n} (λ φ → B (uncurryIˣ a φ) [ _ ↦ uncurryIˣᵉ ∂b φ ])

ΠCubeLiftᵉ→∂CubeDepᵉ : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
  (a : ΠCubeᵉ n A) → ΠCubeLiftᵉ n B a → ∂CubeDepᵉ B (∂ᵉ {n = n} (uncurryCubeᵉ a))
ΠCubeLiftᵉ→∂CubeDepᵉ 0ᵉ B _ _ = tt*ᵉ
ΠCubeLiftᵉ→∂CubeDepᵉ (suc n) B a ∂b φ = partP B (uncurryCubeᵉ a .snd φ) (uncurryIˣᵉ ∂b φ)


-- Direct translation between lifting problems

ΠCubeLiftᵉ→∂CubeDep : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
  (a : ΠCubeᵉ n A) → ΠCubeLiftᵉ n B a → ∂CubeDep B _
ΠCubeLiftᵉ→∂CubeDep n B a ∂b = ∂CubeDepᵉ→∂CubeDep n B (ΠCubeLiftᵉ→∂CubeDepᵉ n B a ∂b)

CubeDepRel→ΠCubeLiftedᵉSuc : (n : ℕᵉ) {A : Type ℓ} (B : A → Type ℓ')
  {a : Cube (ℕᵉ→ℕ (suc n)) A} (∂b : ∂CubeDep B (∂ a)) (b : CubeDepRel {n = ℕᵉ→ℕ (suc n)} a ∂b) → _
CubeDepRel→ΠCubeLiftedᵉSuc n B ∂b b = curryIˣᵉ (CubeDepRel→CubeDepRelᵉSuc n B b)
