{-

External Cubes, and Their Relations with the Internal Ones

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.External where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.2LTT
open import Cubical.Foundations.Cubes.Base
open import Cubical.Data.Nat.Base

private
  variable
    ℓ : Level
    A : Type ℓ


{- Something about manipulating partial elements and cubical subtypes -}

-- Concatenate two sides and parts in between to get a partial element.
concat :
  {φ : I} (a₋ : (i : I) → Partial φ A)
  (a₀ : A [ φ ↦ a₋ i0 ]) (a₁ : A [ φ ↦ a₋ i1 ])
  (i : I) → Partial (i ∨ ~ i ∨ φ) A
concat {φ = φ} a₋ a₀ a₁ i (i = i0) = outS a₀
concat {φ = φ} a₋ a₀ a₁ i (i = i1) = outS a₁
concat {φ = φ} a₋ a₀ a₁ i (φ = i1) = a₋ i 1=1

-- η-rule for concat
concat' :
  {φ : I} {u : (i : I) → Partial φ A}
  (a : (i : I) → A [ _ ↦ u i ])
  (i : I) → A [ _ ↦ concat u (a i0) (a i1) i ]
concat' {φ = φ} a i = inS (outS (a i))


-- And the reverse procedure.
module _ (φ : I) (a₋ : (i : I) → Partial (i ∨ ~ i ∨ φ) A) where

  detach₋ : (i : I) → Partial φ A
  detach₋ i (φ = i1) = a₋ i 1=1

  detach₀ : A [ _ ↦ detach₋ i0 ]
  detach₀ = inS (a₋ i0 1=1)

  detach₁ : A [ _ ↦ detach₋ i1 ]
  detach₁ = inS (a₋ i1 1=1)

-- η-rule for detach
detach' :
  {φ : I} {u : (i : I) → Partial (i ∨ ~ i ∨ φ) A}
  (a : (i : I) → A [ _ ↦ u i ])
  (i : I) → A [ _ ↦ detach₋ φ u i ]
detach' a i = inS (outS (a i))


{- External and Internal Cubes Back and Forth -}


Iˣ : (n : ℕᵉ) → Typeᵉ
Iˣ 0ᵉ = Unitᵉ
Iˣ 1ᵉ = I
Iˣ (suc (suc n)) = I ×ᵉ Iˣ (suc n)

∂Iˣ : {n : ℕᵉ} → Iˣ n → I
∂Iˣ {n = 0ᵉ} _ = i0
∂Iˣ {n = 1ᵉ} i = i ∨ ~ i
∂Iˣ {n = suc (suc n)} (i , φ) = i ∨ ~ i ∨ ∂Iˣ φ



∂Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
∂Cubeᵉ 0ᵉ _ = Unit*ᵉ
∂Cubeᵉ (suc n) A = (φ : Iˣ (suc n)) → Partial (∂Iˣ φ) A

CubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂Cubeᵉ n A → Typeᵉ ℓ
CubeRelᵉ 0ᵉ A _ = Exo A
CubeRelᵉ (suc n) A ∂ᵉ = (φ : Iˣ (suc n)) → A [ _ ↦ ∂ᵉ φ ]

Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
Cubeᵉ 0ᵉ A = Exo A
Cubeᵉ (suc n) A = Σᵉ[ ∂ ∈ ∂Cubeᵉ (suc n) A ] (CubeRelᵉ (suc n) A ∂)


interleaved mutual

  Cube→Cubeᵉ   : (n : ℕᵉ) →  Cube (ℕᵉ→ℕ n) A →  Cubeᵉ n A
  ∂Cube→∂Cubeᵉ : (n : ℕᵉ) → ∂Cube (ℕᵉ→ℕ n) A → ∂Cubeᵉ n A
  CubeRel→CubeRelᵉ : (n : ℕᵉ) {∂ : ∂Cube (ℕᵉ→ℕ n) A}
    → CubeRel (ℕᵉ→ℕ n) A ∂ → CubeRelᵉ n A (∂Cube→∂Cubeᵉ n ∂)

  Cube→Cubeᵉ zero a = exo a
  Cube→Cubeᵉ (suc n) (∂ , a) = ∂Cube→∂Cubeᵉ _ ∂ , CubeRel→CubeRelᵉ _ {∂ = ∂} a

  ∂Cube→∂Cubeᵉ 0ᵉ _ = tt*ᵉ
  ∂Cube→∂Cubeᵉ 1ᵉ (a , b) i = λ { (i = i0) → a ; (i = i1) → b }
  ∂Cube→∂Cubeᵉ (suc (suc n)) (a₀ , a₁ , ∂₋) (i , φ) =
    concat (λ t → ∂Cube→∂Cubeᵉ (suc n) (∂₋ t) φ)
      (Cube→Cubeᵉ (suc n) a₀ .snd φ) (Cube→Cubeᵉ (suc n) a₁ .snd φ) i

  CubeRel→CubeRelᵉ 0ᵉ a = exo a
  CubeRel→CubeRelᵉ 1ᵉ p i = inS (p i)
  CubeRel→CubeRelᵉ (suc (suc n)) a₋ (i , φ) =
    concat' (λ t → CubeRel→CubeRelᵉ (suc n) (a₋ t) φ) i


interleaved mutual

  Cubeᵉ→Cube   : (n : ℕᵉ) →  Cubeᵉ n A →  Cube (ℕᵉ→ℕ n) A
  ∂Cubeᵉ→∂Cube : (n : ℕᵉ) → ∂Cubeᵉ n A → ∂Cube (ℕᵉ→ℕ n) A
  CubeRelᵉ→CubeRel : (n : ℕᵉ) {∂ : ∂Cubeᵉ n A}
    → CubeRelᵉ n A ∂ → CubeRel (ℕᵉ→ℕ n) A (∂Cubeᵉ→∂Cube n ∂)

  Cubeᵉ→Cube zero (exo a) = a
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
    CubeRelᵉ→CubeRel (suc n) (λ φ → detach' (λ i → a₋ (i , φ)) i)


CurryIˣFun : {n : ℕᵉ} (P : Iˣ n → Type ℓ) → Typeᵉ ℓ
CurryIˣFun {n = 0ᵉ} P = Exo (P tt)
CurryIˣFun {n = 1ᵉ} P = (i : I) → P i
CurryIˣFun {n = suc (suc n)} P = (i : I) → CurryIˣFun (λ φ → P (i , φ))

CurryIˣFunᵉ : {n : ℕᵉ} (P : Iˣ n → Typeᵉ ℓ) → Typeᵉ ℓ
CurryIˣFunᵉ {n = 0ᵉ} P = P tt
CurryIˣFunᵉ {n = 1ᵉ} P = (i : I) → P i
CurryIˣFunᵉ {n = suc (suc n)} P = (i : I) → CurryIˣFunᵉ (λ φ → P (i , φ))

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

retcurryˣᵉ : {n : ℕᵉ} {P : Iˣ n → Typeᵉ ℓ} (f : (φ : Iˣ n) → P φ) → (φ : Iˣ n) → uncurryIˣᵉ (curryIˣᵉ f) φ ≡ᵉ f φ
retcurryˣᵉ {n = 0ᵉ} f tt = reflᵉ
retcurryˣᵉ {n = 1ᵉ} f _  = reflᵉ
retcurryˣᵉ {n = suc (suc n)} p (i , _) = retcurryˣᵉ (λ φ → p (i , φ)) _

substCurryIˣFunᵉ :  {n : ℕᵉ} {P Q : Iˣ n → Typeᵉ ℓ} → ((φ : Iˣ n) → P φ ≡ᵉ Q φ) → CurryIˣFunᵉ P → CurryIˣFunᵉ Q
substCurryIˣFunᵉ p f = curryIˣᵉ λ φ → transportᵉ (p φ) (uncurryIˣᵉ f φ)


ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
ΠCubeᵉ 0ᵉ A = Exo A
ΠCubeᵉ (suc n) A = CurryIˣFun {n = suc n} (λ _ → A)

curryCubeᵉ : {n : ℕᵉ} → Cubeᵉ n A → ΠCubeᵉ n A
curryCubeᵉ {n = zero}  a = a
curryCubeᵉ {n = suc n} a = curryIˣ (λ φ → outS (a .snd φ))

uncurryCubeᵉ : {n : ℕᵉ} → ΠCubeᵉ n A → Cubeᵉ n A
uncurryCubeᵉ {n = zero}  a = a
uncurryCubeᵉ {n = suc n} a = _ , λ φ → inS (uncurryIˣ a φ)


∂ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → Typeᵉ ℓ
∂ΠCubeᵉ 0ᵉ A = Unit*ᵉ
∂ΠCubeᵉ (suc n) A = CurryIˣFunᵉ {n = suc n} (λ φ → Partial (∂Iˣ φ) A)

curry∂Cubeᵉ : {n : ℕᵉ} → ∂Cubeᵉ n A → ∂ΠCubeᵉ n A
curry∂Cubeᵉ {n = zero}  a = a
curry∂Cubeᵉ {n = suc n} a = curryIˣᵉ a

uncurry∂Cubeᵉ : {n : ℕᵉ} → ∂ΠCubeᵉ n A → ∂Cubeᵉ n A
uncurry∂Cubeᵉ {n = zero}  a = a
uncurry∂Cubeᵉ {n = suc n} a = uncurryIˣᵉ a


Cube→ΠCubeᵉ : (n : ℕᵉ) → Cube (ℕᵉ→ℕ n) A → ΠCubeᵉ n A
Cube→ΠCubeᵉ n p = curryCubeᵉ (Cube→Cubeᵉ n p)

ΠCubeᵉ→Cube : (n : ℕᵉ) → ΠCubeᵉ n A → Cube (ℕᵉ→ℕ n) A
ΠCubeᵉ→Cube n p = Cubeᵉ→Cube n (uncurryCubeᵉ p)

∂Cube→∂ΠCubeᵉ : (n : ℕᵉ) → ∂Cube (ℕᵉ→ℕ n) A → ∂ΠCubeᵉ n A
∂Cube→∂ΠCubeᵉ n p = curry∂Cubeᵉ (∂Cube→∂Cubeᵉ n p)

∂ΠCubeᵉ→∂Cube : (n : ℕᵉ) → ∂ΠCubeᵉ n A → ∂Cube (ℕᵉ→ℕ n) A
∂ΠCubeᵉ→∂Cube n p = ∂Cubeᵉ→∂Cube n (uncurry∂Cubeᵉ p)


ΠCubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂ΠCubeᵉ n A → Typeᵉ ℓ
ΠCubeRelᵉ 0ᵉ A _ = Exo A
ΠCubeRelᵉ (suc n) A ∂ᵉ = CurryIˣFunᵉ (λ φ → A [ _ ↦ uncurryIˣᵉ {n = suc n} ∂ᵉ φ ])


CubeRel→ΠCubeRelᵉ : (n : ℕᵉ) (∂ : ∂Cube (ℕᵉ→ℕ n) A) → CubeRel (ℕᵉ→ℕ n) A ∂ → ΠCubeRelᵉ n A (∂Cube→∂ΠCubeᵉ n ∂)
CubeRel→ΠCubeRelᵉ 0ᵉ _ a = exo a
CubeRel→ΠCubeRelᵉ {A = A} (suc n) ∂ a =
  substCurryIˣFunᵉ
    (λ φ → congᵉ (λ u → A [ _ ↦ u ]) (symᵉ (retcurryˣᵉ (∂Cube→∂Cubeᵉ _ ∂) φ)))
    (curryIˣᵉ (Cube→Cubeᵉ (suc n) (∂ , a) .snd))
