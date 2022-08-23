{-

  Relation with the external (partial) cubes

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.External where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Cubes.Base
open import Cubical.Data.Nat.Base


private
  variable
    ℓ ℓ' ℓ'' : Level
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

-- Notice that the functions are meta-inductively defined,
-- except for the first two cases when n = 0 or 1.

-- TODO : Write macros to generate them!!!


data ℕᵉ : SSet where
  zero : ℕᵉ
  suc  : ℕᵉ → ℕᵉ

pattern 0ᵉ = zero
pattern 1ᵉ = suc 0ᵉ
pattern 2ᵉ = suc 1ᵉ
pattern 3ᵉ = suc 2ᵉ
pattern 4ᵉ = suc 3ᵉ

ℕᵉ→ℕ : ℕᵉ → ℕ
ℕᵉ→ℕ zero = 0
ℕᵉ→ℕ (suc n) = suc (ℕᵉ→ℕ n)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.List
open import Cubical.Reflection.Base

ℕ→ℕᵉTerm : ℕ → Term
ℕ→ℕᵉTerm 0 = quoteTerm ℕᵉ.zero
ℕ→ℕᵉTerm (suc n) = con (quote ℕᵉ.suc) (ℕ→ℕᵉTerm n v∷ [])

macro
  ℕ→ℕᵉ : ℕ → Term → TC Unit
  ℕ→ℕᵉ n t = unify t (ℕ→ℕᵉTerm n)



data Exo (A : Type ℓ) : SSet ℓ where
  exo : A → Exo A



data Unitᵉ : SSet where
  tt : Unitᵉ

data Unit*ᵉ {ℓ : Level} : SSet ℓ where
  tt*ᵉ : Unit*ᵉ


record Σᵉ (A : SSet ℓ)(B : A → SSet ℓ') : SSet (ℓ-max ℓ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σᵉ public

Σᵉ-syntax : ∀ {ℓ ℓ'} (A : SSet ℓ) (B : A → SSet ℓ') → SSet (ℓ-max ℓ ℓ')
Σᵉ-syntax = Σᵉ

syntax Σᵉ-syntax A (λ x → B) = Σᵉ[ x ∈ A ] B


_×ᵉ_ : ∀ {ℓ ℓ'} (A : SSet ℓ) (B : SSet ℓ') → SSet (ℓ-max ℓ ℓ')
A ×ᵉ B = Σᵉ A (λ _ → B)

infixr 5 _×ᵉ_


curryᵉ :
  {A : SSet ℓ} {B : A → SSet ℓ'} {C : (a : A) → B a → SSet ℓ'}
  → (((a , b) : Σᵉ A B) → C a b)
  → (a : A) → (b : B a) → C a b
curryᵉ f a b = f (a , b)

uncurryᵉ :
  {A : SSet ℓ} {B : A → SSet ℓ'} {C : (a : A) → B a → SSet ℓ'}
  → ((a : A) → (b : B a) → C a b)
  → ((a , b) : Σᵉ A B) → C a b
uncurryᵉ f (a , b) = f a b



data _≡ᵉ_ {A : SSet ℓ} : A → A → SSet ℓ where
  reflᵉ : {a : A} → a ≡ᵉ a

symᵉ : {A : SSet ℓ} {a b : A} → a ≡ᵉ b → b ≡ᵉ a
symᵉ reflᵉ = reflᵉ

congᵉ : {A : SSet ℓ} {B : SSet ℓ'} → (f : A → B) → {a b : A} → a ≡ᵉ b → f a ≡ᵉ f b
congᵉ f reflᵉ = reflᵉ

substᵉ : {A : SSet ℓ} (P : A → SSet ℓ') {a b : A} → a ≡ᵉ b → P a → P b
substᵉ P reflᵉ p = p

transportᵉ : {A B : SSet ℓ} → A ≡ᵉ B → A → B
transportᵉ reflᵉ a = a

Kᵉ : {A : SSet ℓ} {a b : A} → (p q : a ≡ᵉ b) → p ≡ᵉ q
Kᵉ reflᵉ reflᵉ = reflᵉ



Iˣ : (n : ℕᵉ) → SSet
Iˣ 0ᵉ = Unitᵉ
Iˣ 1ᵉ = I
Iˣ (suc (suc n)) = I ×ᵉ Iˣ (suc n)

∂Iˣ : {n : ℕᵉ} → Iˣ n → I
∂Iˣ {n = 0ᵉ} _ = i0
∂Iˣ {n = 1ᵉ} i = i ∨ ~ i
∂Iˣ {n = suc (suc n)} (i , φ) = i ∨ ~ i ∨ ∂Iˣ φ



∂Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → SSet ℓ
∂Cubeᵉ 0ᵉ _ = Unit*ᵉ
∂Cubeᵉ (suc n) A = (φ : Iˣ (suc n)) → Partial (∂Iˣ φ) A

CubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂Cubeᵉ n A → SSet ℓ
CubeRelᵉ 0ᵉ A _ = Exo A
CubeRelᵉ (suc n) A ∂ᵉ = (φ : Iˣ (suc n)) → A [ _ ↦ ∂ᵉ φ ]

Cubeᵉ : (n : ℕᵉ) (A : Type ℓ) → SSet ℓ
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

{-
interleaved mutual

  Cube→Cubeᵉ→Cube : (n : ℕᵉ) → (a : Cube (ℕᵉ→ℕ n) A) → Cubeᵉ→Cube n (Cube→Cubeᵉ n a) ≡ᵉ a
  ∂Cube→∂Cubeᵉ→∂Cube : (n : ℕᵉ) → (∂ : ∂Cube (ℕᵉ→ℕ n) A) → ∂Cubeᵉ→∂Cube n (∂Cube→∂Cubeᵉ n ∂) ≡ᵉ ∂
  CubeRel→CubeRelᵉ→CubeRel : (n : ℕᵉ) {∂ : ∂Cube (ℕᵉ→ℕ n) A}
    → (a : CubeRel (ℕᵉ→ℕ n) A ∂) → CubeRelᵉ n A (∂Cube→∂Cubeᵉ n ∂)

  Cube→Cubeᵉ→Cube zero a = exo a
  Cube→Cubeᵉ→Cube (suc n) (∂ , a) = ∂Cube→∂Cubeᵉ _ ∂ , CubeRel→CubeRelᵉ _ {∂ = ∂} a

  ∂Cube→∂Cubeᵉ→∂Cube 0ᵉ _ = tt*ᵉ
  ∂Cube→∂Cubeᵉ→∂Cube 1ᵉ (a , b) i = λ { (i = i0) → a ; (i = i1) → b }
  ∂Cube→∂Cubeᵉ→∂Cube (suc (suc n)) (a₀ , a₁ , ∂₋) (i , φ) = {!!}
    --concat (λ t → ∂Cube→∂Cubeᵉ (suc n) (∂₋ t) φ)
      --(Cube→Cubeᵉ (suc n) a₀ .snd φ) (Cube→Cubeᵉ (suc n) a₁ .snd φ) i

  CubeRel→CubeRelᵉ 0ᵉ a = exo a
  CubeRel→CubeRelᵉ 1ᵉ p i = inS (p i)
  CubeRel→CubeRelᵉ (suc (suc n)) a₋ (i , φ) =
    concat' (λ t → CubeRel→CubeRelᵉ (suc n) (a₋ t) φ) i
-}


CurryIˣFun : {n : ℕᵉ} (P : Iˣ n → Type ℓ) → SSet ℓ
CurryIˣFun {n = 0ᵉ} P = Exo (P tt)
CurryIˣFun {n = 1ᵉ} P = (i : I) → P i
CurryIˣFun {n = suc (suc n)} P = (i : I) → CurryIˣFun (λ φ → P (i , φ))

CurryIˣFunᵉ : {n : ℕᵉ} (P : Iˣ n → SSet ℓ) → SSet ℓ
CurryIˣFunᵉ {n = 0ᵉ} P = P tt
CurryIˣFunᵉ {n = 1ᵉ} P = (i : I) → P i
CurryIˣFunᵉ {n = suc (suc n)} P = (i : I) → CurryIˣFunᵉ (λ φ → P (i , φ))

curryIˣ : {n : ℕᵉ} {P : Iˣ n → Type ℓ} → ((φ : Iˣ n) → P φ) → CurryIˣFun P
curryIˣ {n = 0ᵉ} p = exo (p tt)
curryIˣ {n = 1ᵉ} p = p
curryIˣ {n = suc (suc n)} p i = curryIˣ λ φ → p (i , φ)

curryIˣᵉ : {n : ℕᵉ} {P : Iˣ n → SSet ℓ} → ((φ : Iˣ n) → P φ) → CurryIˣFunᵉ P
curryIˣᵉ {n = 0ᵉ} p = p tt
curryIˣᵉ {n = 1ᵉ} p = p
curryIˣᵉ {n = suc (suc n)} p i = curryIˣᵉ λ φ → p (i , φ)

uncurryIˣ : {n : ℕᵉ} {P : Iˣ n → Type ℓ} → CurryIˣFun P → (φ : Iˣ n) → P φ
uncurryIˣ {n = 0ᵉ} (exo p) tt = p
uncurryIˣ {n = 1ᵉ} p = p
uncurryIˣ {n = suc (suc n)} p (i , φ) = uncurryIˣ (p i) φ

uncurryIˣᵉ : {n : ℕᵉ} {P : Iˣ n → SSet ℓ} → CurryIˣFunᵉ P → (φ : Iˣ n) → P φ
uncurryIˣᵉ {n = 0ᵉ} p tt = p
uncurryIˣᵉ {n = 1ᵉ} p = p
uncurryIˣᵉ {n = suc (suc n)} p (i , φ) = uncurryIˣᵉ (p i) φ

retcurryˣᵉ : {n : ℕᵉ} {P : Iˣ n → SSet ℓ} (f : (φ : Iˣ n) → P φ) → (φ : Iˣ n) → uncurryIˣᵉ (curryIˣᵉ f) φ ≡ᵉ f φ
retcurryˣᵉ {n = 0ᵉ} f tt = reflᵉ
retcurryˣᵉ {n = 1ᵉ} f _  = reflᵉ
retcurryˣᵉ {n = suc (suc n)} p (i , _) = retcurryˣᵉ (λ φ → p (i , φ)) _

substCurryIˣFunᵉ :  {n : ℕᵉ} {P Q : Iˣ n → SSet ℓ} → ((φ : Iˣ n) → P φ ≡ᵉ Q φ) → CurryIˣFunᵉ P → CurryIˣFunᵉ Q
substCurryIˣFunᵉ p f = curryIˣᵉ λ φ → transportᵉ (p φ) (uncurryIˣᵉ f φ)


ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → SSet ℓ
ΠCubeᵉ 0ᵉ A = Exo A
ΠCubeᵉ (suc n) A = CurryIˣFun {n = suc n} (λ _ → A)

curryCubeᵉ : {n : ℕᵉ} → Cubeᵉ n A → ΠCubeᵉ n A
curryCubeᵉ {n = zero}  a = a
curryCubeᵉ {n = suc n} a = curryIˣ (λ φ → outS (a .snd φ))

uncurryCubeᵉ : {n : ℕᵉ} → ΠCubeᵉ n A → Cubeᵉ n A
uncurryCubeᵉ {n = zero}  a = a
uncurryCubeᵉ {n = suc n} a = _ , λ φ → inS (uncurryIˣ a φ)


∂ΠCubeᵉ : (n : ℕᵉ) (A : Type ℓ) → SSet ℓ
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


ΠCubeRelᵉ : (n : ℕᵉ) (A : Type ℓ) → ∂ΠCubeᵉ n A → SSet ℓ
ΠCubeRelᵉ 0ᵉ A _ = Exo A
ΠCubeRelᵉ (suc n) A ∂ᵉ = CurryIˣFunᵉ (λ φ → A [ _ ↦ uncurryIˣᵉ {n = suc n} ∂ᵉ φ ])


CubeRel→ΠCubeRelᵉ : (n : ℕᵉ) (∂ : ∂Cube (ℕᵉ→ℕ n) A) → CubeRel (ℕᵉ→ℕ n) A ∂ → ΠCubeRelᵉ n A (∂Cube→∂ΠCubeᵉ n ∂)
CubeRel→ΠCubeRelᵉ 0ᵉ _ a = exo a
CubeRel→ΠCubeRelᵉ {A = A} (suc n) ∂ a =
  substCurryIˣFunᵉ
    (λ φ → congᵉ (λ u → A [ _ ↦ u ]) (symᵉ (retcurryˣᵉ (∂Cube→∂Cubeᵉ _ ∂) φ)))
    (curryIˣᵉ (Cube→Cubeᵉ (suc n) (∂ , a) .snd))


--fillCube : (n : ℕᵉ) (A : Type ℓ) → SSet ℓ
--fillCube n A = (∂ : ∂ΠCubeᵉ n A) → ΠCubeRelᵉ n A ∂
