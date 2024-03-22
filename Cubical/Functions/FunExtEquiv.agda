{-# OPTIONS --safe #-}
module Cubical.Functions.FunExtEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Vec.Base
open import Cubical.Data.Vec.NAry
open import Cubical.Data.Nat

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- Function extensionality is an equivalence
module _ {A : Type ℓ} {B : A → I → Type ℓ₁}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1} where

  funExtEquiv : (∀ x → PathP (B x) (f x) (g x)) ≃ PathP (λ i → ∀ x → B x i) f g
  unquoteDef funExtEquiv = defStrictEquiv funExtEquiv funExt funExt⁻

  funExtPath : (∀ x → PathP (B x) (f x) (g x)) ≡ PathP (λ i → ∀ x → B x i) f g
  funExtPath = ua funExtEquiv

  funExtIso : Iso (∀ x → PathP (B x) (f x) (g x)) (PathP (λ i → ∀ x → B x i) f g)
  funExtIso = iso funExt funExt⁻ (λ x → refl {x = x}) (λ x → refl {x = x})

-- Function extensionality for binary functions
funExt₂ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → I → Type ℓ₂}
          {f : (x : A) → (y : B x) → C x y i0}
          {g : (x : A) → (y : B x) → C x y i1}
          → ((x : A) (y : B x) → PathP (C x y) (f x y) (g x y))
          → PathP (λ i → ∀ x y → C x y i) f g
funExt₂ p i x y = p x y i

-- Function extensionality for binary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → I → Type ℓ₂}
         {f : (x : A) → (y : B x) → C x y i0}
         {g : (x : A) → (y : B x) → C x y i1} where
  private
    appl₂ : PathP (λ i → ∀ x y → C x y i) f g → ∀ x y → PathP (C x y) (f x y) (g x y)
    appl₂ eq x y i = eq i x y

  funExt₂Equiv : (∀ x y → PathP (C x y) (f x y) (g x y)) ≃ (PathP (λ i → ∀ x y → C x y i) f g)
  unquoteDef funExt₂Equiv = defStrictEquiv funExt₂Equiv funExt₂ appl₂

  funExt₂Path : (∀ x y → PathP (C x y) (f x y) (g x y)) ≡ (PathP (λ i → ∀ x y → C x y i) f g)
  funExt₂Path = ua funExt₂Equiv


-- Function extensionality for ternary functions
funExt₃ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
          {D : (x : A) → (y : B x) → C x y → I → Type ℓ₃}
          {f : (x : A) → (y : B x) → (z : C x y) → D x y z i0}
          {g : (x : A) → (y : B x) → (z : C x y) → D x y z i1}
        → ((x : A) (y : B x) (z : C x y) → PathP (D x y z) (f x y z) (g x y z))
        → PathP (λ i → ∀ x y z → D x y z i) f g
funExt₃ p i x y z = p x y z i

-- Function extensionality for ternary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
         {D : (x : A) → (y : B x) → C x y → I → Type ℓ₃}
         {f : (x : A) → (y : B x) → (z : C x y) → D x y z i0}
         {g : (x : A) → (y : B x) → (z : C x y) → D x y z i1} where
  private
    appl₃ : PathP (λ i → ∀ x y z → D x y z i) f g → ∀ x y z → PathP (D x y z) (f x y z) (g x y z)
    appl₃ eq x y z i = eq i x y z

  funExt₃Equiv : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≃ (PathP (λ i → ∀ x y z → D x y z i) f g)
  unquoteDef funExt₃Equiv = defStrictEquiv funExt₃Equiv funExt₃ appl₃

  funExt₃Path : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≡ (PathP (λ i → ∀ x y z → D x y z i) f g)
  funExt₃Path = ua funExt₃Equiv


-- n-ary non-dependent funext
nAryFunExt : {X : Type ℓ} {Y : I → Type ℓ₁} (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
           → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
           → PathP (λ i → nAryOp n X (Y i)) fX fY
nAryFunExt zero fX fY p        = p []
nAryFunExt (suc n) fX fY p i x = nAryFunExt n (fX x) (fY x) (λ xs → p (x ∷ xs)) i

-- n-ary funext⁻
nAryFunExt⁻ : (n : ℕ) {X : Type ℓ} {Y : I → Type ℓ₁} (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
           → PathP (λ i → nAryOp n X (Y i)) fX fY
           → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
nAryFunExt⁻ zero fX fY p [] = p
nAryFunExt⁻ (suc n) fX fY p (x ∷ xs) = nAryFunExt⁻ n (fX x) (fY x) (λ i → p i x) xs

nAryFunExtEquiv : (n : ℕ) {X : Type ℓ} {Y : I → Type ℓ₁} (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
  → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs)) ≃ PathP (λ i → nAryOp n X (Y i)) fX fY
nAryFunExtEquiv n {X} {Y} fX fY = isoToEquiv (iso (nAryFunExt n fX fY) (nAryFunExt⁻ n fX fY)
                                              (linv n fX fY) (rinv n fX fY))
  where
  linv : (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
    (p : PathP (λ i → nAryOp n X (Y i)) fX fY)
    → nAryFunExt n fX fY (nAryFunExt⁻ n fX fY p) ≡ p
  linv zero fX fY p          = refl
  linv (suc n) fX fY p i j x = linv n (fX x) (fY x) (λ k → p k x) i j

  rinv : (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
         (p : (xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
       → nAryFunExt⁻ n fX fY (nAryFunExt n fX fY p) ≡ p
  rinv zero fX fY p i []          = p []
  rinv (suc n) fX fY p i (x ∷ xs) = rinv n (fX x) (fY x) (λ ys i → p (x ∷ ys) i) i xs

-- Funext when the domain also depends on the interval

funExtDep : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  → PathP (λ i → (x : A i) → B i x) f g
funExtDep {A = A} {B} {f} {g} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i) (h (λ j → coei→j A i j x) i)

funExtDep⁻ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → PathP (λ i → (x : A i) → B i x) f g
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
funExtDep⁻ q p i = q i (p i)

funExtDepEquiv : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  ≃ PathP (λ i → (x : A i) → B i x) f g
funExtDepEquiv {A = A} {B} {f} {g} = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = funExtDep
  isom .inv = funExtDep⁻
  isom .rightInv q m i x =
    transp
      (λ k → B i (coei→i A i x (k ∨ m)))
      (m ∨ i ∨ ~ i)
      (q i (coei→i A i x m))
  isom .leftInv h m p i =
    transp
      (λ k → B i (lemi→i m k))
      (m ∨ i ∨ ~ i)
      (h (λ j → lemi→j j m) i)
    where
    lemi→j : ∀ j → coei→j A i j (p i) ≡ p j
    lemi→j j k = coePath A (λ i → p i) i j k

    lemi→i : PathP (λ m → lemi→j i m ≡ p i) (coei→i A i (p i)) refl
    lemi→i m k = coei→i A i (p i) (m ∨ k)

-- Funext for non-dependent functions but where both domain and
-- codomain depend on the interval. In this case we can omit the
-- outer transp in funExtDep.

funExtNonDep : {A : I → Type ℓ} {B : I → Type ℓ₁}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  → PathP (λ i → A i → B i) f g
funExtNonDep {A = A} h i x = h (λ j → coei→j A i j x) i

funExtNonDep⁻ : {A : I → Type ℓ} {B : I → Type ℓ₁}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → PathP (λ i → A i → B i) f g
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
funExtNonDep⁻ = funExtDep⁻

funExtNonDepEquiv : {A : I → Type ℓ} {B : I → Type ℓ₁}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g
funExtNonDepEquiv {A = A} = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = funExtNonDep
  isom .inv = funExtNonDep⁻
  isom .rightInv q m i x = q i (coei→i A i x m)
  isom .leftInv h m p i = h (λ j → lemi→j j m) i
    where
    lemi→j : ∀ j → coei→j A i j (p i) ≡ p j
    lemi→j j k = coePath A (λ i → p i) i j k

heteroHomotopy≃Homotopy : {A : I → Type ℓ} {B : (i : I) → Type ℓ₁}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ ((x₀ : A i0) → PathP B (f x₀) (g (transport (λ i → A i) x₀)))
heteroHomotopy≃Homotopy {A = A} {B} {f} {g} = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun h x₀ = h (isContrSinglP A x₀ .fst .snd)
  isom .inv k {x₀} {x₁} p =
    subst (λ fib → PathP B (f x₀) (g (fib .fst))) (isContrSinglP A x₀ .snd (x₁ , p)) (k x₀)
  isom .rightInv k = funExt λ x₀ →
    cong (λ α → subst (λ fib → PathP B (f x₀) (g (fib .fst))) α (k x₀))
      (isProp→isSet isPropSinglP (isContrSinglP A x₀ .fst) _
        (isContrSinglP A x₀ .snd (isContrSinglP A x₀ .fst))
        refl)
    ∙ transportRefl (k x₀)
  isom .leftInv h j {x₀} {x₁} p =
    transp
      (λ i → PathP B (f x₀) (g (isContrSinglP A x₀ .snd (x₁ , p) (i ∨ j) .fst)))
      j
      (h (isContrSinglP A x₀ .snd (x₁ , p) j .snd))
