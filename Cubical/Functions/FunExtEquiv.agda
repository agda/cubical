{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.FunExtEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Vec
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- Function extensionality is an equivalence
module _ {A : Type ℓ} {B : A → I → Type ℓ₁}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1} where

  private
    fib : (p : PathP (λ i → ∀ x → B x i) f g) → fiber funExt p
    fib p = (funExt⁻ p , refl)

    funExt-fiber-isContr : ∀ p → (fi : fiber funExt p) → fib p ≡ fi
    funExt-fiber-isContr p (h , eq) i = (funExt⁻ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt-isEquiv : isEquiv funExt
  equiv-proof funExt-isEquiv p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : (∀ x → PathP (B x) (f x) (g x)) ≃ PathP (λ i → ∀ x → B x i) f g
  funExtEquiv = (funExt , funExt-isEquiv)

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

    fib : (p : PathP (λ i → ∀ x y → C x y i) f g) → fiber funExt₂ p
    fib p = (appl₂ p , refl)

    funExt₂-fiber-isContr : ∀ p → (fi : fiber funExt₂ p) → fib p ≡ fi
    funExt₂-fiber-isContr p (h , eq) i = (appl₂ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt₂-isEquiv : isEquiv funExt₂
  equiv-proof funExt₂-isEquiv p = (fib p , funExt₂-fiber-isContr p)

  funExt₂Equiv : (∀ x y → PathP (C x y) (f x y) (g x y)) ≃ (PathP (λ i → ∀ x y → C x y i) f g)
  funExt₂Equiv = (funExt₂ , funExt₂-isEquiv)

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

    fib : (p : PathP (λ i → ∀ x y z → D x y z i) f g) → fiber funExt₃ p
    fib p = (appl₃ p , refl)

    funExt₃-fiber-isContr : ∀ p → (fi : fiber funExt₃ p) → fib p ≡ fi
    funExt₃-fiber-isContr p (h , eq) i = (appl₃ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt₃-isEquiv : isEquiv funExt₃
  equiv-proof funExt₃-isEquiv p = (fib p , funExt₃-fiber-isContr p)

  funExt₃Equiv : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≃ (PathP (λ i → ∀ x y z → D x y z i) f g)
  funExt₃Equiv = (funExt₃ , funExt₃-isEquiv)

  funExt₃Path : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≡ (PathP (λ i → ∀ x y z → D x y z i) f g)
  funExt₃Path = ua funExt₃Equiv


-- n-ary non-dependent funext
nAryFunExt : (n : ℕ) {X : Type ℓ} {Y : I → Type ℓ₁} (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
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
