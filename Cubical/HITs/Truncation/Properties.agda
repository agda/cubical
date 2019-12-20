{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.HITs.Truncation.Base
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn
open import Cubical.Data.Empty
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₋₁)
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

sphereFill : (n : ℕ) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilled∥∥ : {n : ℕ₋₁} → isSphereFilled (1+ n) (∥ A ∥ n)
isSphereFilled∥∥ f = (top f) , (rays f)

isSphereFilled→isOfHLevel : (n : ℕ) → isSphereFilled n A → isOfHLevel (1 + n) A
isSphereFilled→isOfHLevel {A = A} 0 h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevel {A = A} (suc n) h x y = isSphereFilled→isOfHLevel n (helper h x y)
  where
    helper : {n : ℕ} → isSphereFilled (suc n) A → (x y : A) → isSphereFilled n (x ≡ y)
    helper {n = n} h x y f = l , r
      where
        f' : Susp (S n) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill (suc n) f'
        u = h f'

        z : A
        z = fst u

        p : z ≡ x
        p = snd u north

        q : z ≡ y
        q = snd u south

        l : x ≡ y
        l = sym p ∙ q

        r : (s : S n) → l ≡ f s
        r s i j = hcomp
                    (λ k →
                       λ { (i = i0) → compPath-filler (sym p) q k j
                         ; (i = i1) → snd u (merid s j) k
                         ; (j = i0) → p (k ∨ (~ i))
                         ; (j = i1) → q k
                         })
                  (p ((~ i) ∧ (~ j)))

isOfHLevel→isSphereFilled : (n : ℕ) → isOfHLevel (1 + n) A → isSphereFilled n A
isOfHLevel→isSphereFilled 0 h f = (f north) , (λ _ → h _ _)
isOfHLevel→isSphereFilled {A = A} (suc n) h = helper λ x y → isOfHLevel→isSphereFilled n (h x y)
  where
    helper : {n : ℕ} → ((x y : A) → isSphereFilled n (x ≡ y)) → isSphereFilled (suc n) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S n → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill n f'
      h' = h (f north) (f south) f'

      r : (x : S (suc n)) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                        ; (i = i1) → h' .snd x (~ k) j
                                        ; (j = i0) → f north
                                        ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

isOfHLevel∥∥ : (n : ℕ₋₁) → isOfHLevel (1 + 1+ n) (∥ A ∥ n)
isOfHLevel∥∥ n = isSphereFilled→isOfHLevel (1+ n) isSphereFilled∥∥

ind : {n : ℕ₋₁}
      {B : ∥ A ∥ n → Type ℓ'}
      (hB : (x : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ n) →
      B x
ind hB g (∣ a ∣ ) = g a
ind {B = B} hB g (top f) =
  isOfHLevel→isSphereFilled _ (hB (top f)) (λ x → subst B (sym (rays f x)) (ind hB g (f x)) ) .fst
ind {B = B} hB g (rays f x i) =
  toPathP {A = λ i → B (rays f x (~ i))}
    (sym (isOfHLevel→isSphereFilled _ (hB (top f)) (λ x → subst B (sym (rays f x)) (ind hB g (f x))) .snd x))
    (~ i)

ind2 : {n : ℕ₋₁}
       {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
       (hB : ((x y : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ n) →
       B x y
ind2 {n = n} hB g = ind (λ _ → hLevelPi (1 + 1+ n) (λ _ → hB _ _)) λ a →
                    ind (λ _ → hB _ _) (λ b → g a b)

ind3 : {n : ℕ₋₁}
       {B : (x y z : ∥ A ∥ n) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ n) →
       B x y z
ind3 {n = n} hB g = ind2 (λ _ _ → hLevelPi (1 + 1+ n) (hB _ _)) λ a b →
                    ind (λ _ → hB _ _ _) (λ c → g a b c)

idemTrunc : (n : ℕ₋₁) → isOfHLevel (1 + 1+ n) A → (∥ A ∥ n) ≃ A
idemTrunc {A = A} n hA = isoToEquiv (iso f g f-g g-f)
  where
  f : ∥ A ∥ n → A
  f = ind (λ _ → hA) λ a → a

  g : A → ∥ A ∥ n
  g = ∣_∣

  f-g : ∀ a → f (g a) ≡ a
  f-g a = refl

  g-f : ∀ x → g (f x) ≡ x
  g-f = ind (λ _ → hLevelSuc (1+ n) _ (hLevelPath (1+ n) (isOfHLevel∥∥ n) _ _)) (λ _ → refl)

propTrunc≃Trunc-1 : ∥ A ∥₋₁ ≃ ∥ A ∥ neg1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (elimPropTrunc (λ _ → isOfHLevel∥∥ neg1) ∣_∣)
      (ind (λ _ → propTruncIsProp) ∣_∣)
      (ind (λ _ → hLevelSuc 0 _ (hLevelPath 0 (isOfHLevel∥∥ neg1) _ _)) (λ _ → refl))
      (elimPropTrunc (λ _ → hLevelSuc 0 _ (hLevelPath 0 propTruncIsProp _ _)) (λ _ → refl)))

setTrunc≃Trunc0 : ∥ A ∥₀ ≃ ∥ A ∥ (suc neg1)
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (elimSetTrunc (λ _ → isOfHLevel∥∥ (suc neg1)) ∣_∣)
      (ind (λ _ → squash₀) ∣_∣₀)
      (ind (λ _ → hLevelSuc 1 _ (hLevelPath 1 (isOfHLevel∥∥ (suc neg1)) _ _)) (λ _ → refl))
      (elimSetTrunc (λ _ → hLevelSuc 1 _ (hLevelPath 1 squash₀ _ _)) (λ _ → refl)))

groupoidTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ (suc (suc neg1))
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (groupoidTruncElim _ _ (λ _ → isOfHLevel∥∥ (suc (suc neg1))) ∣_∣)
      (ind (λ _ → squash₁) ∣_∣₁)
      (ind (λ _ → hLevelSuc 2 _ (hLevelPath 2 (isOfHLevel∥∥ (suc (suc neg1))) _ _)) (λ _ → refl))
      (groupoidTruncElim _ _ (λ _ → hLevelSuc 2 _ (hLevelPath 2 squash₁ _ _)) (λ _ → refl)))
