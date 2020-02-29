{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.FromNegOne.Properties where

open import Cubical.HITs.Truncation.FromNegOne.Base
open import Cubical.Data.Nat hiding (suc)
open import Cubical.Data.NatMinusOne renaming (suc₋₁ to suc)
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
open import Cubical.HITs.2GroupoidTruncation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

open import Cubical.HITs.Truncation.Properties using (sphereFill; isSphereFilled)

isSphereFilled∥∥ : {n : ℕ₋₁} → isSphereFilled (suc n) (∥ A ∥ n)
isSphereFilled∥∥ f = (hub f) , (spoke f)

isSphereFilled→isOfHLevel : (n : ℕ₋₁) → isSphereFilled (suc n) A → isOfHLevel (1 + 1+ n) A
isSphereFilled→isOfHLevel {A = A} neg1 h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevel {A = A} (ℕ→ℕ₋₁ n) h x y = isSphereFilled→isOfHLevel (-1+ n) (helper h x y)
  where
    helper : {n : ℕ₋₁} → isSphereFilled (suc n) A → (x y : A) → isSphereFilled n (x ≡ y)
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

isOfHLevel→isSphereFilled : (n : ℕ₋₁) → isOfHLevel (1 + 1+ n) A → isSphereFilled (suc n) A
isOfHLevel→isSphereFilled neg1 h f = (f north) , (λ _ → h _ _)
isOfHLevel→isSphereFilled {A = A} (ℕ→ℕ₋₁ n) h = helper λ x y → isOfHLevel→isSphereFilled (-1+ n) (h x y)
  where
    helper : {n : ℕ₋₁} → ((x y : A) → isSphereFilled n (x ≡ y)) → isSphereFilled (suc n) A
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
isOfHLevel∥∥ n = isSphereFilled→isOfHLevel n isSphereFilled∥∥

ind : {n : ℕ₋₁}
      {B : ∥ A ∥ n → Type ℓ'}
      (hB : (x : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ n) →
      B x
ind hB g (∣ a ∣ ) = g a
ind {B = B} hB g (hub f) =
  isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (ind hB g (f x)) ) .fst
ind {B = B} hB g (spoke f x i) =
  toPathP {A = λ i → B (spoke f x (~ i))}
    (sym (isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (ind hB g (f x))) .snd x))
    (~ i)

ind2 : {n : ℕ₋₁}
       {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
       (hB : ((x y : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ n) →
       B x y
ind2 {n = n} hB g = ind (λ _ → isOfHLevelPi (1 + 1+ n) (λ _ → hB _ _)) λ a →
                    ind (λ _ → hB _ _) (λ b → g a b)

ind3 : {n : ℕ₋₁}
       {B : (x y z : ∥ A ∥ n) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ n) → isOfHLevel (1 + 1+ n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ n) →
       B x y z
ind3 {n = n} hB g = ind2 (λ _ _ → isOfHLevelPi (1 + 1+ n) (hB _ _)) λ a b →
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
  g-f = ind (λ _ → isOfHLevelPath (1 + 1+ n) (isOfHLevel∥∥ n) _ _) (λ _ → refl)

propTrunc≃Trunc-1 : ∥ A ∥₋₁ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (elimPropTrunc (λ _ → isOfHLevel∥∥ -1) ∣_∣)
      (ind (λ _ → propTruncIsProp) ∣_∣)
      (ind (λ _ → isOfHLevelPath 1 (isOfHLevel∥∥ -1) _ _) (λ _ → refl))
      (elimPropTrunc (λ _ → isOfHLevelPath 1 squash _ _) (λ _ → refl)))

setTrunc≃Trunc0 : ∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (elimSetTrunc (λ _ → isOfHLevel∥∥ 0) ∣_∣)
      (ind (λ _ → squash₀) ∣_∣₀)
      (ind (λ _ → isOfHLevelPath 2 (isOfHLevel∥∥ 0) _ _) (λ _ → refl))
      (elimSetTrunc (λ _ → isOfHLevelPath 2 squash₀ _ _) (λ _ → refl)))

groupoidTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (groupoidTruncElim _ _ (λ _ → isOfHLevel∥∥ 1) ∣_∣)
      (ind (λ _ → squash₁) ∣_∣₁)
      (ind (λ _ → isOfHLevelPath 3 (isOfHLevel∥∥ 1) _ _) (λ _ → refl))
      (groupoidTruncElim _ _ (λ _ → isOfHLevelPath 3 squash₁ _ _) (λ _ → refl)))

2groupoidTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
2groupoidTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (g2TruncElim _ _ (λ _ → isOfHLevel∥∥ 2) ∣_∣)
      (ind (λ _ → squash₂) ∣_∣₂)
      (ind (λ _ → isOfHLevelPath 4 (isOfHLevel∥∥ 2) _ _) (λ _ → refl))
      (g2TruncElim _ _ (λ _ → isOfHLevelPath 4 squash₂ _ _) (λ _ → refl)))
