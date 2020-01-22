{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.PathSplitEquiv
open isPathSplitEquiv
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc; ℕ→ℕ₋₁)
import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification

open import Cubical.HITs.Truncation.Base

open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₋₁)
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.2GroupoidTruncation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

sphereFill : (n : ℕ₋₁) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ₋₁ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilled∥∥ : {n : ℕ₋₂} → isSphereFilled (1+ n) (∥ A ∥ n)
isSphereFilled∥∥ {n = neg2}  f = hub f , ⊥-elimDep
isSphereFilled∥∥ {n = suc _} f = hub f , spoke f

isSphereFilled→isOfHLevelSuc : {n : ℕ₋₂} → isSphereFilled (1+ suc n) A → isOfHLevel (2+ suc n) A
isSphereFilled→isOfHLevelSuc {A = A} {neg2} h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevelSuc {A = A} {suc n} h x y = isSphereFilled→isOfHLevelSuc (helper h x y)
  where
    helper : {n : ℕ₋₂} → isSphereFilled (suc (1+ suc n)) A → (x y : A) → isSphereFilled (1+ suc n) (x ≡ y)
    helper {n = n} h x y f = l , r
      where
        f' : Susp (S (1+ suc n)) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill (suc (1+ suc n)) f'
        u = h f'

        z : A
        z = fst u

        p : z ≡ x
        p = snd u north

        q : z ≡ y
        q = snd u south

        l : x ≡ y
        l = sym p ∙ q

        r : (s : S (1+ suc n)) → l ≡ f s
        r s i j = hcomp
                    (λ k →
                       λ { (i = i0) → compPath-filler (sym p) q k j
                         ; (i = i1) → snd u (merid s j) k
                         ; (j = i0) → p (k ∨ (~ i))
                         ; (j = i1) → q k
                         })
                  (p ((~ i) ∧ (~ j)))

isOfHLevel→isSphereFilled : {n : ℕ₋₂} → isOfHLevel (2+ n) A → isSphereFilled (1+ n) A
isOfHLevel→isSphereFilled {A = A} {neg2} h f = fst h , λ _ → snd h _
isOfHLevel→isSphereFilled {A = A} {suc neg2} h f = f north , λ _ → h _ _
isOfHLevel→isSphereFilled {A = A} {suc (suc n)} h = helper λ x y → isOfHLevel→isSphereFilled (h x y)
  where
    helper : {n : ℕ₋₂} → ((x y : A) → isSphereFilled (1+ n) (x ≡ y)) → isSphereFilled (suc (1+ n)) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S (1+ n) → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill (1+ n) f'
      h' = h (f north) (f south) f'

      r : (x : S (suc (1+ n))) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                        ; (i = i1) → h' .snd x (~ k) j
                                        ; (j = i0) → f north
                                        ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

-- isNull (S n) A ≃ (isSphereFilled n A) × (∀ (x y : A) → isSphereFilled n (x ≡ y))

isOfHLevel→isSnNull : {n : ℕ₋₂} → isOfHLevel (2+ n) A → isNull (S (1+ n)) A
fst (sec (isOfHLevel→isSnNull h)) f     = fst (isOfHLevel→isSphereFilled h f)
snd (sec (isOfHLevel→isSnNull h)) f i s = snd (isOfHLevel→isSphereFilled h f) s i
fst (secCong (isOfHLevel→isSnNull h) x y) p       = fst (isOfHLevel→isSphereFilled (hLevelPath _ h x y) (appl p))
snd (secCong (isOfHLevel→isSnNull h) x y) p i j s = snd (isOfHLevel→isSphereFilled (hLevelPath _ h x y) (appl p)) s i j

isSnNull→isOfHLevel : {n : ℕ₋₂} → isNull (S (1+ n)) A → isOfHLevel (2+ n) A
isSnNull→isOfHLevel {n = neg2}  nA = fst (sec nA) ⊥-elim , λ y → fst (secCong nA _ y) (funExt ⊥-elimDep)
isSnNull→isOfHLevel {n = suc n} nA = isSphereFilled→isOfHLevelSuc (λ f → fst (sec nA) f , λ s i → snd (sec nA) f i s)

isOfHLevel∥∥ : (n : ℕ₋₂) → isOfHLevel (2+ n) (∥ A ∥ n)
isOfHLevel∥∥ neg2    = hub ⊥-elim , λ _ → ≡hub ⊥-elim
isOfHLevel∥∥ (suc n) = isSphereFilled→isOfHLevelSuc isSphereFilled∥∥
-- isOfHLevel∥∥ n = isSnNull→isOfHLevel isNull-Null

ind : {n : ℕ₋₂}
      {B : ∥ A ∥ n → Type ℓ'}
      (hB : (x : ∥ A ∥ n) → isOfHLevel (2+ n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ n) →
      B x
ind hB = ind-Null (λ x → isOfHLevel→isSnNull (hB x))

ind2 : {n : ℕ₋₂}
       {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
       (hB : ((x y : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ n) →
       B x y
ind2 {n = n} hB g = ind (λ _ → hLevelPi (2+ n) (λ _ → hB _ _)) λ a →
                    ind (λ _ → hB _ _) (λ b → g a b)

ind3 : {n : ℕ₋₂}
       {B : (x y z : ∥ A ∥ n) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ n) →
       B x y z
ind3 {n = n} hB g = ind2 (λ _ _ → hLevelPi (2+ n) (hB _ _)) λ a b →
                    ind (λ _ → hB _ _ _) (λ c → g a b c)

idemTrunc : (n : ℕ₋₂) → isOfHLevel (2+ n) A → (∥ A ∥ n) ≃ A
idemTrunc {A = A} n hA = isoToEquiv (iso f g f-g g-f)
  where
  f : ∥ A ∥ n → A
  f = ind (λ _ → hA) λ a → a

  g : A → ∥ A ∥ n
  g = ∣_∣

  f-g : ∀ x → f (g x) ≡ x
  f-g x = refl

  g-f : ∀ x → g (f x) ≡ x
  g-f = ind (λ _ → hLevelPath (2+ n) (isOfHLevel∥∥ n) _ _) (λ _ → refl)

propTrunc≃Trunc-1 : ∥ A ∥₋₁ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (elimPropTrunc (λ _ → isOfHLevel∥∥ -1) ∣_∣)
      (ind (λ _ → propTruncIsProp) ∣_∣)
      (ind (λ _ → hLevelPath 1 (isOfHLevel∥∥ -1) _ _) (λ _ → refl))
      (elimPropTrunc (λ _ → hLevelPath 1 squash _ _) (λ _ → refl)))

setTrunc≃Trunc0 : ∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (elimSetTrunc (λ _ → isOfHLevel∥∥ 0) ∣_∣)
      (ind (λ _ → squash₀) ∣_∣₀)
      (ind (λ _ → hLevelPath 2 (isOfHLevel∥∥ 0) _ _) (λ _ → refl))
      (elimSetTrunc (λ _ → hLevelPath 2 squash₀ _ _) (λ _ → refl)))

groupoidTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (groupoidTruncElim _ _ (λ _ → isOfHLevel∥∥ 1) ∣_∣)
      (ind (λ _ → squash₁) ∣_∣₁)
      (ind (λ _ → hLevelPath 3 (isOfHLevel∥∥ 1) _ _) (λ _ → refl))
      (groupoidTruncElim _ _ (λ _ → hLevelPath 3 squash₁ _ _) (λ _ → refl)))

2groupoidTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
2groupoidTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (g2TruncElim _ _ (λ _ → isOfHLevel∥∥ 2) ∣_∣)
      (ind (λ _ → squash₂) ∣_∣₂)
      (ind (λ _ → hLevelPath 4 (isOfHLevel∥∥ 2) _ _) (λ _ → refl))
      (g2TruncElim _ _ (λ _ → hLevelPath 4 squash₂ _ _) (λ _ → refl)))
