{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.HITs.Truncation.Base
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn
open import Cubical.Data.Empty
open import Cubical.HITs.Susp

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    n : ℕ

sphereFill : (f : S n → A) → Type _
sphereFill {n = n} {A = A} f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill f

isSphereFilled∥∥ : isSphereFilled n (∥ A ∥ n)
isSphereFilled∥∥ f = (top f) , (rays f)

isSphereFilled→isOfHLevel : isSphereFilled (suc n) A → isOfHLevel (suc n) A
isSphereFilled→isOfHLevel {n = 0} {A = A} h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevel {n = suc n} {A = A} h x y = isSphereFilled→isOfHLevel (helper h x y)
  where
    helper : {n : ℕ} → isSphereFilled (suc n) A → (x y : A) → isSphereFilled n (x ≡ y)
    helper {n = n} h x y f = l , r
      where
        f' : Susp (S n) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill f'
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

isOfHLevel→isSphereFilled : isOfHLevel n A → isSphereFilled n A
isOfHLevel→isSphereFilled {n = 0} h f = (fst h) , (λ _ → snd h _ )
isOfHLevel→isSphereFilled {n = 1} h f = (f north) , (λ _ → h _ _)
isOfHLevel→isSphereFilled {n = suc (suc n)} {A = A} h = helper λ x y → isOfHLevel→isSphereFilled {n = (suc n)} (h x y)
  where
    helper : {n : ℕ} → ((x y : A) → isSphereFilled n (x ≡ y)) → isSphereFilled (suc n) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S n → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill f'
      h' = h (f north) (f south) f'

      r : (x : S (suc n)) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                        ; (i = i1) → h' .snd x (~ k) j
                                        ; (j = i0) → f north
                                        ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

isOfHLevel∥∥ : isOfHLevel (suc n) (∥ A ∥ (suc n))
isOfHLevel∥∥ = isSphereFilled→isOfHLevel isSphereFilled∥∥

ind : {B : ∥ A ∥ n → Type ℓ'}
      (hB : (x : ∥ A ∥ n) → isOfHLevel n (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ n) →
      B x
ind hB g (∣ a ∣ ) = g a
ind {B = B} hB g (top f) = isOfHLevel→isSphereFilled (hB (top f)) (λ x → subst B (sym (rays f x)) (ind hB g (f x)) ) .fst
ind {B = B} hB g (rays f x i) = toPathP {A = λ i → B (rays f x (~ i))} (sym (isOfHLevel→isSphereFilled (hB (top f)) (λ x → subst B (sym (rays f x)) (ind hB g (f x))) .snd x)) (~ i)

ind2 : {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
       (hB : ((x y : ∥ A ∥ n) → isOfHLevel n (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ n) →
       B x y
ind2 {n = n} hB g = ind (λ _ → hLevelPi n (λ _ → hB _ _)) λ a →
                    ind (λ _ → hB _ _) (λ b → g a b)

ind3 : {B : (x y z : ∥ A ∥ n) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ n) → isOfHLevel n (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ n) →
       B x y z
ind3 {n = n} hB g = ind2 (λ _ _ → hLevelPi n (hB _ _)) λ a b →
                    ind (λ _ → hB _ _ _) (λ c → g a b c)

-- this demostrates that the current def. of isOfHLevel could be inconvenient sometimes
-- note how similiar the two cases are, and yet we can't combine them
idemTrunc : isOfHLevel (suc n) A → (∥ A ∥ (suc n)) ≃ A
idemTrunc {n = 0} {A = A} hA = isoToEquiv (iso f g f-g g-f)
  where
    f : ∥ A ∥ 1 → A
    f = ind (λ _ → hA) λ a → a

    g : A → ∥ A ∥ 1
    g = ∣_∣

    f-g : ∀ a → f (g a) ≡ a
    f-g a = refl

    g-f : ∀ x → g (f x) ≡ x
    g-f = ind (λ _ → hLevelLift {n = 1} 1 (isOfHLevel∥∥ {n = 0}) _ _) λ _ → refl
idemTrunc {n = suc n} {A = A} hA = isoToEquiv (iso f g f-g g-f)
  where
    f : ∥ A ∥ (suc (suc n)) → A
    f = ind (λ _ → hA) λ a → a

    g : A → ∥ A ∥ (suc (suc n))
    g = ∣_∣

    f-g : ∀ a → f (g a) ≡ a
    f-g a = refl

    g-f : ∀ x → g (f x) ≡ x
    g-f = ind (λ x → hLevelLift {n = suc n} 1 (isOfHLevel∥∥ {n = suc n} _ _)) λ _ → refl

