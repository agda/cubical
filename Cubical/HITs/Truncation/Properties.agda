{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.HITs.Truncation.Base
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
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

isOfHLevel∥∥ : isOfHLevel (suc n) (∥ A ∥ (suc n))
isOfHLevel∥∥ = isSphereFilled→isOfHLevel isSphereFilled∥∥

