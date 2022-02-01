{- Adjunction between suspension and loop space (Rongji Kang, Oct. 2021)

Main results:

- Ω∙ : ℕ → Pointed ℓ → Pointed ℓ
- ΣΩAdjunction : ((X , x₀) : Pointed ℓ) (Y : Pointed ℓ') → (∙Susp X →∙ Y) ≃ ((X , x₀) →∙ Ω∙ 1 Y)
-}
{-# OPTIONS --safe #-}
module Cubical.HITs.Susp.LoopAdjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Pointed.Base
open import Cubical.Data.Nat.Base
open import Cubical.HITs.Susp.Base

private
  variable
    ℓ ℓ' : Level

Ω∙ : ℕ → Pointed ℓ → Pointed ℓ
Ω∙ 0 X = X
Ω∙ 1 (X , x) = (x ≡ x) , refl
Ω∙ (suc (suc n)) X = Ω∙ 1 (Ω∙ (suc n) X)

ΣX→∙YEquiv : ((X , x₀) : Pointed ℓ) ((Y , y₀) : Pointed ℓ')
           → (Susp∙ X →∙ (Y , y₀)) ≃ (Σ[ y ∈ Y ] (X → (y₀ ≡ y)))
ΣX→∙YEquiv (X , x₀) (Y , y₀) =
  isoToEquiv (iso left→right right→left right→left→right left→right→left)
  where
    left→right : (Susp∙ X →∙ (Y , y₀)) → Σ[ y ∈ Y ] (X → (y₀ ≡ y))
    left→right (f , b) .fst = f south
    left→right (f , b) .snd x = sym b ∙ cong f (merid x)

    right→left : (Σ[ y ∈ Y ] (X → (y₀ ≡ y))) → (Susp∙ X →∙ (Y , y₀))
    right→left (y , g) .fst north = y₀
    right→left (y , g) .fst south = y
    right→left (y , g) .fst (merid x i) = g x i
    right→left (y , g) .snd = refl

    right→left→right : (g : Σ[ y ∈ Y ] (X → (y₀ ≡ y))) → left→right (right→left g) ≡ g
    right→left→right (y , g) i .fst = y
    right→left→right (y , g) i .snd x = lUnit (g x) (~ i)

    left→right→left : (f : Susp∙ X →∙ (Y , y₀)) → right→left (left→right f) ≡ f
    left→right→left (f , b) i .fst north = b (~ i)
    left→right→left (f , b) i .fst south = f south
    left→right→left (f , b) i .fst (merid x j) =
      hcomp (λ k → λ { (i = i0) → compPath-filler (sym b) (cong f (merid x)) k j
                     ; (i = i1) → f (merid x (j ∧ k))
                     ; (j = i0) → b (~ i)
                     ; (j = i1) → f (merid x k) })
            (b (~ (i ∨ j)))
    left→right→left (f , b) i .snd j = b (~ i ∨ j)

X→∙ΩYEquiv : ((X , x₀) : Pointed ℓ)((Y , y₀) : Pointed ℓ')
           → ((X , x₀) →∙ Ω∙ 1 (Y , y₀)) ≃ (Σ[ y ∈ Y ] (X → (y₀ ≡ y)))
X→∙ΩYEquiv (X , x₀) (Y , y₀) =
  isoToEquiv (iso left→right right→left right→left→right left→right→left)
  where
    left→right : ((X , x₀) →∙ Ω∙ 1 (Y , y₀)) → Σ[ y ∈ Y ] (X → (y₀ ≡ y))
    left→right _ .fst = y₀
    left→right (f , b) .snd = f

    right→left : (Σ[ y ∈ Y ] (X → (y₀ ≡ y))) → ((X , x₀) →∙ Ω∙ 1 (Y , y₀))
    right→left (y , g) .fst x = g x ∙ sym (g x₀)
    right→left (y , g) .snd = rCancel (g x₀)

    right→left→right : (g : Σ[ y ∈ Y ] (X → (y₀ ≡ y))) → left→right (right→left g) ≡ g
    right→left→right (y , g) i .fst = g x₀ i
    right→left→right (y , g) i .snd x j =
      hcomp (λ k → λ { (i = i0) → compPath-filler (g x) (sym (g x₀)) k j
                     ; (i = i1) → g x j
                     ; (j = i0) → y₀
                     ; (j = i1) → g x₀ (i ∨ ~ k) })
            (g x j)

    f-filler : ((X , x₀) →∙ Ω∙ 1 (Y , y₀)) → X → (i j k : I) → Y
    f-filler (f , b) x i j k =
      hfill (λ k' → λ { (i = i0) → compPath-filler (f x) (sym (f x₀)) k' j
                      ; (i = i1) → f x j
                      ; (j = i0) → y₀
                      ; (j = i1) → b i (~ k') })
            (inS (f x j)) k

    bottom : ((X , x₀) →∙ Ω∙ 1 (Y , y₀)) → (i j k : I) → Y
    bottom (f , b) i j k =
      hcomp (λ l → λ { (i = i0) → b (~ l) (k ∧ ~ j)
                     ; (i = i1) → b (j ∨ ~ l) k
                     ; (j = i0) → b (~ l) k
                     ; (j = i1) → y₀
                     ; (k = i0) → y₀
                     ; (k = i1) → b (~ l ∨ i) (~ j) })
            y₀

    left→right→left : (f : (X , x₀) →∙ Ω∙ 1 (Y , y₀)) → right→left (left→right f) ≡ f
    left→right→left (f , b) i .fst x j =
      f-filler (f , b) x i j i1
    left→right→left (f , b) i .snd j k =
      hcomp (λ l → λ { (i = i0) → rCancel-filler (f x₀) l j k
                     ; (i = i1) → b j k
                     ; (j = i0) → f-filler (f , b) x₀ i k l
                     ; (j = i1) → y₀
                     ; (k = i0) → y₀
                     ; (k = i1) → b i (~ l ∧ ~ j) })
            (bottom (f , b) i j k)

{- The Main Theorem -}
ΣΩAdjunction : ((X , x₀) : Pointed ℓ) (Y : Pointed ℓ') → (Susp∙ X →∙ Y) ≃ ((X , x₀) →∙ Ω∙ 1 Y)
ΣΩAdjunction X Y = compEquiv (ΣX→∙YEquiv X Y) (invEquiv (X→∙ΩYEquiv X Y))
