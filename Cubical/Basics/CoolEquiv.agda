{-# OPTIONS --cubical #-}
module Cubical.Basics.CoolEquiv where

open import Cubical.Core.Everything

open import Cubical.Basics.NTypes

record isCoolEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ-max ℓ ℓ') where
  field
   g : B → A
   α : (b : B) → f (g b) ≡ b
   β : (a : A) → g (f a) ≡ a
   αβ : (a : A) → PathP (λ j → f (β a j) ≡ f a) (α (f a)) (λ _ → f a) 

open isCoolEquiv

CoolEquiv : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
CoolEquiv A B = Σ (A → B) (λ f → isCoolEquiv f)

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
         (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) where

  iso→isCoolEquiv : isCoolEquiv f
  iso→isCoolEquiv =
    let aux : A → I → I → A
        aux a k i = hfill (λ l → λ { (i = i0) → g (f (t a l)) ; (i = i1) → t a l }) (inc (g (s (f a) i))) k
    in record { g = g
           ; α = s
           ; β = λ a i → hcomp (λ l → λ { (i = i0) → g (f (t a l)) ; (i = i1) → t a l }) (g (s (f a) i))
           ; αβ = λ a i j →
    let filler : I → I → B
        filler x k = hfill (λ l → λ { (k = i0) → s (f a) l ; (k = i1) → f a }) (inc (f (t a k))) x
    in 
    hcomp (λ k → λ { (i = i0) → s (f (t a k)) j
                   ; (i = i1) → filler j k
                   ; (j = i0) → f (aux a k i)
                   ; (j = i1) → filler i k })
          (s (s (f a) i) j) }
  
  iso→CoolEquiv : CoolEquiv A B
  iso→CoolEquiv = f , iso→isCoolEquiv


CoolEquiv→Equiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → CoolEquiv A B → A ≃ B
CoolEquiv→Equiv {A = A} (f , record { g = g ; α = α ; β = β ; αβ = αβ }) =
  f , record { equiv-proof = λ y → (g y , α y) , λ x →
    let goal : (x : fiber f y) → (g y , α y) ≡ x
        goal x =
          let x1 : A
              x1 = x .fst
              x2 : f x1 ≡ y
              x2 = x .snd
              in λ i → {!!}
    in goal x }

-- Can we prove this directly?
isPropIsCoolEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isProp (isCoolEquiv f)
isPropIsCoolEquiv f p q = {!!}
