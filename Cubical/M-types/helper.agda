
{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

module Cubical.M-types.helper where

identity-x : ∀ {ℓ} {A B : Set ℓ} (k : A -> A) -> k ≡ idfun A -> ∀ (x : A) -> k x ≡ x
identity-x {A = A} k = funExt⁻

-- Right
extent-r : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : C -> A) -> a ≡ b -> a ∘ f ≡ b ∘ f
extent-r = λ f x i → x i ∘ f

identity-f-r : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : B -> A) -> k ∘ f ≡ f
identity-f-r {A = A} {k = k} p f = extent-r {a = k} {b = idfun A} f p 

-- Left
extent-l : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : B -> C) -> a ≡ b -> f ∘ a ≡ f ∘ b
extent-l = λ f x i → f ∘ x i

identity-f-l : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : A -> B) -> f ∘ k ≡ f
identity-f-l {A = A} {k = k} p f = extent-l {a = k} {b = idfun A} f p 

-- General

≡-rel-a-monomorphism : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> {f g : C -> A} -> (a ∘ f ≡ a ∘ g) -> (f ≡ g)
≡-rel-a-monomorphism a b left right {f = f} {g = g} p = λ i →
  compPath-filler {x = f} {y = (b ∘ a ∘ f)} {z = g}
    (sym (identity-f-r right f))
    (λ j → compPath-filler {y = b ∘ a ∘ g}
      (λ k → b ∘ p k)
      (identity-f-r right g)
        j j)
      i i

postulate
  ≡-rel-inj-iso-0 : ∀ {ℓ} {A B C : Set ℓ}
    (a : A -> B)
    (b : B -> A) ->
    (left : a ∘ b ≡ idfun B) ->
    (right : b ∘ a ≡ idfun A) ->
    {f g : C -> A} ->
    -------------------------------
    ∀ p -> ≡-rel-a-monomorphism a b left right {f = f} {g = g} (extent-l a p) ≡ p

  ≡-rel-inj-iso-1 : ∀ {ℓ} {A B C : Set ℓ}
    (a : A -> B)
    (b : B -> A) ->
    (left : a ∘ b ≡ idfun B) ->
    (right : b ∘ a ≡ idfun A) ->
    {f g : C -> A} ->
    -------------------------------
    ∀ p -> extent-l a (≡-rel-a-monomorphism a b left right {f = f} {g = g} p) ≡ p

≡-rel-a-inj : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> ∀ {f g : C -> A} -> (a ∘ f ≡ a ∘ g) ≡ (f ≡ g)
≡-rel-a-inj a b left right = ua (isoToEquiv (iso (≡-rel-a-monomorphism a b left right) (extent-l a) (≡-rel-inj-iso-0 a b left right) (≡-rel-inj-iso-1 a b left right)))

≡-rel-b-inj : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> ∀ {f g : C -> B} -> (b ∘ f ≡ b ∘ g) ≡ (f ≡ g)
≡-rel-b-inj a b left right = ua (isoToEquiv (iso (≡-rel-a-monomorphism b a right left) (extent-l b) (≡-rel-inj-iso-0 b a right left) (≡-rel-inj-iso-1 b a right left)))



