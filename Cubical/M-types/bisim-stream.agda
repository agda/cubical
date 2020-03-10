{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.M-types.itree
open import Cubical.M-types.M
open import Cubical.M-types.Coalg
open import Cubical.M-types.stream

open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Codata.Stream
open import Cubical.Data.Prod

module Cubical.M-types.bisim-stream where

----------------------------------------
-- The stream bisimulation Properties --
----------------------------------------

-- Bisimulation principle for streams
record stream≈ {A} (x y : stream A) : Set where
  coinductive
  field
    hd≈ : hd x ≡ hd y
    tl≈ : stream≈ (tl x) (tl y)

open stream≈

stream≈-refl : ∀ {A} {x} -> stream≈ {A} x x
hd≈ (stream≈-refl) = refl
tl≈ (stream≈-refl {x = x}) = stream≈-refl {x = tl x}

stream≈-sym : ∀ {A} {x y} -> stream≈ {A} x y -> stream≈ {A} y x
hd≈ (stream≈-sym s) = sym (hd≈ s)
tl≈ (stream≈-sym s) = stream≈-sym (tl≈ s)

stream≈-trans : ∀ {A} {x y z} -> stream≈ {A} x y -> stream≈ {A} y z -> stream≈ {A} x z
hd≈ (stream≈-trans s t) = λ i -> compPath-filler (hd≈ s) (hd≈ t) i i
tl≈ (stream≈-trans s t) = stream≈-trans (tl≈ s) (tl≈ t)

----------------------------
-- Bisimulation Principle --
----------------------------

postulate
  stream≈-helper : ∀ {A} -> (x : Σ (stream A) (λ a → Σ (stream A) (stream≈ a))) -> (fst (x .snd)) ≡ (fst x)

stream-bisimulation : ∀ {A} -> bisimulation (stream-S A) M-coalg (stream≈)
stream-bisimulation {A} = bisimulation-property (stream-S A) stream≈ stream≈-refl stream≈-helper

stream-bisim : ∀ {A} -> ∀ {x y : stream A} -> stream≈ x y -> x ≡ y
stream-bisim {A} {x} {y} = coinduction stream≈ stream-bisimulation

stream-misib : ∀ {A} {x y} -> x ≡ y -> stream≈ {A} x y
stream-misib = coinduction⁻ stream≈ stream-bisimulation stream≈-refl

postulate
  iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → stream-bisim {A = A} (stream-misib {A = A} p) ≡ p
  iso2 : {A : Type₀} → {x y : stream A} → (p : stream≈ x y) → stream-misib (stream-bisim p) ≡ p

stream≈≡≡ : ∀ {A} -> stream≈ {A} ≡ _≡_
stream≈≡≡ = coinduction-is-equality stream≈ stream-bisimulation stream≈-refl
