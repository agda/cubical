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

stream≈-equality-relation : ∀ {A} -> equality-relation (stream≈ {A})
stream≈-equality-relation = record { eq-refl = stream≈-refl ; eq-sym = stream≈-sym ; eq-trans = stream≈-trans }

postulate
  stream≈-anti-helper : ∀ {A} {x y : stream A} -> hd x ≡ hd y -> tl x ≡ tl y -> x ≡ y

stream≈-anti : ∀ {A} {x y} -> stream≈ {A} x y -> stream≈ {A} y x -> x ≡ y
stream≈-anti {x = x} {y = y} p q = {!!}

stream≈-helper : ∀ {A} -> (x : Σ (stream A) (λ a → Σ (stream A) (stream≈ a))) -> (fst x) ≡ (fst (x .snd))
stream≈-helper {A} = equality-relation-projection stream≈-equality-relation

----------------------------
-- Bisimulation Principle --
----------------------------

stream-bisimulation : ∀ {A} -> bisimulation (stream-S A) M-coalg (stream≈)
αᵣ (stream-bisimulation) = λ a → fst (out-fun (a .fst)) , (λ b → snd (out-fun (a .fst)) b , (snd (out-fun (a .fst)) b , stream≈-refl))
rel₁ (stream-bisimulation) = funExt λ x → refl
rel₂ (stream-bisimulation) = funExt λ x → λ i → out-fun (stream≈-helper x (~ i))

stream-bisim : ∀ {A} -> ∀ {x y : stream A} -> stream≈ x y -> x ≡ y
stream-bisim {A} {x} {y} = coinduction stream≈ stream-bisimulation
  
stream-misib : ∀ {A} {x y} -> x ≡ y -> stream≈ {A} x y
stream-misib = coinduction⁻ stream≈ stream-bisimulation stream≈-refl

eta-helper : ∀ {A} (x : stream A) -> ( out-fun x .fst , λ { tt -> out-fun x .snd tt } ) ≡ out-fun x
eta-helper = λ x i → out-fun x .fst , λ tt → out-fun x .snd tt

eta-helper-2 : ∀ {A} (x : stream A) -> in-fun ( out-fun x .fst , λ { tt -> out-fun x .snd tt } ) ≡ cons {A = A} (hd x) (tl x)
eta-helper-2 = λ x -> refl

eta-helper-3 : ∀ {A} (x : stream A) -> in-fun (out-fun x) ≡ cons {A = A} (hd x) (tl x)
eta-helper-3 = λ x -> refl

eta : ∀ {A} x -> x ≡ cons {A = A} (hd x) (tl x)
eta {A} = λ x -> λ i ->
  compPath-filler
    {x = x}
    {y = in-fun (out-fun x)}
    {z = cons {A = A} (hd x) (tl x)}
      (sym (funExt⁻ in-inverse-out x))
      (eta-helper-3 x)
      i i

bisim-helper : ∀ {A} {x y : stream A} -> cons {A = A} (hd x) (tl x) ≡ cons {A = A} (hd y) (tl y) -> x ≡ y
bisim-helper {A} {xa} {ya} = λ p i →
  compPath-filler
    (λ j ->
      compPath-filler
        (eta xa)
        p
        j j)
    (sym (eta ya))
    i i

bisim-helper-2 : ∀ {A} {x y : stream A} -> hd x ≡ hd y -> tl x ≡ tl y -> cons {A = A} (hd x) (tl x) ≡ cons {A = A} (hd y) (tl y)
bisim-helper-2 {A} = λ p q i → cons (p i) (q i)

bisim-helper-3 : ∀ {A} {x y : stream A} -> hd x ≡ hd y -> tl x ≡ tl y -> x ≡ y
bisim-helper-3 {A} x y = (bisim-helper (bisim-helper-2 x y))

iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → stream-bisim {A = A} (stream-misib {A = A} p) ≡ p -- equiv cons (hd (p i)) (tl (p i))
iso1 p i j = bisim-helper-3 {x = stream-bisim (stream-misib p) j} {y = p j} (λ i₁ → hd {!!}) (λ i₁ → tl {!!}) {!!}

iso2 : {A : Type₀} → {x y : stream A} → (p : stream≈ x y) → stream-misib (stream-bisim p) ≡ p -- equiv cons (hd (p i)) (tl (p i))
hd≈ (iso2 p i) = λ j → transp (λ k → {!!}) j (hd≈ p i) -- hd≈ p
tl≈ (iso2 p i) = {!!} -- iso2 (tl≈ p) i

stream≈≡≡ : ∀ {A} -> stream≈ {A} ≡ _≡_
stream≈≡≡ = coinduction-is-equality stream≈ stream-bisimulation stream≈-refl
