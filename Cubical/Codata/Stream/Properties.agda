{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Stream.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Codata.Stream.Base

open Stream

mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)

even : ∀ {A} → Stream A → Stream A
head (even a) = head a
tail (even a) = even (tail (tail a))

odd : ∀ {A} → Stream A → Stream A
head (odd a) = head (tail a)
tail (odd a) = odd (tail (tail a))

merge : ∀ {A} → Stream A → Stream A → Stream A
head (merge a _) = head a
head (tail (merge _ b)) = head b
tail (tail (merge a b)) = merge (tail a) (tail b)

mapS-id : ∀ {A} {xs : Stream A} → mapS (λ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = head xs
tail (mapS-id {xs = xs} i) = mapS-id {xs = tail xs} i

Stream-η : ∀ {A} {xs : Stream A} → xs ≡ (head xs , tail xs)
head (Stream-η {A} {xs} i) = head xs
tail (Stream-η {A} {xs} i) = tail xs

elimS : ∀ {A} (P : Stream A → Type₀) (c : ∀ x xs → P (x , xs)) (xs : Stream A) → P xs
elimS P c xs = transp (λ i → P (Stream-η {xs = xs} (~ i))) i0
                      (c (head xs) (tail xs))

odd≡even∘tail : ∀ {A} → (a : Stream A) → odd a ≡ even (tail a)
head (odd≡even∘tail a i) = head (tail a)
tail (odd≡even∘tail a i) = odd≡even∘tail (tail (tail a)) i

mergeEvenOdd≡id : ∀ {A} → (a : Stream A) → merge (even a) (odd a) ≡ a
head (mergeEvenOdd≡id a i) = head a
head (tail (mergeEvenOdd≡id a i)) = head (tail a)
tail (tail (mergeEvenOdd≡id a i)) = mergeEvenOdd≡id (tail (tail a)) i

module Equality≅Bisimulation where

-- Bisimulation
  record _≈_ {A : Type₀} (x y : Stream A) : Type₀ where
    coinductive
    field
      ≈head : head x ≡ head y
      ≈tail : tail x ≈ tail y

  open _≈_

  bisim : {A : Type₀} → {x y : Stream A} → x ≈ y → x ≡ y
  head (bisim x≈y i) = ≈head x≈y i
  tail (bisim x≈y i) = bisim (≈tail x≈y) i

  misib : {A : Type₀} → {x y : Stream A} → x ≡ y → x ≈ y
  ≈head (misib p) = λ i → head (p i)
  ≈tail (misib p) = misib (λ i → tail (p i))

  iso1 : {A : Type₀} → {x y : Stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head (iso1 p i j) = head (p j)
  tail (iso1 p i j) = iso1 (λ i → tail (p i)) i j

  iso2 : {A : Type₀} → {x y : Stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈head (iso2 p i) = ≈head p
  ≈tail (iso2 p i) = iso2 (≈tail p) i

  path≃bisim : {A : Type₀} → {x y : Stream A} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

  path≡bisim : {A : Type₀} → {x y : Stream A} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

  -- misib can be implemented by transport as well.
  refl≈ : {A : Type₀} {x : Stream A} → x ≈ x
  ≈head refl≈ = refl
  ≈tail refl≈ = refl≈

  cast : ∀ {A : Type₀} {x y : Stream A} (p : x ≡ y) → x ≈ y
  cast {x = x} p = transport (λ i → x ≈ p i) refl≈

  misib-refl : ∀ {A : Type₀} {x : Stream A} → misib {x = x} refl ≡ refl≈
  ≈head (misib-refl i) = refl
  ≈tail (misib-refl i) = misib-refl i

  misibTransp : ∀ {A : Type₀} {x y : Stream A} (p : x ≡ y) → cast p ≡ misib p
  misibTransp p = J (λ _ p → cast p ≡ misib p) ((transportRefl refl≈) ∙ (sym misib-refl)) p

module Stream≅Nat→ {A : Type₀} where
  lookup : {A : Type₀} → Stream A → ℕ → A
  lookup xs zero = head xs
  lookup xs (suc n) = lookup (tail xs) n

  tabulate : {A : Type₀} → (ℕ → A) → Stream A
  head (tabulate f) = f zero
  tail (tabulate f) = tabulate (λ n → f (suc n))

  lookup∘tabulate : (λ (x : _ → A) → lookup (tabulate x)) ≡ (λ x → x)
  lookup∘tabulate i f zero = f zero
  lookup∘tabulate i f (suc n) = lookup∘tabulate i (λ n → f (suc n)) n

  tabulate∘lookup : (λ (x : Stream A) → tabulate (lookup x)) ≡ (λ x → x)
  head (tabulate∘lookup i xs) = head xs
  tail (tabulate∘lookup i xs) = tabulate∘lookup i (tail xs)

  Stream≡Nat→ : Stream A ≡ (ℕ → A)
  Stream≡Nat→ = isoToPath (iso lookup tabulate (λ f i → lookup∘tabulate i f) (λ xs i → tabulate∘lookup i xs))
