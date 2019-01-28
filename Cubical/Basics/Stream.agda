{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Basics.Stream where

open import Cubical.Core.Prelude
open import Cubical.Basics.Nat
open import Cubical.Basics.Equiv


record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream


mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)


mapS-id : ∀ {A} {xs : Stream A} → mapS (λ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = head xs
tail (mapS-id {xs = xs} i) = mapS-id {xs = tail xs} i


Stream-η : ∀ {A} {xs : Stream A} → xs ≡ (head xs , tail xs)
head (Stream-η {A} {xs} i) = head xs
tail (Stream-η {A} {xs} i) = tail xs


elimS : ∀ {A} (P : Stream A → Set) (c : ∀ x xs → P (x , xs)) (xs : Stream A) → P xs
elimS P c xs = transp (λ i → P (Stream-η {xs = xs} (~ i))) i0
                      (c (head xs) (tail xs))


even : ∀ {A} → Stream A → Stream A
head (even a) = head a
tail (even a) = even (tail (tail a))


odd : ∀ {A} → Stream A → Stream A
head (odd a) = head (tail a)
tail (odd a) = odd (tail (tail a))


odd≡even∘tail : ∀ {A} → (a : Stream A) → odd a ≡ even (tail a)
head (odd≡even∘tail a i) = head (tail a)
tail (odd≡even∘tail a i) = odd≡even∘tail (tail (tail a)) i


merge : ∀ {A} → Stream A → Stream A → Stream A
head (merge a _) = head a
head (tail (merge _ b)) = head b
tail (tail (merge a b)) = merge (tail a) (tail b)


mergeEvenOdd≡id : ∀ {A} → (a : Stream A) → merge (even a) (odd a) ≡ a
head (mergeEvenOdd≡id a i) = head a
head (tail (mergeEvenOdd≡id a i)) = head (tail a)
tail (tail (mergeEvenOdd≡id a i)) = mergeEvenOdd≡id (tail (tail a)) i


module Equality≅Bisimulation where
  record _≈_ {A : Set} (x y : Stream A) : Set where
    coinductive
    field
      ≈head : head x ≡ head y
      ≈tail : tail x ≈ tail y

  open _≈_

  bisim : {A : Set} → {x y : Stream A} → x ≈ y → x ≡ y
  head (bisim x≈y i) = ≈head x≈y i
  tail (bisim x≈y i) = bisim (≈tail x≈y) i

  misib : {A : Set} → {x y : Stream A} → x ≡ y → x ≈ y
  ≈head (misib p) = λ i → head (p i)
  ≈tail (misib p) = misib (λ i → tail (p i))

  iso1 : {A : Set} → {x y : Stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head (iso1 p i j) = head (p j)
  tail (iso1 p i j) = iso1 (λ i → tail (p i)) i j

  iso2 : {A : Set} → {x y : Stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈head (iso2 p i) = ≈head p
  ≈tail (iso2 p i) = iso2 (≈tail p) i


  -- misib can be implemented by transport as well.
  refl≈ : {A : Set} {x : Stream A} → x ≈ x
  ≈head refl≈ = refl
  ≈tail refl≈ = refl≈

  cast : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → x ≈ y
  cast {A} {x} {y} p = transp (λ i → x ≈ p i) i0 refl≈

  misib-refl : ∀ {A : Set} {x : Stream A} → misib {x = x} refl ≡ refl≈
  ≈head (misib-refl i) = refl
  ≈tail (misib-refl i) = misib-refl i


  misibTransp : ∀ {A : Set} {x y : Stream A} (p : x ≡ y) → cast p ≡ misib p
  misibTransp {x = x} p = J (\ _ p → cast p ≡ misib p) (compPath (transpRefl refl≈) (sym misib-refl)) p



module Stream≅Nat→ {A : Set} where

  lookup : Stream A → ℕ → A
  lookup xs zero = head xs
  lookup xs (suc n) = lookup (tail xs) n

  tabulate : (ℕ → A) → Stream A
  head (tabulate f) = f zero
  tail (tabulate f) = tabulate (λ n → f (suc n))


  lookup∘tabulate : (λ (x : _ → _) → lookup (tabulate x)) ≡ (λ x → x)
  lookup∘tabulate i f zero = f zero
  lookup∘tabulate i f (suc n) = lookup∘tabulate i (λ n → f (suc n)) n


  tabulate∘lookup : (λ (x : Stream _) → tabulate (lookup x)) ≡ (λ x → x)
  head (tabulate∘lookup i xs) = head xs
  tail (tabulate∘lookup i xs) = tabulate∘lookup i (tail xs)

  Stream≡Nat→ : Stream A ≡ (ℕ → A)
  Stream≡Nat→ = isoToPath lookup tabulate
    (λ f i → lookup∘tabulate i f) (λ xs i → tabulate∘lookup i xs)
