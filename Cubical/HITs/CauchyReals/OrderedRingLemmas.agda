{-# OPTIONS --cubical #-}

module Cubical.HITs.CauchyReals.OrderedRingLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma using (Σ; _,_)

open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sum

module OrderedRingLemmas
  {ℓ ℓ₀}
  (R     : Type ℓ)
  (_+_   : R → R → R)
  (_·_   : R → R → R)
  (-_    : R → R)
  (0r 1r : R)
  (_≤_ _<_ _＃_ : R → R → Type ℓ₀)
  (min max : R → R → R)
  where


 infix  4 _≤_ _<_
 infixl 6 _+_
 infixl 7 _·_

 -- Subtraction as addition with negation
 _−_ : R → R → R
 x − y = x + (- y)
 private 
  variable
    x y z x' y' ε : R

  ------------------------------------------------------------------------
  -- 1. Order core (preorder/partial/linear)
  ------------------------------------------------------------------------

  ≤-refl     : (x ≤ x)
  ≤-refl = {!!}

  ≤-antisym  : (x ≤ y) → (y ≤ x) → (x ≡ y)
  ≤-antisym = {!!}

  ≤-trans    : (x ≤ y) → (y ≤ z) → (x ≤ z)
  ≤-trans = {!!}

  <-trans    : (x < y) → (y < z) → (x < z)
  <-trans = {!!}

  <-irrefl   : ¬ (x < x)
  <-irrefl = {!!}

  <-asym     : (x < y) → ¬ (y < x)
  <-asym = {!!}

  <-resp-≡ˡ  : (x ≡ y) → (y < z) → (x < z)
  <-resp-≡ˡ = {!!}

  <-resp-≡ʳ  : (x < y) → (y ≡ z) → (x < z)
  <-resp-≡ʳ = {!!}

  cmp-≤      : (x ≤ y) ⊎ (y ≤ x)
  cmp-≤ = {!!}

  ≤-total    : (x ≤ y) ⊎ (y ≤ x)
  ≤-total = {!!}

  ------------------------------------------------------------------------
  -- 2. Order ↔ equality bridges
  ------------------------------------------------------------------------

  <-to-≤     : (x < y) → (x ≤ y)
  <-to-≤ = {!!}

  ≤-not->    : (x ≤ y) → ¬ (y < x)
  ≤-not-> = {!!}

  ≮-refl     : ¬ (x < x)
  ≮-refl = {!!}

  ≤-≡-≤      : (x ≤ y) → (y ≤ x) → (x ≡ y)
  ≤-≡-≤ = {!!}

  <-cmp-≡    : (x < y) → (x ≡ y) → ⊥
  <-cmp-≡ = {!!}

  ------------------------------------------------------------------------
  -- 3. Interaction with addition
  ------------------------------------------------------------------------

  -- 3.1 Monotonicity and cancellation
  +-monoˡ-≤  : (x ≤ y) → ((z + x) ≤ (z + y))
  +-monoˡ-≤ = {!!}

  +-monoʳ-≤  : (x ≤ y) → ((x + z) ≤ (y + z))
  +-monoʳ-≤ = {!!}

  +-monoˡ-<  : (x < y) → ((z + x) < (z + y))
  +-monoˡ-< = {!!}

  +-monoʳ-<  : (x < y) → ((x + z) < (y + z))
  +-monoʳ-< = {!!}

  +-cancelˡ-≤ : ((z + x) ≤ (z + y)) → (x ≤ y)
  +-cancelˡ-≤ = {!!}

  +-cancelʳ-≤ : ((x + z) ≤ (y + z)) → (x ≤ y)
  +-cancelʳ-≤ = {!!}

  +-cancelˡ-< : ((z + x) <  (z + y)) → (x <  y)
  +-cancelˡ-< = {!!}

  +-cancelʳ-< : ((x + z) <  (y + z)) → (x <  y)
  +-cancelʳ-< = {!!}

  -- 3.2 Zero, negation, subtraction
  0≤1     : (0r ≤ 1r)
  0≤1 = {!!}

  0<1     : (0r < 1r)
  0<1 = {!!}

  neg-mono-≤ : (x ≤ y) → ((- y) ≤ (- x))
  neg-mono-≤ = {!!}

  neg-mono-< : (x < y) → ((- y) < (- x))
  neg-mono-< = {!!}

  ≤-iff-0≤diff : ((x ≤ y) ≃ (0r ≤ (y − x)))
  ≤-iff-0≤diff = {!!}

  <-iff-0<diff : ((x < y) ≃ (0r < (y − x)))
  <-iff-0<diff = {!!}

  diff-monoʳ-≤ : (x ≤ y) → ((x − z) ≤ (y − z))
  diff-monoʳ-≤ = {!!}

  diff-monoˡ-≤ : (x ≤ y) → ((z − y) ≤ (z − x))
  diff-monoˡ-≤ = {!!}

  ------------------------------------------------------------------------
  -- 4. Interaction with multiplication
  ------------------------------------------------------------------------

  -- 4.1 Nonnegativity/positivity closure
  ·-preserves-nonneg : (0r ≤ x) → (0r ≤ y) → (0r ≤ (x · y))
  ·-preserves-nonneg = {!!}

  ·-preserves-pos    : (0r < x) → (0r < y) → (0r < (x · y))
  ·-preserves-pos = {!!}

  square-nonneg : (0r ≤ (x · x))
  square-nonneg = {!!}

  square-pos    : (x ＃ 0r) → (0r < (x · x))
  square-pos = {!!}

  -- 4.2 Monotonicity (restricted)
  ·-monoʳ-≤-nonneg : (x ≤ y) → (0r ≤ z) → ((x · z) ≤ (y · z))
  ·-monoʳ-≤-nonneg = {!!}

  ·-monoˡ-≤-nonneg : (x ≤ y) → (0r ≤ z) → ((z · x) ≤ (z · y))
  ·-monoˡ-≤-nonneg = {!!}

  ·-monoʳ-<-pos    : (x < y) → (0r < z) → ((x · z) < (y · z))
  ·-monoʳ-<-pos = {!!}

  ·-monoˡ-<-pos    : (x < y) → (0r < z) → ((z · x) < (z · y))
  ·-monoˡ-<-pos = {!!}

  -- 4.3 Sign rules for products
  ·-pos-pos→pos  : (0r < x) → (0r < y) → (0r < (x · y))
  ·-pos-pos→pos = {!!}

  ·-pos-neg→neg  : (0r < x) → (y < 0r) → ((x · y) < 0r)
  ·-pos-neg→neg = {!!}

  ·-neg-pos→neg  : (x < 0r) → (0r < y) → ((x · y) < 0r)
  ·-neg-pos→neg = {!!}

  ·-neg-neg→pos  : (x < 0r) → (y < 0r) → (0r < (x · y))
  ·-neg-neg→pos = {!!}

  ·-nonneg-nonpos→nonpos : (0r ≤ x) → (y ≤ 0r) → ((x · y) ≤ 0r)
  ·-nonneg-nonpos→nonpos = {!!}

  ·-nonpos-nonneg→nonpos : (x ≤ 0r) → (0r ≤ y) → ((x · y) ≤ 0r)
  ·-nonpos-nonneg→nonpos = {!!}

  -- 4.4 Cancellation with positive factors
  ·-cancelʳ-≤-pos : (0r < z) → ((x · z) ≤ (y · z)) → (x ≤ y)
  ·-cancelʳ-≤-pos = {!!}

  ·-cancelˡ-≤-pos : (0r < z) → ((z · x) ≤ (z · y)) → (x ≤ y)
  ·-cancelˡ-≤-pos = {!!}

  ·-cancelʳ-<-pos : (0r < z) → ((x · z) <  (y · z)) → (x <  y)
  ·-cancelʳ-<-pos = {!!}

  ·-cancelˡ-<-pos : (0r < z) → ((z · x) <  (z · y)) → (x <  y)
  ·-cancelˡ-<-pos = {!!}

  -- 4.5 Bounds and unit-ish facts (no inverses assumed)
  one-nonneg        : (0r ≤ 1r)
  one-nonneg = {!!}

  ≤-one→≤-mul-when-≤1ˡ : (0r ≤ x) → (x ≤ 1r) → (0r ≤ y) → (y ≤ 1r) → ((x · y) ≤ y)
  ≤-one→≤-mul-when-≤1ˡ = {!!}

  ≤-one→≤-mul-when-≤1ʳ : (0r ≤ x) → (x ≤ 1r) → (0r ≤ y) → (y ≤ 1r) → ((x · y) ≤ x)
  ≤-one→≤-mul-when-≤1ʳ = {!!}

  pos→≤-mul-posˡ : (1r ≤ x) → (0r ≤ y) → (y ≤ (x · y))
  pos→≤-mul-posˡ = {!!}

  pos→≤-mul-posʳ : (1r ≤ y) → (0r ≤ x) → (x ≤ (x · y))
  pos→≤-mul-posʳ = {!!}

  ------------------------------------------------------------------------
  -- 5. Negation & subtraction (sign algebra)
  ------------------------------------------------------------------------

  neg-neg≤ : (x ≤ (- x)) → (x ≤ 0r)
  neg-neg≤ = {!!}

  ≤-neg-neg : ((- x) ≤ x) → (0r ≤ x)
  ≤-neg-neg = {!!}

  neg0≡0  : ((- 0r) ≡ 0r)
  neg0≡0 = {!!}

  neg1≡-1 : ((- 1r) ≡ (- 1r))
  neg1≡-1 = {!!}

  neg-≤-iff : (((- x) ≤ (- y)) ≃ (y ≤ x))
  neg-≤-iff = {!!}

  neg-<-iff : (((- x) < (- y)) ≃ (y < x))
  neg-<-iff = {!!}

  sub-zeroʳ : ((x − 0r) ≡ x)
  sub-zeroʳ = {!!}

  sub-zeroˡ : ((0r − x) ≡ (- x))
  sub-zeroˡ = {!!}

  ≤-sub0    : ((x ≤ 0r) ≃ (0r ≤ (- x)))
  ≤-sub0 = {!!}

  0≤-sub    : ((0r ≤ x) ≃ ((- x) ≤ 0r))
  0≤-sub = {!!}

  ------------------------------------------------------------------------
  -- 6. Mixed order/alg identities (transport & congruence)
  ------------------------------------------------------------------------

  cong-≤-+ : (x ≡ x') → (y ≡ y') → (x ≤ y) → (x' ≤ y')
  cong-≤-+ = {!!}

  cong-<-+ : (x ≡ x') → (y ≡ y') → (x <  y) → (x' <  y')
  cong-<-+ = {!!}

  cong-≤-· : (x ≡ x') → (y ≡ y') → (x ≤ y) → (x' ≤ y')
  cong-≤-· = {!!}

  cong-<-· : (x ≡ x') → (y ≡ y') → (x <  y) → (x' <  y')
  cong-<-· = {!!}

  transport-≤  : (x ≡ y) → (x ≤ y)
  transport-≤ = {!!}

  transport-≥  : (x ≡ y) → (y ≤ x)
  transport-≥ = {!!}

  ------------------------------------------------------------------------
  -- 7. Min/Max (if provided)
  ------------------------------------------------------------------------

  max-ubˡ    : (x ≤ (max x y))
  max-ubˡ = {!!}

  max-ubʳ    : (y ≤ (max x y))
  max-ubʳ = {!!}

  max-le     : (x ≤ z) → (y ≤ z) → ((max x y) ≤ z)
  max-le = {!!}

  min-lbˡ    : ((min x y) ≤ x)
  min-lbˡ = {!!}

  min-lbʳ    : ((min x y) ≤ y)
  min-lbʳ = {!!}

  le-min     : (z ≤ x) → (z ≤ y) → (z ≤ (min x y))
  le-min = {!!}

  +-mono-≤-max : (x ≤ y) → ((x + z) ≤ (max (y + z) (z + y)))
  +-mono-≤-max = {!!}

  ·-mono-≤-max-nonneg : (0r ≤ z) → (x ≤ y) → ((x · z) ≤ (max (y · z) (z · y)))
  ·-mono-≤-max-nonneg = {!!}

  ------------------------------------------------------------------------
  -- 8. Distributivity and order (derived)
  ------------------------------------------------------------------------

  distrib-≤-left  : (0r ≤ x) → ((x · (y + z)) ≤ ((x · y) + (x · z)))
  distrib-≤-left = {!!}

  distrib-≤-right : (0r ≤ x) → (((y + z) · x) ≤ ((y · x) + (z · x)))
  distrib-≤-right = {!!}

  ·-sub-distrˡ-≤-nonneg : (0r ≤ x) → ((x · (y − z)) ≤ ((x · y) − (x · z)))
  ·-sub-distrˡ-≤-nonneg = {!!}

  ·-sub-distrʳ-≤-nonneg : (0r ≤ x) → (((y − z) · x) ≤ ((y · x) − (z · x)))
  ·-sub-distrʳ-≤-nonneg = {!!}

  ------------------------------------------------------------------------
  -- 9. Strict strengthening/weakening utilities
  ------------------------------------------------------------------------

  <→≤-succedent : (x < y) → (x ≤ y)
  <→≤-succedent = {!!}

  ≤∧＃→<        : (x ≤ y) → (x ＃ y) → (x < y)
  ≤∧＃→< = {!!}

  <→≤-+ε       : (0r < ε) → (x < y) → ((x + ε) ≤ y)
  <→≤-+ε = {!!}

  ------------------------------------------------------------------------
  -- 10. Monotone/antitone maps (templates)
  ------------------------------------------------------------------------

  Monotoneᵣ : (f : R → R) → Type (ℓ-max ℓ ℓ₀)
  Monotoneᵣ f = ∀ {x y} → (x ≤ y) → ((f x) ≤ (f y))

  Antitoneᵣ : (f : R → R) → Type (ℓ-max ℓ ℓ₀)
  Antitoneᵣ f = ∀ {x y} → (x ≤ y) → ((f y) ≤ (f x))

  +-mono-functionˡ : (z : R) → Monotoneᵣ (λ x → (z + x))
  +-mono-functionˡ = {!!}

  +-mono-functionʳ : (z : R) → Monotoneᵣ (λ x → (x + z))
  +-mono-functionʳ = {!!}

  ·-mono-functionˡ-nonneg : {z : R} → (0r ≤ z) → Monotoneᵣ (λ x → (z · x))
  ·-mono-functionˡ-nonneg = {!!}

  ·-mono-functionʳ-nonneg : {z : R} → (0r ≤ z) → Monotoneᵣ (λ x → (x · z))
  ·-mono-functionʳ-nonneg = {!!}

  neg-antitone : Antitoneᵣ (λ x → (- x))
  neg-antitone = {!!}

  ------------------------------------------------------------------------
  -- 11. Comparisons to zero/one (grab-bag)
  ------------------------------------------------------------------------

  ≤-0-iff-neg≥0 : ((x ≤ 0r) ≃ (0r ≤ (- x)))
  ≤-0-iff-neg≥0 = {!!}

  0-≤-iff-neg≤0 : ((0r ≤ x) ≃ (((- x) ≤ 0r)))
  0-≤-iff-neg≤0 = {!!}

  1≤-mul-cancelˡ-pos : (0r < y) → (1r ≤ x) → (y ≤ (y · x))
  1≤-mul-cancelˡ-pos = {!!}

  1≤-mul-cancelʳ-pos : (0r < x) → (1r ≤ y) → (x ≤ (x · y))
  1≤-mul-cancelʳ-pos = {!!}

  mul≤-one-when-≤1 : (0r ≤ x) → (x ≤ 1r) → (0r ≤ y) → (y ≤ 1r) → ((x · y) ≤ 1r)
  mul≤-one-when-≤1 = {!!}

  one≤-mul-when-≥1 : (1r ≤ x) → (1r ≤ y) → (1r ≤ (x · y))
  one≤-mul-when-≥1 = {!!}

  ------------------------------------------------------------------------
  -- 12. Convenient equivalences (shift/cancel)
  ------------------------------------------------------------------------

  ≤-shiftˡ-+ : (((x + z) ≤ (y + z)) ≃ (x ≤ y))
  ≤-shiftˡ-+ = {!!}

  ≤-shiftʳ-+ : (((z + x) ≤ (z + y)) ≃ (x ≤ y))
  ≤-shiftʳ-+ = {!!}

  <-shiftˡ-+ : (((x + z) <  (y + z)) ≃ (x <  y))
  <-shiftˡ-+ = {!!}

  <-shiftʳ-+ : (((z + x) <  (z + y)) ≃ (x <  y))
  <-shiftʳ-+ = {!!}

  ≤-shiftˡ-·-pos : (0r < z) → (((x · z) ≤ (y · z)) ≃ (x ≤ y))
  ≤-shiftˡ-·-pos = {!!}

  ≤-shiftʳ-·-pos : (0r < z) → (((z · x) ≤ (z · y)) ≃ (x ≤ y))
  ≤-shiftʳ-·-pos = {!!}

  <-shiftˡ-·-pos : (0r < z) → (((x · z) <  (y · z)) ≃ (x <  y))
  <-shiftˡ-·-pos = {!!}

  <-shiftʳ-·-pos : (0r < z) → (((z · x) <  (z · y)) ≃ (x <  y))
  <-shiftʳ-·-pos = {!!}

  ≤-0-iff-≤-neg : ((x ≤ 0r) ≃ ((x + x) ≤ (0r + x)))
  ≤-0-iff-≤-neg = {!!}
