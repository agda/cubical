{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Fin.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

infixl 6 _+ₘ_ _-ₘ_ _·ₘ_
infix 7 -ₘ_

-- Defining x mod 0 to be 0. This way all the theorems below are true
-- for n : ℕ instead of n : ℕ₊₁. I guess this is pretty useless in practice.
_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
x mod (suc n) = (+induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x) x

mod< : (n x : ℕ) → x mod (suc n) < (suc n)
mod< n =
  +induction n (λ x → x mod (suc n) < suc n)
               (λ x base → fst base
                         , (cong (λ x → fst base + suc x)
                                 (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base)
                          ∙ snd base))
               λ x ind → fst ind
                        , cong (λ x → fst ind + suc x)
                               (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x) ∙ snd ind

mod-rUnit : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
mod-rUnit zero x = refl
mod-rUnit (suc n) x =
    sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
  ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (+-comm (suc n) x)

mod-lUnit : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
mod-lUnit zero _ = refl
mod-lUnit (suc n) x = sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)

mod+mod≡mod : (n x y : ℕ) → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod+mod≡mod zero _ _ = refl
mod+mod≡mod (suc n) =
  +induction n
    (λ z → (x : ℕ) → ((z + x) mod (suc n)) ≡ (((z mod (suc n)) + (x mod (suc n))) mod (suc n)))
    (λ x p → +induction n _
                (λ y q → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                               (sym (cong₂  _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x p)
                               (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) y q))))
                λ y ind → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                (cong (x +_) (+-comm (suc n) y) ∙ (+-assoc x y (suc n)))
                             ∙∙ sym (mod-rUnit (suc n) (x + y))
                             ∙∙ ind
                              ∙ cong (λ z → +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)
                                            ((+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x + z)))
                                     (mod-rUnit (suc n) y ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                                            (+-comm y (suc n))))
    λ x p y → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                (cong suc (sym (+-assoc n x y)))
                 ∙∙ sym (mod-lUnit (suc n) (x + y))
                 ∙∙ p y
                  ∙ sym (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                        (cong (_+ +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y)
                        (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                        (+-comm (suc n) x) ∙ sym (mod-rUnit (suc n) x))))

mod-idempotent : {n : ℕ} → (x : ℕ) → (x mod n) mod n ≡ x mod n
mod-idempotent {n = zero} _ = refl
mod-idempotent {n = suc n} =
  +induction n (λ x → (x mod suc n) mod (suc n) ≡ x mod (suc n))
             (λ x p → cong (_mod (suc n))
                            (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x p))
              λ x p → cong (_mod (suc n))
                            (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                             ∙∙ p
                             ∙∙ mod-rUnit (suc n) x
                              ∙ (cong (_mod (suc n)) (+-comm x (suc n)))

mod-rCancel : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
mod-rCancel zero x y = refl
mod-rCancel (suc n) x =
  +induction n _
    (λ y p → cong (λ z → (x + z) mod (suc n))
                   (sym (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y p)))
     λ y p → cong (_mod suc n) (+-assoc x (suc n) y
                             ∙∙ (cong (_+ y) (+-comm x (suc n)))
                             ∙∙ sym (+-assoc (suc n) x y))
          ∙∙ sym (mod-lUnit (suc n) (x + y))
          ∙∙ (p ∙ cong (λ z → (x + z) mod suc n) (mod-lUnit (suc n) y))

mod-lCancel : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
mod-lCancel n x y =
     cong (_mod n) (+-comm x y)
  ∙∙ mod-rCancel n y x
  ∙∙ cong (_mod n) (+-comm y (x mod n))

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero = refl
zero-charac (suc n) = cong (_mod suc n) (+-comm 0 (suc n))
                  ∙∙ +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0
                  ∙∙ +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0 (n , (+-comm n 1))

-- Addition, subtraction and multiplication
_+ₘ_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
_+ₘ_ {n = n} x y = (((fst x) + (fst y)) mod (suc n)) , mod< _ ((fst x) + (fst y))

-ₘ_ : {n : ℕ} → (x : Fin (suc n)) → Fin (suc n)
fst (-ₘ_ {n = n} x) = (+induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x) (fst x)
snd (-ₘ_ {n = n} x) = lem (fst x)
  where
  ≡<-trans : {x y z : ℕ} → x < y → x ≡ z → z < y
  ≡<-trans (k , p) q = k , cong (λ x → k + suc x) (sym q) ∙ p

  lem : {n : ℕ} (x : ℕ)
     → (+induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x) x < suc n
  lem {n = n} =
    +induction n _
      (λ x p → ≡<-trans (mod< n (suc n ∸ x))
                         (sym (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x p)))
       λ x p → ≡<-trans p (sym (+inductionStep n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x))

_-ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_-ₘ_ x y = x +ₘ (-ₘ y)

_·ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_·ₘ_ {n = n} x y = (fst x · fst y) mod (suc n) , mod< n (fst x · fst y)

-- Group laws
+ₘ-assoc : {n : ℕ} (x y z : Fin (suc n)) → (x +ₘ y) +ₘ z ≡ (x +ₘ (y +ₘ z))
+ₘ-assoc {n = n} x y z =
  Σ≡Prop (λ _ → m≤n-isProp)
       ((mod-rCancel (suc n) ((fst x + fst y) mod (suc n)) (fst z))
    ∙∙ sym (mod+mod≡mod (suc n) (fst x + fst y) (fst z))
    ∙∙ cong (_mod suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
    ∙∙ mod+mod≡mod (suc n) (fst x) (fst y + fst z)
    ∙∙ sym (mod-lCancel (suc n) (fst x) ((fst y + fst z) mod suc n)))

+ₘ-comm : {n : ℕ} (x y : Fin (suc n)) → (x +ₘ y) ≡ (y +ₘ x)
+ₘ-comm {n = n} x y = Σ≡Prop (λ _ → m≤n-isProp) (cong (_mod suc n) (+-comm (fst x) (fst y)))

+ₘ-lUnit : {n : ℕ} (x : Fin (suc n)) → 0 +ₘ x ≡ x
+ₘ-lUnit {n = n} (x , p) = Σ≡Prop (λ _ → m≤n-isProp) (+inductionBase n _ _ _ x p)

+ₘ-rUnit : {n : ℕ} (x : Fin (suc n)) → x +ₘ 0 ≡ x
+ₘ-rUnit x = +ₘ-comm x 0 ∙ (+ₘ-lUnit x)

+ₘ-rCancel : {n : ℕ} (x : Fin (suc n)) → x -ₘ x ≡ 0
+ₘ-rCancel {n = n} x =
  Σ≡Prop (λ _ → m≤n-isProp)
      (cong (λ z → (fst x + z) mod (suc n))
            (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) (fst x) (snd x))
    ∙∙ sym (mod-rCancel (suc n) (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (+-comm (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (≤-∸-+-cancel (<-weaken (snd x)))
    ∙∙ zero-charac (suc n))

+ₘ-lCancel : {n : ℕ} (x : Fin (suc n)) → (-ₘ x) +ₘ x ≡ 0
+ₘ-lCancel {n = n} x = +ₘ-comm (-ₘ x) x ∙ +ₘ-rCancel x


-- remainder and quotient after division by n
-- Again, allowing for 0-division to get nicer syntax
remainder_/_ : (x n : ℕ) → ℕ
remainder x / zero = x
remainder x / suc n = x mod (suc n)

quotient_/_ : (x n : ℕ) → ℕ
quotient x / zero = 0
quotient x / suc n = +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

rem+quot-mod≡ : (n x : ℕ) → (remainder x / n) + n · (quotient x / n) ≡ x
rem+quot-mod≡ zero x = +-comm x 0
rem+quot-mod≡ (suc n) =
  +induction n
    (λ x → (remainder x / (suc n)) + (suc n) · (quotient x / (suc n)) ≡ x)
    (λ x base → cong₂ _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base)
                           (cong ((suc n) ·_) (+inductionBase n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x base))
              ∙∙ cong (x +_) (·-comm n 0)
              ∙∙ +-comm x 0)
     λ x ind → cong₂ _+_ (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x)
                        (cong ((suc n) ·_) (+inductionStep n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
          ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                  (·-suc (suc n) (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
          ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                  (+-comm (suc n) ((suc n) · (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)))
          ∙∙ +-assoc (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                     ((suc n) · +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)
                     (suc n)
          ∙∙ cong (_+ suc n) ind
           ∙ +-comm x (suc n)


private
  test₀ : 100 mod 81 ≡ 19
  test₀ = refl

  test₁ : ((11 + (10 mod 3)) mod 3) ≡ 0
  test₁ = refl

  test₂ : Path (Fin 11) (5 +ₘ 10) 4
  test₂ = refl

  test₃ : Path (Fin 11) (-ₘ 7 +ₘ 5 +ₘ 10) 8
  test₃ = refl
