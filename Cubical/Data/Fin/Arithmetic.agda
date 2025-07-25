{-# OPTIONS --cubical #-}
module Cubical.Data.Fin.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

infixl 6 _+ₘ_ _-ₘ_ _·ₘ_
infix 7 -ₘ_

-- Addition, subtraction and multiplication
_+ₘ_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
fst (_+ₘ_ {n = n} x y) = ((fst x) + (fst y)) mod (suc n)
snd (_+ₘ_ {n = n} x y) = mod< _ ((fst x) + (fst y))

-ₘ_ : {n : ℕ} → (x : Fin (suc n)) → Fin (suc n)
fst (-ₘ_ {n = n} x) =
  (+induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x) (fst x)
snd (-ₘ_ {n = n} x) = lem (fst x)
  where
  ≡<-trans : {x y z : ℕ} → x < y → x ≡ z → z < y
  ≡<-trans (k , p) q = k , cong (λ x → k + suc x) (sym q) ∙ p

  lem : {n : ℕ} (x : ℕ)
     → (+induction n _ _ _) x < suc n
  lem {n = n} =
    +induction n _
      (λ x p → ≡<-trans (mod< n (suc n ∸ x))
                 (sym (+inductionBase n _ _ _ x p)))
       λ x p → ≡<-trans p
                 (sym (+inductionStep n _ _ _ x))

_-ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_-ₘ_ x y = x +ₘ (-ₘ y)

_·ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
fst (_·ₘ_ {n = n} x y) = (fst x · fst y) mod (suc n)
snd (_·ₘ_ {n = n} x y) = mod< n (fst x · fst y)

-- Group laws
+ₘ-assoc : {n : ℕ} (x y z : Fin (suc n))
  → (x +ₘ y) +ₘ z ≡ (x +ₘ (y +ₘ z))
+ₘ-assoc {n = n} x y z =
  Σ≡Prop (λ _ → isProp≤)
       ((mod-rCancel (suc n) ((fst x + fst y) mod (suc n)) (fst z))
    ∙∙ sym (mod+mod≡mod (suc n) (fst x + fst y) (fst z))
    ∙∙ cong (_mod suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
    ∙∙ mod+mod≡mod (suc n) (fst x) (fst y + fst z)
    ∙∙ sym (mod-lCancel (suc n) (fst x) ((fst y + fst z) mod suc n)))

+ₘ-comm : {n : ℕ} (x y : Fin (suc n)) → (x +ₘ y) ≡ (y +ₘ x)
+ₘ-comm {n = n} x y =
  Σ≡Prop (λ _ → isProp≤)
    (cong (_mod suc n) (+-comm (fst x) (fst y)))

+ₘ-lUnit : {n : ℕ} (x : Fin (suc n)) → 0 +ₘ x ≡ x
+ₘ-lUnit {n = n} (x , p) =
  Σ≡Prop (λ _ → isProp≤)
    (+inductionBase n _ _ _ x p)

+ₘ-rUnit : {n : ℕ} (x : Fin (suc n)) → x +ₘ 0 ≡ x
+ₘ-rUnit x = +ₘ-comm x 0 ∙ (+ₘ-lUnit x)

+ₘ-rCancel : {n : ℕ} (x : Fin (suc n)) → x -ₘ x ≡ 0
+ₘ-rCancel {n = n} x =
  Σ≡Prop (λ _ → isProp≤)
      (cong (λ z → (fst x + z) mod (suc n))
            (+inductionBase n _ _ _ (fst x) (snd x))
    ∙∙ sym (mod-rCancel (suc n) (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (+-comm (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (≤-∸-+-cancel (<-weaken (snd x)))
    ∙∙ zero-charac (suc n))

+ₘ-lCancel : {n : ℕ} (x : Fin (suc n)) → (-ₘ x) +ₘ x ≡ 0
+ₘ-lCancel {n = n} x = +ₘ-comm (-ₘ x) x ∙ +ₘ-rCancel x

-- TODO : Ring laws

private
  test₁ : Path (Fin 11) (5 +ₘ 10) 4
  test₁ = refl

  test₂ : Path (Fin 11) (-ₘ 7 +ₘ 5 +ₘ 10) 8
  test₂ = refl
