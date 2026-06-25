module Cubical.Data.Fin.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

infixl 6 _+ₘ_ _-ₘ_ _·ₘ_
infix 7 -ₘ_

-- Addition, subtraction and multiplication
_+ₘ_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
fst (_+ₘ_ {n = n} x y) = ((fst x) + (fst y)) mod (suc n)
snd (_+ₘ_ {n = n} x y) = <→<ᵗ
                         {n = ((fst x) + (fst y)) mod (suc n)}
                         {m = suc n}
                         (mod< n ((fst x) + (fst y)))

-ₘ_ : {n : ℕ} → (x : Fin (suc n)) → Fin (suc n)
fst (-ₘ_ {n = n} x) = (suc n ∸ fst x) mod suc n
snd (-ₘ_ {n = n} x) = <→<ᵗ (mod< n (suc n ∸ fst x))

_-ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_-ₘ_ x y = x +ₘ (-ₘ y)

_·ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
fst (_·ₘ_ {n = n} x y) = (fst x · fst y) mod (suc n)
snd (_·ₘ_ {n = n} x y) = <→<ᵗ (mod< n (fst x · fst y))

-- Group laws
+ₘ-assoc : {n : ℕ} (x y z : Fin (suc n))
  → (x +ₘ y) +ₘ z ≡ (x +ₘ (y +ₘ z))
+ₘ-assoc {n = n} x y z =
  Σ≡Prop (λ w → isProp<ᵗ {n = w} {suc n})
       ((mod-rCancel (suc n) ((fst x + fst y) mod (suc n)) (fst z))
    ∙∙ sym (mod+mod≡mod (suc n) (fst x + fst y) (fst z))
    ∙∙ cong (_mod suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
    ∙∙ mod+mod≡mod (suc n) (fst x) (fst y + fst z)
    ∙∙ sym (mod-lCancel (suc n) (fst x) ((fst y + fst z) mod suc n)))

+ₘ-comm : {n : ℕ} (x y : Fin (suc n)) → (x +ₘ y) ≡ (y +ₘ x)
+ₘ-comm {n = n} x y =
  Σ≡Prop (λ z → isProp<ᵗ {n = z} {suc n})
    (cong (_mod suc n) (+-comm (fst x) (fst y)))

+ₘ-lUnit : {n : ℕ} (x : Fin (suc n)) → 0 +ₘ x ≡ x
+ₘ-lUnit {n = n} (x , p) =
  Σ≡Prop (λ z → isProp<ᵗ {n = z} {suc n})
    (<→mod≡id x (suc n) (<ᵗ→< p))

+ₘ-rUnit : {n : ℕ} (x : Fin (suc n)) → x +ₘ 0 ≡ x
+ₘ-rUnit x = +ₘ-comm x 0 ∙ (+ₘ-lUnit x)

+ₘ-rCancel : {n : ℕ} (x : Fin (suc n)) → x -ₘ x ≡ 0
+ₘ-rCancel {n = n} (k , p) =
  Σ≡Prop (λ z → isProp<ᵗ {n = z} {suc n}) (
  (k + (suc n ∸ k)  mod suc n) mod suc n ≡⟨ sym (mod-rCancel (suc n) k _) ⟩
  (k + (suc n ∸ k)) mod suc n            ≡⟨ cong (_mod suc n) (+-comm k _) ⟩
  ((suc n ∸ k) + k) mod suc n            ≡⟨ cong (_mod suc n) (≤-∸-+-cancel (<-weaken {k} {suc n} (<ᵗ→< p))) ⟩
  suc n mod suc n                        ≡⟨ zero-charac (suc n) ⟩
  0                                      ∎)

+ₘ-lCancel : {n : ℕ} (x : Fin (suc n)) → (-ₘ x) +ₘ x ≡ 0
+ₘ-lCancel {n = n} x = +ₘ-comm (-ₘ x) x ∙ +ₘ-rCancel x

-- TODO : Ring laws

private
  test₁ : Path (Fin 11) (5 +ₘ 10) 4
  test₁ = refl

  test₂ : Path (Fin 11) (-ₘ 7 +ₘ 5 +ₘ 10) 8
  test₂ = refl

  test₃ : Path (Fin 1024) (1022 ·ₘ 1023) 2
  test₃ = refl

  test₄ : Path (Fin 8192) (-ₘ 32 ·ₘ 64 +ₘ 256) 6400
  test₄ = refl
