
module Cubical.HITs.Delooping.Two.Base where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

-- Explicit construction of the delooping of the two-element group
data Bℤ₂ : Type₀ where
  base : Bℤ₂
  loop : base ≡ base
  loop² : Square loop refl refl loop
  trunc : isGroupoid Bℤ₂

private
  variable
    ℓ : Level
    A : Type ℓ

module Elim where
  rec : (x : A)
      → (p : x ≡ x)
      → (sq : Square p refl refl p)
      → isGroupoid A
      → Bℤ₂ → A
  rec x p sq Agpd = go
    where
    go : _ → _
    go base = x
    go (loop i) = p i
    go (loop² i j) = sq i j
    go (trunc x y p q r s i j k)
      = Agpd
          (go x) (go y)
          (cong go p) (cong go q)
          (cong (cong go) r) (cong (cong go) s)
          i j k

  elim : (P : Bℤ₂ → Type ℓ)
       → (x : P base)
       → (p : PathP (λ i → P (loop i)) x x)
       → (sq : SquareP (λ i j → P (loop² i j)) p (λ i → x) (λ i → x) p)
       → isOfHLevelDep 3 P
       → (z : Bℤ₂) → P z
  elim P x p sq Pgpd = go
    where
    go : (z : Bℤ₂) → P z
    go base = x
    go (loop i) = p i
    go (loop² i j) = sq i j
    go (trunc x y p q r s i j k)
      = Pgpd (go x) (go y)
             (cong go p) (cong go q)
             (cong (cong go) r) (cong (cong go) s)
             (trunc x y p q r s) i j k
