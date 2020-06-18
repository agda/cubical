{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.TruncNat.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A : Type ℓ

TruncNat : Type
TruncNat = ∥ ℕ ∥

Cost : (A : Type ℓ) → Type ℓ
Cost A = A × TruncNat

-- To compare two elements of Cost we only need to look at the first parts
Cost≡ : (x y : Cost A) → x .fst ≡ y .fst → x ≡ y
Cost≡ _ _ = Σ≡Prop λ _ → squash

-- An inefficient version of addition which recurses on both arguments
addBad : ℕ → ℕ → Cost ℕ
addBad 0 0 = (0 , ∣ 0 ∣)
addBad 0 (suc y) with addBad 0 y
... | z , c = (suc z , map suc c)
addBad (suc x) y with addBad x y
... | z , c = (suc z , map suc c)

-- More efficient addition which only recurse on the first argument
add : ℕ → ℕ → Cost ℕ
add 0       y = (y , ∣ 0 ∣)
add (suc x) y with add x y
... | z , c = (suc z , map suc c)

private
  -- addBad x y will do x + y recursive calls
  _ : addBad 3 5 ≡ (8 , ∣ 8 ∣)
  _ = refl

  -- add x y will only do x recursive calls
  _ : add 3 5 ≡ (8 , ∣ 3 ∣)
  _ = refl

-- Despite addBad and add having different cost we can still prove
-- that they are equal functions
add≡addBad : add ≡ addBad
add≡addBad i x y = Cost≡ (add x y) (addBad x y) (rem x y) i
  where
  rem : (x y : ℕ) → add x y .fst ≡ addBad x y .fst
  rem 0 0       = refl
  rem 0 (suc y) = cong suc (rem 0 y)
  rem (suc x) y = cong suc (rem x y)



-- Another example: computing Fibonacci numbers

fib : ℕ → Cost ℕ
fib 0 = 0 , ∣ 0 ∣
fib 1 = 1 , ∣ 0 ∣
fib (suc (suc x)) with fib (suc x) | fib x
... | y , c1 | z , c2 = y + z , map (suc ∘ suc) (map2 _+_ c1 c2)

fibTail : ℕ → Cost ℕ
fibTail 0       = 0 , ∣ 0 ∣
fibTail (suc x) = fibAux x 1 0
  where
  fibAux : ℕ → ℕ → ℕ → Cost ℕ
  fibAux 0 res _ = res , ∣ 0 ∣
  fibAux (suc x) res prev with fibAux x (res + prev) res
  ... | r , cn = r , (map suc cn)


private
  _ : fib 10 ≡ (55 , ∣ 176 ∣)
  _ = refl

  _ : fibTail 10 ≡ (55 , ∣ 9 ∣)
  _ = refl

  _ : fib 20 ≡ (6765 , ∣ 21890 ∣)
  _ = refl

  _ : fibTail 20 ≡ (6765 , ∣ 19 ∣)
  _ = refl

-- TODO: finish this proof
-- fib≡fibTail : fib ≡ fibTail
-- fib≡fibTail i x = Cost≡ (fib x) (fibTail x) (rem x) i
--   where
--   rem : (x : ℕ) → fib x .fst ≡ fibTail x .fst
--   rem zero = refl
--   rem (suc zero) = refl
--   rem (suc (suc x)) = {!!}
