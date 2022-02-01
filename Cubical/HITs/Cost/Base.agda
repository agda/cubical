{-# OPTIONS --safe #-}
module Cubical.HITs.Cost.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A B C : Type ℓ

Cost : (A : Type ℓ) → Type ℓ
Cost A = A × ∥ ℕ ∥

-- To compare two elements of Cost A we only need to look at the first parts
Cost≡ : (x y : Cost A) → x .fst ≡ y .fst → x ≡ y
Cost≡ _ _ = Σ≡Prop λ _ → squash

-- To make it easier to program with Cost A we prove that it forms a
-- monad which counts the number of calls to >>=. We could also turn
-- it into a proper state monad which tracks the cost, but for the
-- programs we write later this simple version suffices
_>>=_ : Cost A → (A → Cost B) → Cost B
(x , m) >>= g with g x
... | (y , n) = (y , map suc (map2 _+_ m n))

return : A → Cost A
return x = (x , ∣ 0 ∣)

-- The monad laws all hold by Cost≡

>>=-return : (f : Cost A) → f >>= return ≡ f
>>=-return f = Cost≡ _ _ refl

return->>= : (a : A) (f : A → Cost B) → return a >>= f ≡ f a
return->>= a f = Cost≡ _ _ refl

>>=-assoc : (f : Cost A) (g : A → Cost B) (h : B → Cost C)
          → (f >>= g) >>= h ≡ f >>= (λ x → g x >>= h)
>>=-assoc f g h = Cost≡ _ _ refl


-- An inefficient version of addition which recurses on both arguments
addBad : ℕ → ℕ → Cost ℕ
addBad 0 0       = return 0
addBad 0 (suc y) = do
  x ← addBad 0 y
  return (suc x)
addBad (suc x) y = do
  z ← addBad x y
  return (suc z)

-- More efficient addition which only recurse on the first argument
add : ℕ → ℕ → Cost ℕ
add 0       y = return y
add (suc x) y = do
  z ← add x y
  return (suc z)

private
  -- addBad x y will do x + y calls
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
fib 0 = return 0
fib 1 = return 1
fib (suc (suc x)) = do
  y ← fib (suc x)
  z ← fib x
  return (y + z)

fibTail : ℕ → Cost ℕ
fibTail 0       = return 0
fibTail (suc x) = fibAux x 1 0
  where
  fibAux : ℕ → ℕ → ℕ → Cost ℕ
  fibAux 0 res _          = return res
  fibAux (suc x) res prev = do
    r ← fibAux x (res + prev) res
    return r


private
  _ : fib 10 ≡ (55 , ∣ 176 ∣)
  _ = refl

  _ : fibTail 10 ≡ (55 , ∣ 9 ∣)
  _ = refl

  _ : fib 20 ≡ (6765 , ∣ 21890 ∣)
  _ = refl

  _ : fibTail 20 ≡ (6765 , ∣ 19 ∣)
  _ = refl

-- Exercise left to the reader: prove that fib and fibTail are equal functions
-- fib≡fibTail : fib ≡ fibTail
-- fib≡fibTail i x = Cost≡ (fib x) (fibTail x) (rem x) i
--   where
--   rem : (x : ℕ) → fib x .fst ≡ fibTail x .fst
--   rem zero = refl
--   rem (suc zero) = refl
--   rem (suc (suc x)) = {!!}
