{-# OPTIONS --cubical --guardedness #-}

module Cubical.Codata.M.AsLimit.stream where

open import Cubical.Data.Nat
open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Foundations.Isomorphism

open import Cubical.Codata.Stream

open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

--------------------------------------
-- Stream definitions using M.AsLimit --
--------------------------------------

stream-S : ∀ A -> Container ℓ-zero
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Type₀) -> Type₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

------------------------------
-- Equality of stream types --
------------------------------

open Stream

stream-to-Stream : ∀ {A : Set} → stream A → Stream A
head (stream-to-Stream x) = (hd x)
tail (stream-to-Stream x) = (stream-to-Stream (tl x))

Stream-to-stream-func-x : ∀ {A : Set} (n : ℕ) -> Stream A → X (sequence (stream-S A)) n
Stream-to-stream-func-x 0 x = lift tt
Stream-to-stream-func-x (suc n) x = head x , λ _ → Stream-to-stream-func-x n (tail x)

Stream-to-stream-func-π : ∀ {A : Set} (n : ℕ) (a : Stream A) → π (sequence (stream-S A)) (Stream-to-stream-func-x (suc n) a) ≡ Stream-to-stream-func-x n a
Stream-to-stream-func-π 0 a = refl {x = lift tt}
Stream-to-stream-func-π (suc n) a = λ i → head a , λ _ → Stream-to-stream-func-π n (tail a) i

Stream-to-stream : ∀ {A : Set} -> Stream A -> stream A
Stream-to-stream s = lift-to-M Stream-to-stream-func-x Stream-to-stream-func-π s

hd-to-head : ∀ {A : Set} (b : Stream A) → hd (Stream-to-stream b) ≡ head b
hd-to-head {A = A} b = refl

head-to-hd : ∀ {A : Set} (b : stream A) → head (stream-to-Stream b) ≡ hd b
head-to-hd {A = A} b = refl

tail-to-tl : ∀ {A : Set} (b : stream A) → tail (stream-to-Stream b) ≡ stream-to-Stream (tl b)
tail-to-tl b = refl

postulate
  tl-to-tail : ∀ {A : Set} (b : Stream A) → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b) 
  -- should this comput ?

nth : ∀ {A : Set} → ℕ → (b : Stream A) → A
nth 0 b = head b
nth (suc n) b = nth n (tail b)

stream-equality-iso-1 : ∀ {A : Set} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
stream-equality-iso-1 b = bisim-nat (stream-to-Stream (Stream-to-stream b)) b (helper b)
  where
    helper : ∀ {A : Set} → (b : Stream A) → ((n : ℕ) → nth n (stream-to-Stream (Stream-to-stream b)) ≡ nth n b)
    helper b 0 = head-to-hd (Stream-to-stream b) ∙ hd-to-head b
    helper b (suc n) =
      nth (suc n) (stream-to-Stream (Stream-to-stream b))
        ≡⟨ refl ⟩
      nth n (tail (stream-to-Stream (Stream-to-stream b)))
        ≡⟨ cong (nth n) (tail-to-tl (Stream-to-stream b) ∙ cong stream-to-Stream (tl-to-tail b)) ⟩
      nth n (stream-to-Stream (Stream-to-stream (tail b)))
        ≡⟨ helper (tail b) n ⟩
      nth n (tail b) ∎

    bisim-nat : ∀ {A : Set} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≡ b
    bisim-nat a b nat-bisim = bisim (bisim-nat' a b nat-bisim)
      where
        open Equality≅Bisimulation
        open _≈_
  
        bisim-nat' : ∀ {A : Set} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≈ b
        ≈head (bisim-nat' a b nat-bisim) = nat-bisim 0
        ≈tail (bisim-nat' a b nat-bisim) = bisim-nat' (tail a) (tail b) (nat-bisim ∘ suc)

postulate
  stream-equality-iso-2 : ∀ {A : Set} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a

stream-equality : ∀ {A : Set} -> stream A ≡ Stream A
stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

------------------------------------------------------
-- Defining stream examples by transporting records --
------------------------------------------------------

-- Zeros defined as a record type
Zeros : Stream ℕ
head Zeros = 0
tail Zeros = Zeros

zeros-transported : stream ℕ
zeros-transported = transport (sym stream-equality) Zeros

-- It is now easy to show computation properties for the M-types:
hd-zeros-transported : hd zeros-transported ≡ 0
hd-zeros-transported = hd-to-head (transportRefl Zeros i0)

tl-zeros-transported : tl zeros-transported ≡ zeros-transported
tl-zeros-transported = tl-to-tail (transportRefl Zeros i0)

-- zeros defined for stream M-type
zeros : stream ℕ
zeros = lift-direct-M zeros-x zeros-π
  where
    zeros-x : (n : ℕ) → Wₙ (stream-S ℕ) n
    zeros-x 0 = lift tt
    zeros-x (suc n) = 0 , (λ _ → zeros-x n)
    
    zeros-π : (n : ℕ) → πₙ (stream-S ℕ) (zeros-x (suc n)) ≡ zeros-x n
    zeros-π 0 i = lift tt
    zeros-π (suc n) i = 0 , (λ _ → zeros-π n i)
