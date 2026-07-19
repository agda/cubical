{- The circle using _≡_

- loop path-"constructor" using _≡_

- recursion and induction scheme

- β-rules for recursion and induction in terms of _≡_

-}

module Cubical.Data.Equality.S1 where

open import Cubical.Foundations.Prelude
  using (PathP)
  renaming (cong to congPath)

open import Cubical.HITs.S1 as S1 public
  using (S¹; base)

open import Cubical.HITs.S1 as S1
  using ()
  renaming (loop to loopPath)

open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.Conversion
open import Cubical.Data.Equality.Univalence

private
 variable
  a ℓ ℓ' : Level
  A : Type a

loop : base ≡ base
loop = pathToEq loopPath

S¹-rec : {A : Type ℓ} (b : A) (l : b ≡ b) → S¹ → A
S¹-rec b l = S1.rec b (eqToPath l)

S¹-rec-loop : (b : A) (l : b ≡ b) → ap (S¹-rec b l) loop ≡ l
S¹-rec-loop b l =
  ap (S¹-rec b l) loop                      ≡⟨ ap≡congPath (S¹-rec b l) loopPath ⟩
  pathToEq (congPath (S¹-rec b l) loopPath) ≡⟨ refl ⟩
  pathToEq (eqToPath l)                     ≡⟨ pathToEq (pathToEq-eqToPath l) ⟩
  l ∎

S¹-elimPath : (P : S¹ → Type ℓ) (b : P base) (l : PathP (λ i → P (loopPath i)) b b) → (x : S¹) → P x
S¹-elimPath _ b l base         = b
S¹-elimPath _ b l (loopPath i) = l i

S¹-elim : (P : S¹ → Type ℓ) (b : P base) (l : transport P loop b ≡ b) → (x : S¹) → P x
S¹-elim P b l = S¹-elimPath P b (pathOver→PathP P loopPath l)

S¹-elim-base : (C : S¹ → Type ℓ) (b : C base) (l : transport C loop b ≡ b) → S¹-elim C b l base ≡ b
S¹-elim-base C b l = refl

S¹-elim-loop : (C : S¹ → Type ℓ) (b : C base) (l : transport C loop b ≡ b) → apd (S¹-elim C b l) loop ≡ l
S¹-elim-loop C b l = cong-PathP→apd-pathOver C (S¹-elim C b l) loopPath l refl


-- We now compute some winding numbers to check that everything computes as expected

Cover : S¹ → Type₀
Cover = S¹-rec ℤ (pathToEq sucPathℤ)

ΩS¹ : Type₀
ΩS¹ = base ≡ base

encode : {x : S¹} → base ≡ x → Cover x
encode p = transport Cover p (pos zero)

winding : ΩS¹ → ℤ
winding = encode {base}

loop^ : ℤ → ΩS¹
loop^ (pos zero)       = refl
loop^ (pos (suc n))    = loop^ (pos n) ∙ loop
loop^ (negsuc zero)    = sym loop
loop^ (negsuc (suc n)) = loop^ (negsuc n) ∙ sym loop

private
  test-winding-refl : winding refl ≡ pos 0
  test-winding-refl = refl

  test-winding-loop : winding loop ≡ pos 1
  test-winding-loop = refl

  test-winding-pos5 : winding (loop^ (pos 2)) ≡ pos 2
  test-winding-pos5 = refl

  test-winding-neg5 : winding (loop^ (negsuc 2)) ≡ negsuc 2
  test-winding-neg5 = refl
