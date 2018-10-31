{- 

Definition of the circle as a HIT

-}
{-# OPTIONS --cubical #-}
module Cubical.HITs.Circle where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Int

data S¹ : Set where
  base : S¹
  loop : base ≡ base

helix : S¹ → Set
helix base     = Int
helix (loop i) = sucPathℤ i

winding : base ≡ base → Int
winding p = transp (λ i → helix (p i)) i0 (pos zero)

posLoop : ℕ → base ≡ base
posLoop zero = refl
posLoop (suc n) = compPath (posLoop n) loop

negLoop : ℕ → base ≡ base
negLoop zero = sym loop
negLoop (suc n) = compPath (negLoop n) (sym loop)

intLoop : Int → base ≡ base
intLoop (pos n) = posLoop n
intLoop (negsuc n) = negLoop n

-- upstream
Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i ≡ v i)) r0 r1

decodeSquarePos : (n : ℕ) → Square refl loop (intLoop (predℤ (pos n))) (intLoop (pos n))
decodeSquarePos zero i j    = loop (i ∨ ~ j)
decodeSquarePos (suc n) i j = hfill (λ k → λ { (j = i0) → base
                                             ; (j = i1) → loop k } )
                                    (inc (posLoop n j)) i

decodeSquareNeg : (n : ℕ) → Square refl loop (intLoop (negsuc (suc n))) (intLoop (negsuc n))
decodeSquareNeg n i j = hcomp (λ k → λ { (i = i1) → negLoop n j
                                       ; (j = i0) → base
                                       ; (j = i1) → loop (i ∨ ~ k) })
                              (negLoop n j)

decodeSquare : (n : Int) → Square refl loop (intLoop (predℤ n)) (intLoop n)
decodeSquare (pos n)    = decodeSquarePos n
decodeSquare (negsuc n) = decodeSquareNeg n

decode : (x : S¹) → helix x → base ≡ x
decode base = intLoop
decode (loop i) y j =
  let n : Int
      n = unglue {φ = i ∨ ~ i} y
  in hcomp (λ k → λ { (j = i0) → base
                    ; (j = i1) → loop i
                    ; (i = i0) → intLoop (predSuc y k) j
                    ; (i = i1) → intLoop y j})
           (decodeSquare n i j )

encode : ∀ x → base ≡ x → helix x
encode x p = transp (λ i → helix (p i)) i0 (pos zero)

decodeEncode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = transp (λ i → decode (p i) (encode (p i) (λ j → p (i ∧ j))) ≡ (λ j → p (i ∧ j))) i0 refl



-- Some tests

five = suc (suc (suc (suc (suc zero))))

-- Hmm, these are not refl?

test-winding-pos : winding (intLoop (pos five)) ≡ pos five
test-winding-pos = {!refl!}

test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
test-winding-neg = {!!}
