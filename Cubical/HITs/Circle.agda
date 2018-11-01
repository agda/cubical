{-

Definition of the circle as a HIT

-}
{-# OPTIONS --cubical #-}

-- TODO: remove this!
{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.HITs.Circle where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Int
open import Cubical.Basics.Nat
open import Cubical.Basics.IsoToEquiv

data S¹ : Set where
  base : S¹
  loop : base ≡ base

helix : S¹ → Set
helix base     = Int
helix (loop i) = sucPathℤ i

ΩS¹ : Set
ΩS¹ = base ≡ base

encode : ∀ x → base ≡ x → helix x
encode x p = transp (λ i → helix (p i)) i0 (pos zero)

winding : ΩS¹ → Int
winding = encode base

intLoop : Int → ΩS¹
intLoop (pos zero)       = refl
intLoop (pos (suc n))    = compPath (intLoop (pos n)) loop
intLoop (negsuc zero)    = sym loop
intLoop (negsuc (suc n)) = compPath (intLoop (negsuc n)) (sym loop)

windingIntLoop : (n : Int) → winding (intLoop n) ≡ n
windingIntLoop (pos zero) = refl
windingIntLoop (pos (suc n)) = {!!} -- Why doesn't this solve the goal: λ i → sucℤ (windingIntLoop (pos n) i)
windingIntLoop (negsuc zero) = {!!} -- C-c C-r triggers internal error!
windingIntLoop (negsuc (suc n)) = {!!}

decodeSquare : (n : Int) → PathP (λ i → base ≡ loop i) (intLoop (predℤ n)) (intLoop n)
decodeSquare (pos zero) i j    = loop (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → base
                                                ; (j = i1) → loop k } )
                                       (inc (intLoop (pos n) j)) i
decodeSquare (negsuc n) i j = hcomp (λ k → λ { (i = i1) → intLoop (negsuc n) j
                                             ; (j = i0) → base
                                             ; (j = i1) → loop (i ∨ ~ k) })
                                    (intLoop (negsuc n) j)

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

decodeEncode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p =
  transp (λ i → decode (p i) (encode (p i) (λ j → p (i ∧ j))) ≡
                (λ j → p (i ∧ j))) i0 refl

ΩS¹≡Int : ΩS¹ ≡ Int
ΩS¹≡Int = isoToPath winding (decode base) windingIntLoop (decodeEncode base)


-- Some tests

five = suc (suc (suc (suc (suc zero))))

-- Hmm, these are not refl?

test-winding-pos : winding (intLoop (pos five)) ≡ pos five
test-winding-pos = refl

test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
test-winding-neg = refl
