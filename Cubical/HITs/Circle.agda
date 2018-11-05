{-

Definition of the circle as a HIT

-}
{-# OPTIONS --cubical #-}
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

-- This should be refl
transpS¹ : ∀ (φ : I) (u0 : S¹) → transp (λ _ → S¹) φ u0 ≡ u0
transpS¹ φ u0 = refl -- transpFill {A' = S¹} φ (λ _ → inc S¹) u0 (~ i)

-- This should be trivial
compS1 : ∀ (φ : I) (u : ∀ i → Partial φ S¹) (u0 : S¹ [ φ ↦ u i0 ]) →
  comp (λ _ → S¹) u u0 ≡ hcomp u (ouc u0)
compS1 φ u u0 = refl -- hcomp (λ j → λ { (φ = i1) → transpS¹ j (u (j ∨ i0) 1=1) i })
                     --    (transpS¹ i0 (ouc u0) i)

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

-- Why is this not proved with refl?
hcompIntEmpty : (n : Int) → hcomp (λ _ → empty) n ≡ n
hcompIntEmpty n i = hfill (λ _ → empty) (inc n) (~ i)

-- This proof is far too complicated because of hcomp with emptys systems in Int!
windingIntLoop : (n : Int) → winding (intLoop n) ≡ n
windingIntLoop (pos zero) = refl
windingIntLoop (pos (suc n)) =
  -- The following should solve the goal: λ i → sucℤ (windingIntLoop (pos n) i)
  winding (intLoop (pos (suc n)))
  ≡⟨ refl ⟩
  hcomp {A = Int} (λ i → empty)
        (hcomp {A = Int} (λ i → empty)
        (hcomp {A = Int} (λ i → empty)
        (sucℤ (hcomp {A = Int} (λ i → empty) (winding (intLoop (pos n)))))))
  ≡⟨ hcompIntEmpty _ ⟩
  hcomp {A = Int} (λ i → empty)
        (hcomp {A = Int} (λ i → empty)
        (sucℤ (hcomp {A = Int} (λ i → empty) (winding (intLoop (pos n))))))
  ≡⟨ hcompIntEmpty _ ⟩
  hcomp {A = Int} (λ i → empty)
        (sucℤ (hcomp {A = Int} (λ i → empty) (winding (intLoop (pos n)))))
  ≡⟨ hcompIntEmpty _ ⟩
  sucℤ (hcomp {A = Int} (λ i → empty) (winding (intLoop (pos n))))
  ≡⟨ cong sucℤ (hcompIntEmpty _) ⟩
  sucℤ (winding (intLoop (pos n)))
  ≡⟨ cong sucℤ (windingIntLoop (pos n)) ⟩
  pos (suc n) ∎
windingIntLoop (negsuc zero) = refl
windingIntLoop (negsuc (suc n)) =
  winding (intLoop (negsuc (suc n))) ≡⟨ refl ⟩
  hcomp (λ i → empty)
        (hcomp (λ i → empty)
        (predℤ
        (hcomp (λ i → empty)
        (hcomp (λ i → empty)
        (winding (intLoop (negsuc n)))))))
  ≡⟨ hcompIntEmpty _ ⟩
  hcomp (λ i → empty)
        (predℤ (hcomp (λ i → empty)
               (hcomp (λ i → empty)
               (winding (intLoop (negsuc n))))))
  ≡⟨ hcompIntEmpty _ ⟩  
  predℤ (hcomp (λ i → empty)
        (hcomp (λ i → empty)
        (winding (intLoop (negsuc n)))))
  ≡⟨ cong predℤ (hcompIntEmpty _) ⟩  
  predℤ (hcomp (λ i → empty)
        (winding (intLoop (negsuc n))))
  ≡⟨ cong predℤ (hcompIntEmpty _) ⟩  
  predℤ (winding (intLoop (negsuc n)))
  ≡⟨ cong predℤ (windingIntLoop (negsuc n)) ⟩
  negsuc (suc n) ∎

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
module _ where
 private
  five : ℕ
  five = suc (suc (suc (suc (suc zero))))

  test-winding-pos : winding (intLoop (pos five)) ≡ pos five
  test-winding-pos = refl

  test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
  test-winding-neg = refl
