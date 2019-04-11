-- An example of something where normalization is surprisingly slow
{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Problem where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.Hopf

ptType : Type _
ptType = Σ Type₀ \ A → A

pt : (A : ptType) → A .fst
pt A = A .snd

S¹pt : ptType
S¹pt = (S¹ , base)
S²pt : ptType
S²pt = (S² , base)
S³pt : ptType
S³pt = (S³ , base)
joinpt : ptType
joinpt = (join S¹ S¹ , inl base)

Ω : (A : ptType) → ptType
Ω A = Path _ (pt A) (pt A) , refl
Ω² : (A : ptType) → ptType
Ω² A = Ω (Ω A)
Ω³ : (A : ptType) → ptType
Ω³ A = Ω² (Ω A)


α : join S¹ S¹ → S²
α (inl _) = base
α (inr _) = base
α (push x y i) = (merid y ∙ merid x) i
  where
  merid : S¹ → Path S² base base
  merid base = refl
  merid (loop i) = λ j → surf i j

-- The tests

test0To2 : Ω³ S³pt .fst
test0To2 i j k = surf i j k

f3 : Ω³ S³pt .fst → Ω³ joinpt .fst
f3 p i j k = S³→joinS¹S¹ (p i j k)

test0To3 : Ω³ joinpt .fst
test0To3 = f3 test0To2

f4 : Ω³ joinpt .fst → Ω³ S²pt .fst
f4 p i j k = α (p i j k)

test0To4 : Ω³ S²pt .fst
test0To4 = f4 test0To3

innerpath : ∀ i j → HopfS² (test0To4 i j i1)
innerpath i j = transp (λ k → HopfS² (test0To4 i j k)) i0 base

-- C-c C-n problem uses a lot of memory
problem : pos 0 ≡ pos 0
problem i = transp (λ j → helix (innerpath i j)) i0 (pos 0)


-- Lots of tests: (thanks Evan!)

winding2 : Path (Path S² base base) refl refl → Int
winding2 p = winding (λ j → transp (λ i → HopfS² (p i j)) i0 base)

test0 : Int
test0 = winding2 (λ i j → surf i j)

test1 : Int
test1 = winding2 (λ i j → surf j i)

test2 : Int
test2 = winding2 (λ i j → hcomp (λ _ → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) (surf i j))

test3 : Int
test3 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) base)

test4 : Int
test4 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) base)

test5 : Int
test5 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → surf k i ; (j = i1) → base}) base)

test6 : Int
test6 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → surf k i}) base)

test7 : Int
test7 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → surf j k ; (j = i0) → base ; (j = i1) → base}) (surf i j))

test8 : Int
test8 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → surf k i ; (j = i1) → base}) (surf i j))

test9 : Int
test9 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → surf k i}) (surf i j))

test10 : Int
test10 = winding2 (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) (surf i j))



-- Tests using HopfS²'

winding2' : Path (Path S² base base) refl refl → Int
winding2' p = winding (λ j → transp (λ i → HopfS²' (p i j)) i0 base)

test0' : Int
test0' = winding2' (λ i j → surf i j)

test1' : Int
test1' = winding2' (λ i j → surf j i)

test2' : Int
test2' = winding2' (λ i j → hcomp (λ _ → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) (surf i j))

test3' : Int
test3' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) base)

test4' : Int
test4' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) base)

test5' : Int
test5' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → surf k i ; (j = i1) → base}) base)

test6' : Int
test6' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → surf k i}) base)

test7' : Int
test7' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → surf j k ; (j = i0) → base ; (j = i1) → base}) (surf i j))

test8' : Int
test8' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → surf k i ; (j = i1) → base}) (surf i j))

test9' : Int
test9' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → base ; (i = i1) → base ; (j = i0) → base ; (j = i1) → surf k i}) (surf i j))

test10' : Int
test10' = winding2' (λ i j → hcomp (λ k → λ { (i = i0) → surf j k ; (i = i1) → base ; (j = i0) → base ; (j = i1) → base}) (surf i j))
