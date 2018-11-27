{-# OPTIONS --cubical #-}
module Cubical.Experiments.Problem where

open import Cubical.Core.Everything

open import Cubical.Basics.Int

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.Hopf

ptType : Set _
ptType = Σ Set \ A → A

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
α (push x y i) = compPath (merid y) (merid x) i
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

module M (p : Ω³ S²pt .fst) where
    innerpath : ∀ i j → HopfS² (p i j i1)
    innerpath i j = transp (λ k → HopfS² (p i j k)) i0 base

    problem : pos 0 ≡ pos 0
    problem i = transp (λ j → helix (innerpath i j)) i0 (pos 0)

    -- This term contains a ton of hcomp U:
    -- problempath : Path (helix (primTransp (\ k → Hopf (x k i0 k)) i0 base1))
    --                      (helix (primTransp (\ k → Hopf (x k i1 k)) i0 base1))
    -- problempath j = helix (primTransp (\ k → Hopf (x k j k)) i0 base1)

test = M.problem test0To4

-- C-c C-n test generates:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:72
