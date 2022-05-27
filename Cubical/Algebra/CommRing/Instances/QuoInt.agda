{-

ℤ is a Commutative Ring (using QuoInt)

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.QuoInt where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat  using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (not)
open import Cubical.Data.Int.MoreInts.QuoInt
  renaming ( ℤ to ℤType ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

open CommRingStr

-- The missing additive inversion

+-lInv' : ∀ n s → signed (not s) n +ℤ signed s n ≡ signed s zero
+-lInv' zero _ = refl
+-lInv' (suc n) spos = predℤ-+ʳ (neg n) (pos (suc n)) ∙ (λ i → neg n +ℤ predSucℤ (pos n) i) ∙ +-lInv' n spos
+-lInv' (suc n) sneg = sucℤ-+ʳ  (pos n) (neg (suc n)) ∙ (λ i → pos n +ℤ sucPredℤ (neg n) i) ∙ +-lInv' n sneg

+-lInv : (n : ℤType) → (-ℤ n) +ℤ n ≡ 0
+-lInv (signed spos n) = +-lInv' n spos
+-lInv (signed sneg n) = +-lInv' n sneg ∙ sym posneg
+-lInv (posneg i) j =
  hcomp (λ k → λ
    { (i = i0) → 0
    ; (i = i1) → compPath-filler refl (sym posneg) k j
    ; (j = i0) → posneg i
    ; (j = i1) → posneg (i ∧ ~ k) })
  (posneg i)

+-rInv : (n : ℤType) → n +ℤ (-ℤ n) ≡ 0
+-rInv n = +-comm n (-ℤ n) ∙ +-lInv n


ℤ : CommRing ℓ-zero
fst ℤ = ℤType
0r (snd ℤ) = 0
1r (snd ℤ) = 1
_+_ (snd ℤ) = _+ℤ_
_·_ (snd ℤ) = _·ℤ_
- snd ℤ = -ℤ_
isCommRing (snd ℤ) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing
      isSetℤ +-assoc (+-zeroʳ _)
      +-rInv +-comm ·-assoc
      ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm
