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
  renaming (ℤ to ℤType ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

open CommRingStr

-- The missing additive inversion

+InvL' : ∀ n s → signed (not s) n +ℤ signed s n ≡ signed s zero
+InvL' zero _ = refl
+InvL' (suc n) spos = predℤ-+ʳ (neg n) (pos (suc n)) ∙ (λ i → neg n +ℤ predSucℤ (pos n) i) ∙ +InvL' n spos
+InvL' (suc n) sneg = sucℤ-+ʳ  (pos n) (neg (suc n)) ∙ (λ i → pos n +ℤ sucPredℤ (neg n) i) ∙ +InvL' n sneg

+InvL : (n : ℤType) → (-ℤ n) +ℤ n ≡ 0
+InvL (signed spos n) = +InvL' n spos
+InvL (signed sneg n) = +InvL' n sneg ∙ sym posneg
+InvL (posneg i) j =
  hcomp (λ k → λ
    { (i = i0) → 0
    ; (i = i1) → compPath-filler refl (sym posneg) k j
    ; (j = i0) → posneg i
    ; (j = i1) → posneg (i ∧ ~ k) })
  (posneg i)

+InvR : (n : ℤType) → n +ℤ (-ℤ n) ≡ 0
+InvR n = +-comm n (-ℤ n) ∙ +InvL n


ℤCommRing : CommRing ℓ-zero
ℤCommRing .fst = ℤType
ℤCommRing .snd .0r = 0
ℤCommRing .snd .1r = 1
ℤCommRing .snd ._+_ = _+ℤ_
ℤCommRing .snd ._·_ = _·ℤ_
ℤCommRing .snd .-_ = -ℤ_
ℤCommRing .snd .isCommRing = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing
      isSetℤ +-assoc (+-zeroʳ _)
      +InvR +-comm ·-assoc
      ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm
