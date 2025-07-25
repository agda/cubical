{-

ℤ is a Commutative Ring (using QuoInt)

-}
module Cubical.Algebra.CommRing.Instances.QuoInt where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat  using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (not)
open import Cubical.Data.Int.MoreInts.QuoInt
  renaming (ℤ to ℤType ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

open CommRingStr

-- The missing additive inversion

+ℤInvL' : ∀ n s → signed (not s) n +ℤ signed s n ≡ signed s zero
+ℤInvL' zero _ = refl
+ℤInvL' (suc n) spos = predℤ-+ʳ (neg n) (pos (suc n)) ∙ (λ i → neg n +ℤ predSucℤ (pos n) i) ∙ +ℤInvL' n spos
+ℤInvL' (suc n) sneg = sucℤ-+ʳ  (pos n) (neg (suc n)) ∙ (λ i → pos n +ℤ sucPredℤ (neg n) i) ∙ +ℤInvL' n sneg

+ℤInvL : (n : ℤType) → (-ℤ n) +ℤ n ≡ 0
+ℤInvL (signed spos n) = +ℤInvL' n spos
+ℤInvL (signed sneg n) = +ℤInvL' n sneg ∙ sym posneg
+ℤInvL (posneg i) j =
  hcomp (λ k → λ
    { (i = i0) → 0
    ; (i = i1) → compPath-filler refl (sym posneg) k j
    ; (j = i0) → posneg i
    ; (j = i1) → posneg (i ∧ ~ k) })
  (posneg i)

+ℤInvR : (n : ℤType) → n +ℤ (-ℤ n) ≡ 0
+ℤInvR n = +-comm n (-ℤ n) ∙ +ℤInvL n


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
      +ℤInvR +-comm ·-assoc
      ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm
