{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.BiInvInt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.Foundations.BiInvEquiv


-- Adapted from: https://github.com/RedPRL/redtt/blob/master/library/cool/biinv-int.red

data BiInvInt : Type₀ where
  zero : BiInvInt
  suc : BiInvInt -> BiInvInt
  
  -- suc is a bi-invertible equivalence:
  predr : BiInvInt -> BiInvInt
  suc-predr : ∀ z -> suc (predr z) ≡ z
  predl : BiInvInt -> BiInvInt
  predl-suc : ∀ z -> predl (suc z) ≡ z

suc-biiequiv : BiInvEquiv BiInvInt BiInvInt
suc-biiequiv = record { fun = suc ; invr = predr ; invr-rightInv = suc-predr
                                  ; invl = predl ; invl-leftInv  = predl-suc }

predr-suc : ∀ z -> predr (suc z) ≡ z
predr-suc = BiInvEquiv.invr-leftInv suc-biiequiv

suc-predl : ∀ z -> suc (predl z) ≡ z
suc-predl = BiInvEquiv.invl-rightInv suc-biiequiv

-- predr and predl are indistinguishable!
predr≡predl : ∀ z -> predr z ≡ predl z
predr≡predl = BiInvEquiv.invr≡invl suc-biiequiv

-- we arbitrarily define 'pred' to be predr
pred : BiInvInt -> BiInvInt
pred = predr


-- suc' is equal to suc (suc≡suc') but cancels pred *exactly* (see suc'-pred)

suc'ᵖ : (z : BiInvInt) -> Σ BiInvInt (suc z ≡_)
suc' = fst ∘ suc'ᵖ
suc≡suc' = snd ∘ suc'ᵖ

suc'ᵖ zero = suc zero , refl
suc'ᵖ (suc z) = suc (suc z) , refl
suc'ᵖ (predr z) = z , suc-predr z
suc'ᵖ (suc-predr z i) = let filler : I → I → BiInvInt
                            filler j i = hfill (λ j → λ { (i = i0) → suc (suc (predr z))
                                                        ; (i = i1) → suc≡suc' z j })
                                               (inS (suc (suc-predr z i))) j
                         in filler i1 i , λ j → filler j i
suc'ᵖ (predl z) = z , suc-predl z
suc'ᵖ (predl-suc z i) = let filler : I → I → BiInvInt
                            filler j i = hfill (λ j → λ { (i = i0) → suc-predl (suc z) j
                                                        ; (i = i1) → suc≡suc' z j })
                                               (inS (suc (predl-suc z i))) j
                         in filler i1 i , λ j → filler j i

suc'-pred : ∀ z → suc' (pred z) ≡ z
suc'-pred z = refl


-- pred' is equal to pred (pred≡pred') but cancels suc *exactly* (see pred'-suc)

predr'ᵖ : (z : BiInvInt) -> Σ BiInvInt (predr z ≡_)
predr' = fst ∘ predr'ᵖ
predr≡predr' = snd ∘ predr'ᵖ

predr'ᵖ zero = predr zero , refl
predr'ᵖ (suc z) = z , predr-suc z
predr'ᵖ (predr z) = predr (predr z) , refl
predr'ᵖ (suc-predr z i) = let filler : I → I → BiInvInt
                              filler j i = hfill (λ j → λ { (i = i0) → predr-suc (predr z) j
                                                          ; (i = i1) → predr≡predr' z j })
                                                 (inS (predr (suc-predr z i))) j
                           in filler i1 i , λ j → filler j i
predr'ᵖ (predl z) = predr (predl z) , refl
predr'ᵖ (predl-suc z i) = let filler : I → I → BiInvInt
                              filler j i = hfill (λ j → λ { (i = i0) → predr (predl (suc z))
                                                          ; (i = i1) → predr≡predr' z j })
                                                 (inS (predr (predl-suc z i))) j
                           in filler i1 i , λ j → filler j i

predl'ᵖ : (z : BiInvInt) -> Σ BiInvInt (predl z ≡_)
predl' = fst ∘ predl'ᵖ
predl≡predl' = snd ∘ predl'ᵖ

predl'ᵖ zero = predl zero , refl
predl'ᵖ (suc z) = z , predl-suc z
predl'ᵖ (predr z) = predl (predr z) , refl
predl'ᵖ (suc-predr z i) = let filler : I → I → BiInvInt
                              filler j i = hfill (λ j → λ { (i = i0) → predl-suc (predr z) j
                                                          ; (i = i1) → predl≡predl' z j })
                                                 (inS (predl (suc-predr z i))) j
                           in filler i1 i , λ j → filler j i
predl'ᵖ (predl z) = predl (predl z) , refl
predl'ᵖ (predl-suc z i) = let filler : I → I → BiInvInt
                              filler j i = hfill (λ j → λ { (i = i0) → predl (predl (suc z))
                                                          ; (i = i1) → predl≡predl' z j })
                                                 (inS (predl (predl-suc z i))) j
                           in filler i1 i , λ j → filler j i

predr'-suc : ∀ z → predr' (suc z) ≡ z
predr'-suc z = refl

predl'-suc : ∀ z → predl' (suc z) ≡ z
predl'-suc z = refl


-- 'normalizes' a BiInvInt, should be equal to the identity

norm : BiInvInt -> BiInvInt
norm zero = zero
norm (suc z) = suc' (norm z)
norm (predr z) = predr' (norm z)
norm (suc-predr z i) = let p : suc (predr (norm z)) ≡ suc' (predr' (norm z))
                           p = cong suc (predr≡predr' (norm z)) ∙ suc≡suc' (predr' (norm z))
                        in (sym p ∙ suc-predr (norm z)) i
norm (predl z) = predl' (norm z)
norm (predl-suc z i) = let p : predl (suc (norm z)) ≡ predl' (suc' (norm z))
                           p = cong predl (suc≡suc' (norm z)) ∙ predl≡predl' (suc' (norm z))
                        in (sym p ∙ predl-suc (norm z)) i

-- norm≡id : ∀ z → z ≡ norm z
-- norm≡id zero = refl
-- norm≡id (suc z) = suc≡suc' z ∙ cong suc' (norm≡id z)
-- norm≡id (predr z) = predr≡predr' z ∙ cong predr' (norm≡id z)
-- norm≡id (suc-predr z i) = {!!}
-- norm≡id (predl z) = predl≡predl' z ∙ cong predl' (norm≡id z)
-- norm≡id (predl-suc z i) = {!!}


-- Int ≡ BiInvInt

fwd : Int -> BiInvInt
fwd (pos zero) = zero
fwd (pos (suc n)) = suc (fwd (pos n))
fwd (negsuc zero) = pred zero
fwd (negsuc (suc n)) = pred (fwd (negsuc n))

bwd : BiInvInt -> Int
bwd zero = pos zero
bwd (suc x) = sucInt (bwd x)
bwd (predr x) = predInt (bwd x)
bwd (suc-predr x i) = sucPred (bwd x) i
bwd (predl x) = predInt (bwd x)
bwd (predl-suc x i) = predSuc (bwd x) i

bwd-fwd : ∀ (x : Int) -> bwd (fwd x) ≡ x
bwd-fwd (pos zero) = refl
bwd-fwd (pos (suc n)) = cong sucInt (bwd-fwd (pos n))
bwd-fwd (negsuc zero) = refl
bwd-fwd (negsuc (suc n)) = cong predInt (bwd-fwd (negsuc n))

-- fwd-bwd : ∀ (x : BiInvInt) -> fwd (bwd x) ≡ x
-- fwd-bwd zero = refl
-- fwd-bwd (suc x) = {!!}
-- fwd-bwd (predr x) = {!!}
-- fwd-bwd (suc-predr x i) = {!!}
-- fwd-bwd (predl x) = {!!}
-- fwd-bwd (predl-suc x i) = {!!}
