module Cubical.Algebra.Ring.Instances.Int where

open import Cubical.Algebra.Ring.Instances.BiInvInt
open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
import Cubical.Data.Int.MoreInts.BiInvInt as B
open import Cubical.Data.Nat
  hiding   (+-assoc ; +-comm ; ·-comm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc)

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring.Base
open import Cubical.Displayed.Base

private
  variable
    ℓ ℓ' : Level

ℤRawRingStr : RawRingStr ℤ
RawRingStr.0r ℤRawRingStr = pos zero
RawRingStr.1r ℤRawRingStr = pos (suc zero)
RawRingStr._+_ ℤRawRingStr = _+_
RawRingStr._·_ ℤRawRingStr = _·_
RawRingStr.- ℤRawRingStr = -_

ℤRawRing : RawRing _
ℤRawRing = ℤ ,  ℤRawRingStr

ℤ≃BiInvℤHom : IsRawRingHom ℤRawRingStr (B.ℤ≃BiInvℤ .fst) BiInvℤRawRingStr
IsRawRingHom.pres0 ℤ≃BiInvℤHom = refl
IsRawRingHom.pres1 ℤ≃BiInvℤHom = refl
IsRawRingHom.pres+ ℤ≃BiInvℤHom x y = l x y where
  l1 : (n : ℕ) → (y : ℤ) → B.ℤ≃BiInvℤ .fst ((ℤRawRingStr RawRingStr.+ pos n) y) ≡
                           B.ℤ≃BiInvℤ .fst (pos n) B.+ B.ℤ≃BiInvℤ .fst y
  l1 zero y =  cong B.fwd (sym (pos0+ _))
  l1 (suc n) y =   cong B.fwd (sym (sucℤ+ (pos n) y))
                 ∙ B.fwd-sucℤ _
                 ∙ cong B.suc (l1 n y)

  l2 : (n : ℕ) → (y : ℤ) → B.ℤ≃BiInvℤ .fst ((ℤRawRingStr RawRingStr.+ negsuc n) y) ≡
                          (BiInvℤRawRingStr RawRingStr.+ B.ℤ≃BiInvℤ .fst (negsuc n))
                          (B.ℤ≃BiInvℤ .fst y)
  l2 zero y =   cong B.fwd (sym (predℤ+ (pos zero) y))
              ∙ B.fwd-predℤ (pos zero + y)
              ∙ cong (λ x → B.predl (B.fwd x)) (sym (pos0+ _))
  l2 (suc n) y =   cong B.fwd (sym (predℤ+ (negsuc n) y))
                 ∙ B.fwd-predℤ (negsuc n + y)
                 ∙ cong B.predl (l2 n y)

  l : ∀ x → ∀ y → B.ℤ≃BiInvℤ .fst ((ℤRawRingStr RawRingStr.+ x) y) ≡
                    B.ℤ≃BiInvℤ .fst x B.+ B.ℤ≃BiInvℤ .fst y
  l (pos n) y = l1 n y
  l (negsuc n) y = l2 n y
IsRawRingHom.pres· ℤ≃BiInvℤHom (pos n) y = l1 n y where
  l1 : ∀ n → ∀ y →  B.ℤ≃BiInvℤ .fst ((ℤRawRingStr RawRingStr.· pos n) y) ≡
             B.ℤ≃BiInvℤ .fst (pos n) B.· B.ℤ≃BiInvℤ .fst y
  l1 zero y = refl
  l1 (suc n) y@(pos _) =   IsRawRingHom.pres+ ℤ≃BiInvℤHom y (pos n · y)
                          ∙ cong (λ x → B.fwd y B.+ x) (l1 n y)
  l1 (suc n) y@(negsuc _) =   IsRawRingHom.pres+ ℤ≃BiInvℤHom y (pos n · y)
                             ∙ cong (λ x → B.fwd y B.+ x) (l1 n y)
IsRawRingHom.pres· ℤ≃BiInvℤHom (negsuc n) y = l1 n y where
   l1 : ∀ n → ∀ y → B.ℤ≃BiInvℤ .fst ((ℤRawRingStr RawRingStr.· negsuc n) y) ≡
                    B.ℤ≃BiInvℤ .fst (negsuc n) B.· B.ℤ≃BiInvℤ .fst y
   l1 zero y@(pos _)    = IsRawRingHom.pres- ℤ≃BiInvℤHom y ∙ sym (B.+-zero ((B.-_ (B.fwd y))))
   l1 zero y@(negsuc _) = IsRawRingHom.pres- ℤ≃BiInvℤHom y ∙ sym (B.+-zero ((B.-_ (B.fwd y))))
   l1 (suc n) y@(pos _)    =   IsRawRingHom.pres+ ℤ≃BiInvℤHom (- y) ((negsuc n) · y)
                             ∙ cong₂ (λ a b → a B.+ b)
                                 (IsRawRingHom.pres- ℤ≃BiInvℤHom y)
                                 (l1 n y)
   l1 (suc n) y@(negsuc _) =   IsRawRingHom.pres+ ℤ≃BiInvℤHom (- y) ((negsuc n) · y)
                             ∙ cong₂ (λ a b → a B.+ b)
                                 (IsRawRingHom.pres- ℤ≃BiInvℤHom y)
                                 (l1 n y)
IsRawRingHom.pres- ℤ≃BiInvℤHom (pos n) = l1 n where
  l1 : ∀ n → B.ℤ≃BiInvℤ .fst ((RawRingStr.- ℤRawRingStr) (pos n)) ≡
      (      B.- B.ℤ≃BiInvℤ .fst (pos n))
  l1 zero = refl
  l1 (suc zero) = refl
  l1 (suc (suc n)) = cong B.pred (l1 (suc n))
IsRawRingHom.pres- ℤ≃BiInvℤHom (negsuc n) = l1 n where
  l1 : ∀ n → B.ℤ≃BiInvℤ .fst ((RawRingStr.- ℤRawRingStr) (negsuc n)) ≡
             (B.- B.ℤ≃BiInvℤ .fst (negsuc n))
  l1 zero = refl
  l1 (suc n) = cong B.suc (l1 n)

ℤRawRing≡BiInvℤRawRing : ℤRawRing ≡ BiInvℤRawRing
ℤRawRing≡BiInvℤRawRing = UARel.ua (∫ 𝒮ᴰ-RawRing) _ _ .fst (B.ℤ≃BiInvℤ  , ℤ≃BiInvℤHom)

ℤRingStr : RingStr ℤ
RingStr.rawRingStr ℤRingStr = ℤRawRingStr 
RingStr.isRing ℤRingStr = subst (λ (_ , y) → IsRing y) (sym ℤRawRing≡BiInvℤRawRing) BiInvℤIsRing

ℤRing : Ring _
ℤRing = ℤ , ℤRingStr

ℤRing≡BiInvℤRing : ℤRing ≡ BiInvℤRing
ℤRing≡BiInvℤRing = UARel.ua (∫ 𝒮ᴰ-Ring) _ _ .fst (B.ℤ≃BiInvℤ  , isringhom ℤ≃BiInvℤHom)

ℤCommRingStr : CommRingStr ℤ
CommRingStr.ringStr ℤCommRingStr = ℤRingStr
CommRingStr.isCommRing ℤCommRingStr = subst (λ (_ , y) → IsCommRing y) (sym ℤRing≡BiInvℤRing) BiInvℤIsCommRing

ℤCommRing : CommRing _
ℤCommRing = _ , ℤCommRingStr

ℤCommRing≡BiInvℤCommRing : ℤCommRing ≡ BiInvℤCommRing
ℤCommRing≡BiInvℤCommRing = UARel.ua (∫ 𝒮ᴰ-CommRing) _ _ .fst (B.ℤ≃BiInvℤ  , iscommringhom (isringhom ℤ≃BiInvℤHom))
