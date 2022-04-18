{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.DirectProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Ring.Base

private
  variable
    ℓ ℓ' : Level

module _
  (A'@(A , Ar) : Ring ℓ)
  (B'@(B , Br) : Ring ℓ')
  where

  open RingStr Ar using ()
    renaming
    ( 0r        to 0A
    ; 1r        to 1A
    ; _+_       to _+A_
    ; -_        to -A_
    ; _·_       to _·A_
    ; +Assoc    to +AAssoc
    ; +Identity to +AIdentity
    ; +Lid      to +ALid
    ; +Rid      to +ARid
    ; +Inv      to +AInv
    ; +Linv     to +ALinv
    ; +Rinv     to +ARinv
    ; +Comm     to +AComm
    ; ·Assoc    to ·AAssoc
    ; ·Identity to ·AIdentity
    ; ·Lid      to ·ALid
    ; ·Rid      to ·ARid
    ; ·Rdist+   to ·ARdist+
    ; ·Ldist+   to ·ALdist+
    ; is-set    to isSetA     )

  open RingStr Br using ()
    renaming
    ( 0r        to 0B
    ; 1r        to 1B
    ; _+_       to _+B_
    ; -_        to -B_
    ; _·_       to _·B_
    ; +Assoc    to +BAssoc
    ; +Identity to +BIdentity
    ; +Lid      to +BLid
    ; +Rid      to +BRid
    ; +Inv      to +BInv
    ; +Linv     to +BLinv
    ; +Rinv     to +BRinv
    ; +Comm     to +BComm
    ; ·Assoc    to ·BAssoc
    ; ·Identity to ·BIdentity
    ; ·Lid      to ·BLid
    ; ·Rid      to ·BRid
    ; ·Rdist+   to ·BRdist+
    ; ·Ldist+   to ·BLdist+
    ; is-set    to isSetB     )

  DirectProd : Ring (ℓ-max ℓ ℓ')
  fst DirectProd = A × B
  RingStr.0r (snd DirectProd) = 0A , 0B
  RingStr.1r (snd DirectProd) = 1A , 1B
  (snd DirectProd RingStr.+ (a , b)) (a' , b') = (a +A a') , (b +B b')
  (snd DirectProd RingStr.· (a , b)) (a' , b') = (a ·A a') , (b ·B b')
  (RingStr.- snd DirectProd) (a , b) = (-A a) , (-B b)
  RingStr.isRing (snd DirectProd) =
    makeIsRing (isSet× isSetA isSetB)
    (λ x y z i → +AAssoc (fst x) (fst y) (fst z) i , +BAssoc (snd x) (snd y) (snd z) i)
    (λ x i → (+ARid (fst x) i) , (+BRid (snd x) i))
    (λ x i → (+ARinv (fst x) i) , +BRinv (snd x) i)
    (λ x y i → (+AComm (fst x) (fst y) i) , (+BComm (snd x) (snd y) i))
    (λ x y z i → (·AAssoc (fst x) (fst y) (fst z) i) , (·BAssoc (snd x) (snd y) (snd z) i))
    (λ x i → (·ARid (fst x) i) , (·BRid (snd x) i))
    (λ x i → (·ALid (fst x) i) , (·BLid (snd x) i))
    (λ x y z i → (·ARdist+ (fst x) (fst y) (fst z) i) , (·BRdist+ (snd x) (snd y) (snd z) i))
    (λ x y z i → (·ALdist+ (fst x) (fst y) (fst z) i) , (·BLdist+ (snd x) (snd y) (snd z) i))
