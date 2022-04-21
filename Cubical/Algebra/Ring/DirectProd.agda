{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.DirectProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Ring.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

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

  DirectProd-Ring : Ring (ℓ-max ℓ ℓ')
  fst DirectProd-Ring = A × B
  RingStr.0r (snd DirectProd-Ring) = 0A , 0B
  RingStr.1r (snd DirectProd-Ring) = 1A , 1B
  (snd DirectProd-Ring RingStr.+ (a , b)) (a' , b') = (a +A a') , (b +B b')
  (snd DirectProd-Ring RingStr.· (a , b)) (a' , b') = (a ·A a') , (b ·B b')
  (RingStr.- snd DirectProd-Ring) (a , b) = (-A a) , (-B b)
  RingStr.isRing (snd DirectProd-Ring) =
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

module Coproduct-Equiv
  {Xr@(X , Xstr) : Ring ℓ}
  {Yr@(Y , Ystr) : Ring ℓ'}
  {X'r@(X' , X'str) : Ring ℓ''}
  {Y'r@(Y' , Y'str) : Ring ℓ'''}
  where

  open Iso
  open IsRingHom

  Coproduct-Equiv-12 : (re : RingEquiv Xr Yr) → (re' : RingEquiv X'r Y'r) →
                        RingEquiv (DirectProd-Ring Xr X'r) (DirectProd-Ring Yr Y'r)
  fst (Coproduct-Equiv-12 re re') = isoToEquiv is
    where
    e : _
    e = equivToIso (fst re)

    e' : _
    e' = equivToIso (fst re')

    is : Iso (X × X') (Y × Y')
    fun is (x , x') = (fun e x) , (fun e' x')
    inv is (y , y') = (inv e y) , inv e' y'
    rightInv is (x , x') = ≡-× (rightInv e x) (rightInv e' x')
    leftInv is (y , y') = ≡-× (leftInv e y) (leftInv e' y')
  snd (Coproduct-Equiv-12 e e') = makeIsRingHom map1 map+ map·
    where
    map1 : _
    map1 = ≡-× (pres1 (snd e)) (pres1 (snd e'))

    map+ : _
    map+ (x1 , x'1) (x2 , x'2) = ≡-× (pres+ (snd e) x1 x2) (pres+ (snd e') x'1 x'2)

    map· : _
    map· (x1 , x'1) (x2 , x'2) = ≡-× (pres· (snd e) x1 x2) (pres· (snd e') x'1 x'2)
