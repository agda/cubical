{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.DirectProd where

open import Cubical.Foundations.Prelude
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
  open RingStr

  _+X×X'_ : X × X' → X × X' → X × X'
  _+X×X'_ = _+_ (snd (DirectProd-Ring Xr X'r))

  _+Y×Y'_ : Y × Y' → Y × Y' → Y × Y'
  _+Y×Y'_ = _+_ (snd (DirectProd-Ring Yr Y'r))

  _·X×X'_ : X × X' → X × X' → X × X'
  _·X×X'_ = _·_ (snd (DirectProd-Ring Xr X'r))

  _·Y×Y'_ : Y × Y' → Y × Y' → Y × Y'
  _·Y×Y'_ = _·_ (snd (DirectProd-Ring Yr Y'r))

  re×re' : (re : RingEquiv Xr Yr) → (re' : RingEquiv X'r Y'r) → (X × X') ≃ (Y × Y')
  re×re' re re' = ≃-× (fst re) (fst re')

  Coproduct-Equiv-12 : (re : RingEquiv Xr Yr) → (re' : RingEquiv X'r Y'r) →
                        RingEquiv (DirectProd-Ring Xr X'r) (DirectProd-Ring Yr Y'r)
  fst (Coproduct-Equiv-12 re re') = re×re' re re'
  snd (Coproduct-Equiv-12 re re') = makeIsRingHom fun-pres1 fun-pres+ fun-pres·
    where
    fun-pres1 : (fst (re×re' re re')) (1r Xstr , 1r X'str) ≡ (1r (Yr .snd) , 1r (Y'r .snd))
    fun-pres1 = ≡-× (pres1 (snd re)) (pres1 (snd re'))

    fun-pres+ : (x1 x2 : X × X') → (fst (re×re' re re')) (x1 +X×X' x2) ≡ (( (fst (re×re' re re')) x1) +Y×Y' ( (fst (re×re' re re')) x2))
    fun-pres+ (x1 , x'1) (x2 , x'2) = ≡-× (pres+ (snd re) x1 x2) (pres+ (snd re') x'1 x'2)

    fun-pres· : (x1 x2 : X × X') → (fst (re×re' re re')) (x1 ·X×X' x2) ≡ (( (fst (re×re' re re')) x1) ·Y×Y' ( (fst (re×re' re re')) x2))
    fun-pres· (x1 , x'1) (x2 , x'2) = ≡-× (pres· (snd re) x1 x2) (pres· (snd re') x'1 x'2)
