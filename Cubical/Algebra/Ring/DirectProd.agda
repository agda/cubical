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
    ; +IdR      to +AIdR
    ; +IdL      to +AIdL
    ; +InvR     to +AInvR
    ; +InvL     to +AInvL
    ; +Comm     to +AComm
    ; ·Assoc    to ·AAssoc
    ; ·IdL      to ·AIdL
    ; ·IdR      to ·AIdR
    ; ·DistR+   to ·ADistR+
    ; ·DistL+   to ·ADistL+
    ; is-set    to isSetA     )

  open RingStr Br using ()
    renaming
    ( 0r        to 0B
    ; 1r        to 1B
    ; _+_       to _+B_
    ; -_        to -B_
    ; _·_       to _·B_
    ; +Assoc    to +BAssoc
    ; +IdR      to +BIdR
    ; +IdL      to +BIdL
    ; +InvR     to +BInvR
    ; +InvL     to +BInvL
    ; +Comm     to +BComm
    ; ·Assoc    to ·BAssoc
    ; ·IdL      to ·BIdL
    ; ·IdR      to ·BIdR
    ; ·DistR+   to ·BDistR+
    ; ·DistL+   to ·BDistL+
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
    (λ x i → (+AIdR (fst x) i) , (+BIdR (snd x) i))
    (λ x i → (+AInvR (fst x) i) , +BInvR (snd x) i)
    (λ x y i → (+AComm (fst x) (fst y) i) , (+BComm (snd x) (snd y) i))
    (λ x y z i → (·AAssoc (fst x) (fst y) (fst z) i) , (·BAssoc (snd x) (snd y) (snd z) i))
    (λ x i → (·AIdR (fst x) i) , (·BIdR (snd x) i))
    (λ x i → (·AIdL (fst x) i) , (·BIdL (snd x) i))
    (λ x y z i → (·ADistR+ (fst x) (fst y) (fst z) i) , (·BDistR+ (snd x) (snd y) (snd z) i))
    (λ x y z i → (·ADistL+ (fst x) (fst y) (fst z) i) , (·BDistL+ (snd x) (snd y) (snd z) i))

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
