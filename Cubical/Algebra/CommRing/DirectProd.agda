module Cubical.Algebra.CommRing.DirectProd where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd
open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ ℓ' : Level

module _
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : CommRing ℓ')
  where

  AB = DirectProd-Ring (CommRing→Ring A') (CommRing→Ring B')

  open RingStr (snd AB) using ()
    renaming
    ( 0r        to 0AB
    ; 1r        to 1AB
    ; _+_       to _+AB_
    ; -_        to -AB_
    ; _·_       to _·AB_
    ; +Assoc    to +ABAssoc
    ; +IdL      to +ABIdL
    ; +IdR      to +ABIdR
    ; +InvL     to +ABInvL
    ; +InvR     to +ABInvR
    ; +Comm     to +ABComm
    ; ·Assoc    to ·ABAssoc
    ; ·IdR      to ·ABIdR
    ; ·IdL      to ·ABIdL
    ; ·DistR+   to ·ABDistR+
    ; ·DistL+   to ·ABDistL+
    ; is-set    to isSetAB     )

  DirectProd-CommRing : CommRing (ℓ-max ℓ ℓ')
  fst DirectProd-CommRing = A × B
  CommRingStr.0r (snd DirectProd-CommRing) = 0AB
  CommRingStr.1r (snd DirectProd-CommRing) = 1AB
  CommRingStr._+_ (snd DirectProd-CommRing) = _+AB_
  CommRingStr._·_ (snd DirectProd-CommRing) = _·AB_
  CommRingStr.- snd DirectProd-CommRing = -AB_
  CommRingStr.isCommRing (snd DirectProd-CommRing) =
    makeIsCommRing
    isSetAB
    +ABAssoc
    +ABIdR
    +ABInvR
    +ABComm
    ·ABAssoc
    ·ABIdR
    ·ABDistR+
    λ x y i → (CommRingStr.·Comm Ar (fst x) (fst y) i) , (CommRingStr.·Comm Br (snd x) (snd y) i)
