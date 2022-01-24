module Cubical.Algebra.Ring.Instances.BiInvInt where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.MoreInts.BiInvInt

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring.Base

BiInvℤCommRing : CommRing _
BiInvℤCommRing = makeCommRing zero (suc zero) _+_ _·_ -_ isSetBiInvℤ +-assoc +-zero +-invʳ +-comm ·-assoc
                              ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm

BiInvℤCommRingStr : CommRingStr BiInvℤ
BiInvℤCommRingStr = snd BiInvℤCommRing


BiInvℤRingStr : RingStr BiInvℤ
BiInvℤRingStr = CommRingStr.ringStr (snd BiInvℤCommRing)

BiInvℤIsCommRing : IsCommRing BiInvℤRingStr
BiInvℤIsCommRing = CommRingStr.isCommRing BiInvℤCommRingStr

BiInvℤRing : Ring _
BiInvℤRing = _ , BiInvℤRingStr

BiInvℤRawRingStr : RawRingStr BiInvℤ
BiInvℤRawRingStr = RingStr.rawRingStr (snd BiInvℤRing)

BiInvℤRawRing : RawRing _
BiInvℤRawRing = _ , BiInvℤRawRingStr

BiInvℤIsRing : IsRing BiInvℤRawRingStr
BiInvℤIsRing = RingStr.isRing BiInvℤRingStr
