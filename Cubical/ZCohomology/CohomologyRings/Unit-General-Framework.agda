{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Unit-General-Framework where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Int
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group hiding (Unit ; ℤ; Bool ; _/_ )
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base renaming (base to baseP)
-- open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing

open import Cubical.Data.Unit
open import Cubical.ZCohomology.AbGroups.Unit

private variable
  ℓ : Level

open Iso

open CommRingStr (snd ℤCR) using ()
  renaming
  ( 0r        to 0ℤ
  ; 1r        to 1ℤ
  ; _+_       to _+ℤ_
  ; -_        to -ℤ_
  ; _·_       to _cup_
  ; +Assoc    to +ℤAssoc
  ; +Identity to +ℤIdentity
  ; +Lid      to +ℤLid
  ; +Rid      to +ℤRid
  ; +Inv      to +ℤInv
  ; +Linv     to +ℤLinv
  ; +Rinv     to +ℤRinv
  ; +Comm     to +ℤComm
  ; ·Assoc    to ·ℤAssoc
  ; ·Identity to ·ℤIdentity
  ; ·Lid      to ·ℤLid
  ; ·Rid      to ·ℤRid
  ; ·Rdist+   to ·ℤRdist+
  ; ·Ldist+   to ·ℤLdist+
  ; is-set    to isSetℤ     )

open RingStr (snd (H*R Unit)) using ()
  renaming
  ( 0r        to 0H*
  ; 1r        to 1H*
  ; _+_       to _+H*_
  ; -_        to -H*_
  ; _·_       to _cup_
  ; +Assoc    to +H*Assoc
  ; +Identity to +H*Identity
  ; +Lid      to +H*Lid
  ; +Rid      to +H*Rid
  ; +Inv      to +H*Inv
  ; +Linv     to +H*Linv
  ; +Rinv     to +H*Rinv
  ; +Comm     to +H*Comm
  ; ·Assoc    to ·H*Assoc
  ; ·Identity to ·H*Identity
  ; ·Lid      to ·H*Lid
  ; ·Rid      to ·H*Rid
  ; ·Rdist+   to ·H*Rdist+
  ; ·Ldist+   to ·H*Ldist+
  ; is-set    to isSetH*     )

ℤ[X] : CommRing ℓ-zero
ℤ[X] = PolyCommRing ℤCR 1

ℤ[x] : Type ℓ-zero
ℤ[x] = fst ℤ[X]

open CommRingStr (snd ℤ[X]) using ()
  renaming
  ( 0r        to 0Pℤ
  ; 1r        to 1Pℤ
  ; _+_       to _+Pℤ_
  ; -_        to -Pℤ_
  ; _·_       to _cup_
  ; +Assoc    to +PℤAssoc
  ; +Identity to +PℤIdentity
  ; +Lid      to +PℤLid
  ; +Rid      to +PℤRid
  ; +Inv      to +PℤInv
  ; +Linv     to +PℤLinv
  ; +Rinv     to +PℤRinv
  ; +Comm     to +PℤComm
  ; ·Assoc    to ·PℤAssoc
  ; ·Identity to ·PℤIdentity
  ; ·Lid      to ·PℤLid
  ; ·Rid      to ·PℤRid
  ; ·Rdist+   to ·PℤRdist+
  ; ·Ldist+   to ·PℤLdist+
  ; is-set    to isSetPℤ     )

-----------------------------------------------------------------------------
-- Definitions

X : FinVec ℤ[x] 1
X zero = baseP (1 ∷ []) (CommRingStr.1r (snd ℤCR))


-- finVec et pas du vec !
ℤ[X]/X : CommRing ℓ-zero
ℤ[X]/X = ℤ[X] / genIdeal ℤ[X] X

ℤ[x]/x : Type ℓ-zero
ℤ[x]/x = fst ℤ[X]/X


-----------------------------------------------------------------------------
-- Converse Sens

-- define it on the upper level, all properties on the upper level
-- cancel on I in both sens => goes throught the quotient
-- issue one side was hard to work with !

ℤ[x]→H*-Unit : ℤ[x] → H* Unit
ℤ[x]→H*-Unit = Poly-Rec-Set.f _ _ _ isSetH*
                0H*
                base-trad
                _+H*_
                +H*Assoc
                +H*Rid
                +H*Comm
                base-neutral-eq
                base-add-eq
             where
             base-trad : _
             base-trad (zero ∷ []) a = base zero (inv (fst H⁰-Unit≅ℤ) a)
             base-trad (suc n ∷ []) a = 0H*

             base-neutral-eq :  _
             base-neutral-eq (zero ∷ []) = base-neutral _
             base-neutral-eq (suc n ∷ []) = refl

             base-add-eq : _
             base-add-eq (zero ∷ []) a b = base-add _ _ _
                                            ∙ cong (base 0) (sym (IsGroupHom.pres· (snd (invGroupIso H⁰-Unit≅ℤ)) a b))
             base-add-eq (suc n ∷ []) a b = +H*Rid _




-----------------------------------------------------------------------------
-- Direct-Sens

H*-Unit→ℤ[x] : H* Unit → ℤ[x]
H*-Unit→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
                0Pℤ
                base-trad
                _+Pℤ_
                +PℤAssoc
                +PℤRid
                +PℤComm
                base-neutral-eq
                base-add-eq
             where
             base-trad : (n : ℕ) → coHom n Unit → ℤ[x]
             base-trad zero a = baseP (0 ∷ []) (fun (fst H⁰-Unit≅ℤ) a)
             base-trad (suc n) a = 0Pℤ

             base-neutral-eq : _
             base-neutral-eq zero = base-0P _
             base-neutral-eq (suc n) = refl

             base-add-eq : _
             base-add-eq zero a b = base-Poly+ _ _ _
                                    ∙ cong (baseP (0 ∷ [])) (sym (IsGroupHom.pres· (snd H⁰-Unit≅ℤ) a b))
             base-add-eq (suc n) a b = +PℤRid _


H*-Unit→ℤ[x]/x : H* Unit → ℤ[x]/x
H*-Unit→ℤ[x]/x = [_]/ ∘ H*-Unit→ℤ[x]
