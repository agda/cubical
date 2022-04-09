{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Unit-Direct-Carac where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Int
open import Cubical.Data.Sum

open import Cubical.Algebra.Group hiding (Unit ; ℤ; Bool)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties

open import Cubical.HITs.Susp
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

ℤR = CommRing→Ring ℤCR

open RingStr (snd (H*R Unit))
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

open RingStr (snd ℤR)
  renaming
  ( 0r        to 0z
  ; 1r        to 1z
  ; _+_       to _+z_
  ; -_        to -z_
  ; _·_       to _·z_
  ; +Assoc    to +zAssoc
  ; +Identity to +zIdentity
  ; +Lid      to +zLid
  ; +Rid      to +zRid
  ; +Inv      to +zInv
  ; +Linv     to +zLinv
  ; +Rinv     to +zRinv
  ; +Comm     to +zComm
  ; ·Assoc    to ·zAssoc
  ; ·Identity to ·zIdentity
  ; ·Lid      to ·zLid
  ; ·Rid      to ·zRid
  ; ·Rdist+   to ·zRdist+
  ; ·Ldist+   to ·zLdist+   )

-----------------------------------------------------------------------------
-- Direct Sens

H*-Unit→ℤ : H* Unit → ℤ
H*-Unit→ℤ = DS-Rec-Set.f ℕ _ _ ℤ isSetℤ
               0z
               trad-base
               _+z_
               +zAssoc
               +zRid
               +zComm
               eq-base-neutral
               eq-base-add
  where
  trad-base : (n : ℕ) → (a : coHom n Unit) → ℤ
  trad-base zero a = Iso.fun (fst H⁰-Unit≅ℤ) a
  trad-base (suc n) a = 0z

  eq-base-neutral : _
  eq-base-neutral zero = refl
  eq-base-neutral (suc n) = refl

  eq-base-add : _
  eq-base-add zero = sElim2 (λ _ _ → isSet→isGroupoid isSetℤ _ _) (λ a b → refl)
  eq-base-add (suc n) a b = refl

H*-Unit→ℤ-map1 : H*-Unit→ℤ 1H* ≡ 1z
H*-Unit→ℤ-map1 = refl

H*-Unit→ℤ-gmorph : (x y : H* Unit) → H*-Unit→ℤ ( x +H* y) ≡ H*-Unit→ℤ x +z H*-Unit→ℤ y
H*-Unit→ℤ-gmorph x y = refl

-- hard but doable ? doable in a more general case ???
-- H*-Unit→ℤ-rmorph : (x y : H* Unit) → H*-Unit→ℤ ( x cup y) ≡ H*-Unit→ℤ x ·z H*-Unit→ℤ y
-- H*-Unit→ℤ-rmorph = DS-Ind-Prop.f _ _ _ _
--                     (λ x p q i y → isSetℤ _ _ (p y) (q y) i )
--                     (λ y → refl)
--                     -- One should also do an induction on n and m !!!
--                     (λ n → sElim (λ x → isProp→isSet (λ p q i y j → isSetℤ _ _ (p y) (q y) i j))
--                             λ a → DS-Ind-Prop.f _ _ _ _
--                                    (λ _ → isSetℤ _ _)
--                                    (sym (RingTheory.0RightAnnihilates ℤR  _))
--                                    (λ m → sElim {!!}
--                                           (λ b → {!refl!}))
--                                    λ {U V} ind-U ind-V → (cong₂ _+z_ ind-U ind-V) ∙ sym (·zRdist+ _ _ _))
--                     λ {U V} ind-U ind-V y → (cong₂ _+z_ (ind-U y) (ind-V y)) ∙ sym (·zLdist+ _ _ _)

-----------------------------------------------------------------------------
-- Converse Sens

ℤ→H*-Unit : ℤ → H* Unit
ℤ→H*-Unit z = base 0 (Iso.inv (fst H⁰-Unit≅ℤ) z)

ℤ→H*-Unit-map1 : ℤ→H*-Unit 1z ≡ 1H*
ℤ→H*-Unit-map1 = refl

-- gmorph is not needed but it is better to have it
ℤ→H*-Unit-gmorph : (x y : ℤ) → ℤ→H*-Unit ( x +z y) ≡ ℤ→H*-Unit x +H* ℤ→H*-Unit y
ℤ→H*-Unit-gmorph x y = cong {ℓ-zero} {coHom 0 Unit} {ℓ-zero} {λ _ → H* Unit} -- ask anders
                        (base 0) (gmorph x y)
                        ∙ sym (base-add 0 (Iso.inv (fst H⁰-Unit≅ℤ) x) (Iso.inv (fst H⁰-Unit≅ℤ) y))
                 where
                 gmorph : _
                 gmorph = IsGroupHom.pres· (snd (invGroupIso H⁰-Unit≅ℤ))


ℤ→H*-Unit-rmorph : (x y : ℤ) → ℤ→H*-Unit ( x ·z y) ≡ ℤ→H*-Unit x cup ℤ→H*-Unit y
ℤ→H*-Unit-rmorph x y = cong {ℓ-zero} {coHom 0 Unit} {ℓ-zero} {λ _ → H* Unit} (base 0)
                        (cong ∣_∣₂ (did x y))
                 where
                 did : (x y : ℤ) → (λ _ → x ·z y) ≡ (λ x₁ → x ·₀ y)
                 did (pos zero) y = refl
                 did (pos (suc n)) y = funExt (λ z → cong (y +z_) λ i → did (pos n) y i z)
                 did (negsuc zero) y = funExt (λ z  → sym (+zLid (negsuc zero ·z y)))
                 did (negsuc (suc n)) y = funExt (λ z → (+zComm _ _)
                                          ∙ cong₂ _+z_ (λ i → did (negsuc n) y i z) (sym (+zLid (negsuc zero ·z y))))



-----------------------------------------------------------------------------
-- Section

e-sect : retract H*-Unit→ℤ ℤ→H*-Unit
e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _ )
         (base-neutral 0)
         eq-base
         λ {U V} ind-U ind-V → ℤ→H*-Unit-gmorph (H*-Unit→ℤ U) (H*-Unit→ℤ V) ∙ cong₂ _+H*_ ind-U ind-V
  where
  eq-base : (n : ℕ) (a : coHom n Unit) → ℤ→H*-Unit (H*-Unit→ℤ (base n a)) ≡ base n a
  eq-base zero a = cong {ℓ-zero} {coHom 0 Unit} {ℓ-zero} {λ _ → H* Unit}
                   (base 0) (Iso.leftInv (fst H⁰-Unit≅ℤ) a)
                    -- the others groups are trivial
  eq-base (suc n) a = base-neutral 0 ∙ sym (base-neutral (suc n))
                      ∙ cong {ℓ-zero} {coHom (suc n) Unit} {ℓ-zero} {λ _ → H* Unit}
                        (base (suc n)) (isContr→isProp (isContrHⁿ-Unit n) _ a)


-----------------------------------------------------------------------------
-- Retraction

e-retr : section H*-Unit→ℤ ℤ→H*-Unit
e-retr z = Iso.rightInv (fst H⁰-Unit≅ℤ) z

-----------------------------------------------------------------------------
-- Ring Equiv

H*-Unit≅ℤ : RingEquiv ℤR (H*R Unit)
fst H*-Unit≅ℤ = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = ℤ→H*-Unit
  Iso.inv is = H*-Unit→ℤ
  Iso.rightInv is = e-sect
  Iso.leftInv is = e-retr
snd H*-Unit≅ℤ = makeIsRingHom ℤ→H*-Unit-map1 ℤ→H*-Unit-gmorph ℤ→H*-Unit-rmorph
