{-# OPTIONS --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.RingStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.NatPlusBis
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.DirectSumHIT

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT

open import Cubical.HITs.SetTruncation as ST

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

private variable
  ℓ ℓ' ℓ'' : Level

open Iso

-----------------------------------------------------------------------------
-- Definition Cohomology Ring

open PlusBis
open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆
open RingStr


module _ (R : Ring ℓ') (A : Type ℓ) where
  private
    R-ab = Ring→AbGroup R

  H*R : Ring _
  H*R = ⊕HITgradedRing-Ring
        NatPlusBis-Monoid
        (λ k → coHom k R-ab A)
        (λ k → snd (coHomGr k R-ab A))
        1ₕ
        _⌣_
        (λ {k} {l} → 0ₕ-⌣ k l)
        (λ {k} {l} → ⌣-0ₕ k l)
        (λ _ _ _ → sym (ΣPathTransport→PathΣ _ _ (sym (+'-assoc _ _ _) , flipTransport (assoc⌣ _ _ _ _ _ _))))
        (λ {n} a → sym (ΣPathTransport→PathΣ _ _ (sym (+'-rid _)
                  , sym (⌣-1ₕ _ _ ∙ cong (λ p → subst (λ p → coHom p R-ab A) p a)
                        (isSetℕ _ _ _ _)))))
        (λ _ → ΣPathTransport→PathΣ _ _ (refl , transportRefl _ ∙ 1ₕ-⌣ _ _))
        (λ _ _ _ → distrL⌣ _ _ _ _ _)
        λ _ _ _ → distrR⌣ _ _ _ _ _

  H* : Type _
  H* = fst H*R

module CohomologyRing-Equiv
  {R : Ring ℓ}
  {X : Type ℓ'}
  {Y : Type ℓ''}
  (e : Iso X Y)
  where
  private
    R-ab = Ring→AbGroup R

  open IsGroupHom

  open RingStr (snd (H*R R X)) using ()
    renaming
    ( 0r        to 0H*X
    ; 1r        to 1H*X
    ; _+_       to _+H*X_
    ; -_        to -H*X_
    ; _·_       to _cupX_
    ; +Assoc    to +H*XAssoc
    ; +IdR      to +H*XIdR
    ; +Comm     to +H*XComm
    ; ·Assoc    to ·H*XAssoc
    ; is-set    to isSetH*X     )

  open RingStr (snd (H*R R Y)) using ()
    renaming
    ( 0r        to 0H*Y
    ; 1r        to 1H*Y
    ; _+_       to _+H*Y_
    ; -_        to -H*Y_
    ; _·_       to _cupY_
    ; +Assoc    to +H*YAssoc
    ; +IdR      to +H*YIdR
    ; +Comm     to +H*YComm
    ; ·Assoc    to ·H*YAssoc
    ; is-set    to isSetH*Y     )


  coHomGr-Iso : {n : ℕ} → AbGroupIso (coHomGr n R-ab X) (coHomGr n R-ab Y)
  fst (coHomGr-Iso {n}) = is
    where
    is : Iso (coHom n R-ab X) (coHom n R-ab Y)
    fun is = ST.rec squash₂ (λ f → ∣ (λ y → f (inv e y)) ∣₂)
    inv is = ST.rec squash₂ (λ g → ∣ (λ x → g (fun e x)) ∣₂)
    rightInv is = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ f → cong ∣_∣₂ (funExt (λ y → cong f (rightInv e y))))
    leftInv is = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ g → cong ∣_∣₂ (funExt (λ x → cong g (leftInv e x))))
  snd (coHomGr-Iso {n}) = makeIsGroupHom
                                        (ST.elim (λ _ → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i)
                                        (λ f → ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                                        (λ f' → refl)))

  H*-X→H*-Y : H* R X → H* R Y
  H*-X→H*-Y = DS-Rec-Set.f _ _ _ _ isSetH*Y
               0H*Y
               (λ n a → base n (fun (fst coHomGr-Iso) a))
               _+H*Y_
               +H*YAssoc
               +H*YIdR
               +H*YComm
               (λ n → cong (base n) (pres1 (snd coHomGr-Iso)) ∙ base-neutral n)
               λ n a b → base-add _ _ _ ∙ cong (base n) (sym (pres· (snd coHomGr-Iso) a b))

  H*-Y→H*-X : H* R Y → H* R X
  H*-Y→H*-X = DS-Rec-Set.f _ _ _ _ isSetH*X
               0H*X
               (λ m a → base m (inv (fst coHomGr-Iso) a))
               _+H*X_
               +H*XAssoc
               +H*XIdR
               +H*XComm
               (λ m → cong (base m) (pres1 (snd (invGroupIso coHomGr-Iso))) ∙ base-neutral m)
               λ m a b → base-add _ _ _ ∙ cong (base m) (sym (pres· (snd (invGroupIso coHomGr-Iso)) a b))

  e-sect : (y : H* R Y) → H*-X→H*-Y (H*-Y→H*-X y) ≡ y
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*Y _ _)
           refl
           (λ m a → cong (base m) (rightInv (fst coHomGr-Iso) a))
           (λ {U V} ind-U ind-V → cong₂ _+H*Y_ ind-U ind-V)

  e-retr : (x : H* R X) → H*-Y→H*-X (H*-X→H*-Y x) ≡ x
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X _ _)
           refl
           (λ n a → cong (base n) (leftInv (fst coHomGr-Iso) a))
           (λ {U V} ind-U ind-V → cong₂ _+H*X_ ind-U ind-V)

  H*-X→H*-Y-pres1 : H*-X→H*-Y 1H*X ≡ 1H*Y
  H*-X→H*-Y-pres1 = refl

  H*-X→H*-Y-pres+ : (x x' : H* R X) → H*-X→H*-Y (x +H*X x') ≡ H*-X→H*-Y x +H*Y H*-X→H*-Y x'
  H*-X→H*-Y-pres+ x x' = refl

  H*-X→H*-Y-pres· : (x x' : H* R X) → H*-X→H*-Y (x cupX x') ≡ H*-X→H*-Y x cupY H*-X→H*-Y x'
  H*-X→H*-Y-pres· = DS-Ind-Prop.f _ _ _ _ (λ x u v i y → isSetH*Y _ _ (u y) (v y) i)
         (λ _ → refl)
         (λ n → ST.elim (λ x → isProp→isSet λ u v i y → isSetH*Y _ _ (u y) (v y) i)
                (λ f → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*Y _ _)
                        refl
                        (λ m → ST.elim (λ _ → isProp→isSet (isSetH*Y _ _))
                                (λ g → refl))
                        λ {U V} ind-U ind-V → cong₂ _+H*Y_ ind-U ind-V) )
         (λ {U V} ind-U ind-V y → cong₂ _+H*Y_ (ind-U y) (ind-V y))


module _
  {R : Ring ℓ}
  {X : Type ℓ'}
  {Y : Type ℓ''}
  (e : Iso X Y)
  where

  open CohomologyRing-Equiv {R = R} e
  CohomologyRing-Equiv : RingEquiv (H*R R X) (H*R R Y)
  fst CohomologyRing-Equiv = isoToEquiv is
    where
    is : Iso (H* R X) (H* R Y)
    fun is = H*-X→H*-Y
    inv is = H*-Y→H*-X
    rightInv is = e-sect
    leftInv is = e-retr
  snd CohomologyRing-Equiv =
    makeIsRingHom H*-X→H*-Y-pres1 H*-X→H*-Y-pres+ H*-X→H*-Y-pres·
