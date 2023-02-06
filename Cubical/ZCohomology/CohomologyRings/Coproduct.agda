{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Coproduct
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing

private variable
  ℓ ℓ' : Level

module Equiv-Coproduct-Properties
  {X : Type ℓ}
  {Y : Type ℓ'}
  where

  open Iso
  open IsGroupHom
  open GroupStr
  open PlusBis

  open RingStr (snd (H*R X)) using ()
    renaming
    ( 0r        to 0H*X
    ; 1r        to 1H*X
    ; _+_       to _+H*X_
    ; -_        to -H*X_
    ; _·_       to _cupX_
    ; +Assoc    to +H*XAssoc
    ; +IdL      to +H*XIdL
    ; +IdR      to +H*XIdR
    ; +Comm     to +H*XComm
    ; ·Assoc    to ·H*XAssoc
    ; ·IdL      to ·H*XIdL
    ; ·IdR      to ·H*XIdR
    ; is-set    to isSetH*X     )

  open RingStr (snd (H*R Y)) using ()
    renaming
    ( 0r        to 0H*Y
    ; 1r        to 1H*Y
    ; _+_       to _+H*Y_
    ; -_        to -H*Y_
    ; _·_       to _cupY_
    ; +Assoc    to +H*YAssoc
    ; +IdL      to +H*YIdL
    ; +IdR      to +H*YIdR
    ; +Comm     to +H*YComm
    ; ·Assoc    to ·H*YAssoc
    ; ·IdL      to ·H*YIdL
    ; ·IdR      to ·H*YIdR
    ; is-set    to isSetH*Y     )

  -- warning this does not open H*(X×Y) !
  -- This just a notation shorter and pratical
  open RingStr (snd (DirectProd-Ring (H*R X) (H*R Y))) using ()
    renaming
    ( 0r        to 0H*X×Y
    ; 1r        to 1H*X×Y
    ; _+_       to _+H*X×Y_
    ; -_        to -H*X×Y_
    ; _·_       to _cupX×Y_
    ; +Assoc    to +H*X×YAssoc
    ; +IdL      to +H*X×YIdL
    ; +IdR      to +H*X×YIdR
    ; +Comm     to +H*X×YComm
    ; ·Assoc    to ·H*X×YAssoc
    ; ·IdL      to ·H*X×YIdL
    ; ·IdR      to ·H*X×YIdR
    ; is-set    to isSetH*X×Y     )

  open RingStr (snd (H*R (X ⊎ Y))) using ()
    renaming
    ( 0r        to 0H*X⊎Y
    ; 1r        to 1H*X⊎Y
    ; _+_       to _+H*X⊎Y_
    ; -_        to -H*X⊎Y_
    ; _·_       to _cupX⊎Y_
    ; +Assoc    to +H*X⊎YAssoc
    ; +IdL      to +H*X⊎YIdL
    ; +IdR      to +H*X⊎YIdR
    ; +Comm     to +H*X⊎YComm
    ; ·Assoc    to ·H*X⊎YAssoc
    ; ·IdL      to ·H*X⊎YIdL
    ; ·IdR      to ·H*X⊎YIdR
    ; is-set    to isSetH*X⊎Y     )


-----------------------------------------------------------------------------
-- Notation needed for type checking
-- indeed several base coexists and two cannot be inferef without implicit argument
-- it is clearer to add a notation

  baseX : (n : ℕ) → (x : coHom n X) → H* X
  baseX n x = base n x

  baseY : (n : ℕ) → (x : coHom n Y) → H* Y
  baseY n x = base n x

-----------------------------------------------------------------------------
-- Direct Sens

  H*-X⊎Y→H*-X×H*-Y : H* (X ⊎ Y) → (H* X) × (H* Y)
  H*-X⊎Y→H*-X×H*-Y =
    DS-Rec-Set.f _ _ _ _
    isSetH*X×Y
    (0H*X , 0H*Y)
    (λ n a → (base n (fst (fun (fst Equiv-Coproduct-CoHom) a))) , (base n (snd (fun (fst Equiv-Coproduct-CoHom) a))))
    _+H*X×Y_
    +H*X×YAssoc
    +H*X×YIdR
    +H*X×YComm
    (λ n → ≡-× ((cong (λ A → baseX n (fst A)) (pres1 (snd Equiv-Coproduct-CoHom))) ∙ base-neutral n)
               (((cong (λ B → baseY n (snd B)) (pres1 (snd Equiv-Coproduct-CoHom))) ∙ base-neutral n)))
    λ n a b → sym (≡-× (cong (λ A → baseX n (fst A)) (pres· (snd Equiv-Coproduct-CoHom) a b)
                        ∙ cong (base n) (helper1 _ _ _)
                        ∙ sym (base-add n _ _))
                   (cong (λ B → baseY n (snd B)) (pres· (snd Equiv-Coproduct-CoHom) a b)
                        ∙ cong (base n) (helper2 _ _ _)
                        ∙ sym (base-add n _ _)))
      where
      helper1 : (n : ℕ) → (x y : coHom n X × coHom n Y)
                → fst ((DirProd (coHomGr n X) (coHomGr n Y) .snd GroupStr.· x) y) ≡ ((fst x) +ₕ (fst y))
      helper1 n (fst₁ , snd₁) (fst₂ , snd₂) = refl

      helper2 : (n : ℕ) → (x y : coHom n X × coHom n Y)
                → snd ((DirProd (coHomGr n X) (coHomGr n Y) .snd GroupStr.· x) y) ≡ ((snd x) +ₕ (snd y))
      helper2 n (fst₁ , snd₁) (fst₂ , snd₂) = refl

-----------------------------------------------------------------------------
-- Converse Sens

-- One need to convert seperatly the X an Y
-- Otherwise the traduction fails in the case base n a , 0
-- because one need then to lift x + 0 ≡ 0
-- which doesn't work because the + being lifted is on H*(Y) and not H*(X)×H*(Y)

  H*-X→H*-X⊎Y : H*(X) → H*(X ⊎ Y)
  H*-X→H*-X⊎Y = DS-Rec-Set.f _ _ _ _ isSetH*X⊎Y
       0H*X⊎Y
       (λ n a → base n (inv (fst Equiv-Coproduct-CoHom) (a , (0ₕ n))))
       _+H*X⊎Y_
       +H*X⊎YAssoc
       +H*X⊎YIdR
       +H*X⊎YComm
       (λ n → cong (base n) (pres1 (snd (invGroupIso Equiv-Coproduct-CoHom))) ∙ base-neutral n)
       λ n a a' → base-add _ _ _
                   ∙ cong (base n) (sym (pres· (snd (invGroupIso Equiv-Coproduct-CoHom)) _ _))
                   ∙ cong (base n) (cong (inv (fst Equiv-Coproduct-CoHom))
                                         (≡-× refl (AbGroupStr.+IdL (snd (coHomGroup n Y)) (0ₕ n))))

  H*-Y→H*-X⊎Y : H*(Y) → H*(X ⊎ Y)
  H*-Y→H*-X⊎Y = DS-Rec-Set.f _ _ _ _ isSetH*X⊎Y
       0H*X⊎Y
       (λ m b → base m (inv (fst Equiv-Coproduct-CoHom) (0ₕ m , b)))
       _+H*X⊎Y_
       +H*X⊎YAssoc
       +H*X⊎YIdR
       +H*X⊎YComm
       (λ m → cong (base m) (pres1 (snd (invGroupIso Equiv-Coproduct-CoHom))) ∙ base-neutral m)
       λ m b b' → base-add _ _ _
                   ∙ cong (base m) (sym (pres· (snd (invGroupIso Equiv-Coproduct-CoHom)) (0ₕ m , b) (0ₕ m , b')))
                   ∙ cong (base m) (cong (inv (fst Equiv-Coproduct-CoHom)) (≡-× (AbGroupStr.+IdL (snd (coHomGroup m X)) (0ₕ m)) refl))


  H*-X×H*-Y→H*-X⊎Y : H*(X) × H*(Y) → H*(X ⊎ Y)
  H*-X×H*-Y→H*-X⊎Y (x , y) = (H*-X→H*-X⊎Y x) +H*X⊎Y (H*-Y→H*-X⊎Y y)

  H*-X×H*-Y→H*-X⊎Y-pres+ : (x y : H*(X) × H*(Y)) → H*-X×H*-Y→H*-X⊎Y (x +H*X×Y y) ≡ ((H*-X×H*-Y→H*-X⊎Y x) +H*X⊎Y (H*-X×H*-Y→H*-X⊎Y y))
  H*-X×H*-Y→H*-X⊎Y-pres+ (x , y) (x' , y') = RingTheory.+ShufflePairs (H*R (X ⊎ Y)) _ _ _ _

-----------------------------------------------------------------------------
-- Section Sens

  e-sectX : (x : H* X) → H*-X⊎Y→H*-X×H*-Y (H*-X→H*-X⊎Y x) ≡ (x , 0H*Y)
  e-sectX = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X×Y _ _)
            refl
            (λ n a → ≡-× (cong (base n) (cong fst (rightInv (fst Equiv-Coproduct-CoHom) (a , 0ₕ n))))
                          (cong (base n) (cong snd (rightInv (fst Equiv-Coproduct-CoHom) (a , 0ₕ n))))
                     ∙ ≡-× refl (base-neutral n))
            λ {U V} ind-U ind-V → cong₂ _+H*X×Y_ ind-U ind-V ∙ ≡-× refl (+H*YIdR _)

  e-sectY : (y : H* Y) → (H*-X⊎Y→H*-X×H*-Y (H*-Y→H*-X⊎Y y)) ≡ (0H*X , y)
  e-sectY = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X×Y _ _)
            refl
            (λ m b → ≡-× (cong (base m) (cong fst (rightInv (fst Equiv-Coproduct-CoHom) (0ₕ m , b))))
                          (cong (base m) (cong snd (rightInv (fst Equiv-Coproduct-CoHom) (0ₕ m , b))))
                     ∙ ≡-× (base-neutral m) refl)
            λ {U V} ind-U ind-V → cong₂ _+H*X×Y_ ind-U ind-V ∙ ≡-× (+H*XIdR _) refl

  e-sect : (z : H*(X) × H*(Y)) → H*-X⊎Y→H*-X×H*-Y (H*-X×H*-Y→H*-X⊎Y z) ≡ z
  e-sect (x , y) = cong₂ _+H*X×Y_ (e-sectX x) (e-sectY y) ∙ ≡-× (+H*XIdR x) (+H*YIdL y)



-----------------------------------------------------------------------------
-- Retraction Sens

  e-retr : (x : H*(X ⊎ Y)) → H*-X×H*-Y→H*-X⊎Y (H*-X⊎Y→H*-X×H*-Y x) ≡ x
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X⊎Y _ _)
           (+H*X⊎YIdR _)
           (λ n a → ((base n (T⁻ ((fst (T a)) , 0ₕ n))) +H*X⊎Y (base n (T⁻ (0ₕ n , snd (T a)))))
                           ≡⟨ base-add n _ _ ⟩
                     base n ((T⁻ ((fst (T a)) , 0ₕ n)) +ₕ (T⁻ (0ₕ n , snd (T a))))
                           ≡⟨ cong (base n) (sym (pres· (snd (invGroupIso Equiv-Coproduct-CoHom)) ((fst (T a)) , 0ₕ n) (0ₕ n , snd (T a)))) ⟩
                     base n (T⁻ ( fst (T a) +ₕ 0ₕ n , 0ₕ n +ₕ snd (T a)))
                           ≡⟨ cong (base n) (cong T⁻ (≡-× (rUnitₕ n (fst (T a))) (lUnitₕ n (snd (T a))))) ⟩
                     base n (T⁻ ( fst (T a) , snd (T a)))
                           ≡⟨ cong (base n) (cong T⁻ (helper1 _ _ (T a))) ⟩
                     base n (T⁻ (T a))
                           ≡⟨ cong (base n) (leftInv (fst Equiv-Coproduct-CoHom) a) ⟩
                     base n a ∎)
           λ {U V} ind-U ind-V → (H*-X×H*-Y→H*-X⊎Y-pres+ _ _) ∙ (cong₂ _+H*X⊎Y_ ind-U ind-V)

           where
           T : {n : ℕ} → coHom n (X ⊎ Y) → coHom n X × coHom n Y
           T {n} = fun (fst (Equiv-Coproduct-CoHom))

           T⁻ : {n : ℕ} → coHom n X × coHom n Y → coHom n (X ⊎ Y)
           T⁻ {n} = inv (fst (Equiv-Coproduct-CoHom))

           helper1 : (A : Type ℓ) → (B : Type ℓ') → (x : A × B) → (fst x , snd x) ≡ x
           helper1 A B (fst₁ , snd₁) = refl

-----------------------------------------------------------------------------
-- Ring Equiv-Coproduct-CoHomphism

  H*-X⊎Y→H*-X×H*-Y-pres1 : H*-X⊎Y→H*-X×H*-Y 1H*X⊎Y ≡ (1H*X , 1H*Y)
  H*-X⊎Y→H*-X×H*-Y-pres1 = refl

  H*-X⊎Y→H*-X×H*-Y-pres+ : (x y : H* (X ⊎ Y)) →
                              H*-X⊎Y→H*-X×H*-Y ( x +H*X⊎Y y)
                            ≡ H*-X⊎Y→H*-X×H*-Y x +H*X×Y H*-X⊎Y→H*-X×H*-Y y
  H*-X⊎Y→H*-X×H*-Y-pres+ x y = refl

  H*-X⊎Y→H*-X×H*-Y-pres· : (x y : H* (X ⊎ Y)) →
                              H*-X⊎Y→H*-X×H*-Y ( x cupX⊎Y y)
                            ≡ H*-X⊎Y→H*-X×H*-Y x cupX×Y H*-X⊎Y→H*-X×H*-Y y
  H*-X⊎Y→H*-X×H*-Y-pres· = DS-Ind-Prop.f _ _ _ _ (λ x p q i y → isSetH*X×Y _ _ (p y) (q y) i)
         (λ y → refl)
         (λ n a → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X×Y _ _)
                   refl
                   (λ m b → (base (n +' m) (fst (T (a ⌣ b)))) , base (n +' m) (snd (T (a ⌣ b)))
                                  ≡⟨ ≡-× (cong (base (n +' m)) (helperX a b))
                                         (cong (base (n +' m)) (helperY a b)) ⟩
                             (base (n +' m) ((fst (T a)) ⌣ (fst (T b)))) , base (n +' m) ((snd (T a)) ⌣ (snd (T b))) ∎ )
                   λ {U V} ind-U ind-V → cong₂ _+H*X×Y_ ind-U ind-V)
         (λ {U V} ind-U ind-V y → cong₂ _+H*X×Y_ (ind-U y) (ind-V y))

         where
         T : {n : ℕ} → coHom n (X ⊎ Y) → coHom n X × coHom n Y
         T {n} = fun (fst (Equiv-Coproduct-CoHom))

         helperX : {n : ℕ} → {m : ℕ} → (a : coHom n (X ⊎ Y)) → (b : coHom m (X ⊎ Y))
                    → fst (T (a ⌣ b)) ≡ (fst (T a)) ⌣ (fst (T b))
         helperX = ST.elim (λ x → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i )
                   λ g → ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                   (λ h → refl)

         helperY : {n : ℕ} → {m : ℕ} → (a : coHom n (X ⊎ Y)) → (b : coHom m (X ⊎ Y))
                   → snd (T (a ⌣ b)) ≡ (snd (T a)) ⌣ (snd (T b))
         helperY = ST.elim (λ x → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i )
                   λ g → ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                   (λ h → refl)



-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _
  (X : Type ℓ)
  (Y : Type ℓ')
  where

  open Equiv-Coproduct-Properties
  open Iso
  open RingEquivs

  CohomologyRing-Coproduct : RingEquiv (H*R(X ⊎ Y)) (DirectProd-Ring (H*R X) (H*R Y))
  fst (CohomologyRing-Coproduct) = isoToEquiv is
    where
    is : Iso (H* (X ⊎ Y)) (H* X × H* Y)
    fun is = H*-X⊎Y→H*-X×H*-Y
    inv is = H*-X×H*-Y→H*-X⊎Y
    rightInv is = e-sect
    leftInv is = e-retr
  snd (CohomologyRing-Coproduct) = makeIsRingHom
                                   H*-X⊎Y→H*-X×H*-Y-pres1
                                   H*-X⊎Y→H*-X×H*-Y-pres+
                                   H*-X⊎Y→H*-X×H*-Y-pres·
