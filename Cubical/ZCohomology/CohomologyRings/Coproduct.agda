{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (elim to elim-sum ; rec to rec-sum)
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group hiding (Unit ; ℤ; Bool ; _/_ )
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetQuotients renaming (elimProp to elimProp-sq ; rec to rec-sq ; _/_ to _/sq_)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing

private variable
  ℓ ℓ' : Level

open Iso
open IsGroupHom
open GroupStr

module _
  (X : Type ℓ)
  (Y : Type ℓ')
  where

  open RingStr (snd (H*R X)) using ()
    renaming
    ( 0r        to 0H*X
    ; 1r        to 1H*X
    ; _+_       to _+H*X_
    ; -_        to -H*X_
    ; _·_       to _cupX_
    ; +Assoc    to +H*XAssoc
    ; +Identity to +H*XIdentity
    ; +Lid      to +H*XLid
    ; +Rid      to +H*XRid
    ; +Inv      to +H*XInv
    ; +Linv     to +H*XLinv
    ; +Rinv     to +H*XRinv
    ; +Comm     to +H*XComm
    ; ·Assoc    to ·H*XAssoc
    ; ·Identity to ·H*XIdentity
    ; ·Lid      to ·H*XLid
    ; ·Rid      to ·H*XRid
    ; ·Rdist+   to ·H*XRdist+
    ; ·Ldist+   to ·H*XLdist+
    ; is-set    to isSetH*X     )

  open RingStr (snd (H*R Y)) using ()
    renaming
    ( 0r        to 0H*Y
    ; 1r        to 1H*Y
    ; _+_       to _+H*Y_
    ; -_        to -H*Y_
    ; _·_       to _cupY_
    ; +Assoc    to +H*YAssoc
    ; +Identity to +H*YIdentity
    ; +Lid      to +H*YLid
    ; +Rid      to +H*YRid
    ; +Inv      to +H*YInv
    ; +Linv     to +H*YLinv
    ; +Rinv     to +H*YRinv
    ; +Comm     to +H*YComm
    ; ·Assoc    to ·H*YAssoc
    ; ·Identity to ·H*YIdentity
    ; ·Lid      to ·H*YLid
    ; ·Rid      to ·H*YRid
    ; ·Rdist+   to ·H*YRdist+
    ; ·Ldist+   to ·H*YLdist+
    ; is-set    to isSetH*Y     )

  open RingStr (snd (DirectProd-Ring (H*R X) (H*R Y))) using ()
    renaming
    ( 0r        to 0H*X×Y
    ; 1r        to 1H*X×Y
    ; _+_       to _+H*X×Y_
    ; -_        to -H*X×Y_
    ; _·_       to _cupX×Y_
    ; +Assoc    to +H*X×YAssoc
    ; +Identity to +H*X×YIdentity
    ; +Lid      to +H*X×YLid
    ; +Rid      to +H*X×YRid
    ; +Inv      to +H*X×YInv
    ; +Linv     to +H*X×YLinv
    ; +Rinv     to +H*X×YRinv
    ; +Comm     to +H*X×YComm
    ; ·Assoc    to ·H*X×YAssoc
    ; ·Identity to ·H*X×YIdentity
    ; ·Lid      to ·H*X×YLid
    ; ·Rid      to ·H*X×YRid
    ; ·Rdist+   to ·H*X×YRdist+
    ; ·Ldist+   to ·H*X×YLdist+
    ; is-set    to isSetH*X×Y     )

  open RingStr (snd (H*R (X ⊎ Y))) using ()
    renaming
    ( 0r        to 0H*X⊎Y
    ; 1r        to 1H*X⊎Y
    ; _+_       to _+H*X⊎Y_
    ; -_        to -H*X⊎Y_
    ; _·_       to _cupX⊎Y_
    ; +Assoc    to +H*X⊎YAssoc
    ; +Identity to +H*X⊎YIdentity
    ; +Lid      to +H*X⊎YLid
    ; +Rid      to +H*X⊎YRid
    ; +Inv      to +H*X⊎YInv
    ; +Linv     to +H*X⊎YLinv
    ; +Rinv     to +H*X⊎YRinv
    ; +Comm     to +H*X⊎YComm
    ; ·Assoc    to ·H*X⊎YAssoc
    ; ·Identity to ·H*X⊎YIdentity
    ; ·Lid      to ·H*X⊎YLid
    ; ·Rid      to ·H*X⊎YRid
    ; ·Rdist+   to ·H*X⊎YRdist+
    ; ·Ldist+   to ·H*X⊎YLdist+
    ; is-set    to isSetH*X⊎Y     )


-----------------------------------------------------------------------------
-- On Cohomology Groups

  mor : {n : ℕ} → GroupIso (coHomGr n (X ⊎ Y)) (DirProd (coHomGr n X) (coHomGr n Y))
  Iso.fun (fst mor)      = sRec (isSet× squash₂ squash₂) (λ f → ∣ f ∘ inl ∣₂ , ∣ (f ∘ inr) ∣₂)
  Iso.inv (fst mor)      = uncurry
                           (sRec (λ u v p q i j y → squash₂ (u y) (v y) (λ X → p X y) (λ X → q X y) i j)
                           (λ g → sRec squash₂ (λ h → ∣ rec-sum g h ∣₂)))
  Iso.rightInv (fst mor) = uncurry
                           (sElim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                           (λ g → sElim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                                   (λ h → refl)))
  Iso.leftInv (fst mor) = sElim (λ _ → isProp→isSet (squash₂ _ _))
                          λ f → cong ∣_∣₂ (funExt (elim-sum (λ x → refl) (λ x → refl)))
  snd mor =               makeIsGroupHom
                          (sElim (λ x → isProp→isSet λ u v i y → isSet× squash₂ squash₂ _ _ (u y) (v y) i)
                          (λ g → sElim (λ _ → isProp→isSet (isSet× squash₂ squash₂ _ _))
                          λ h → refl))

-----------------------------------------------------------------------------
-- Notation ?

  _+×_ : H*(X) × H*(Y) → H*(X) × H*(Y) → H*(X) × H*(Y)
  _+×_ x y = ((snd (DirectProd-Ring (H*R X) (H*R Y))) RingStr.+ x) y

  baseX : (n : ℕ) → (x : coHom n X) → H* X
  baseX n x = base n x

  base-neutralX : (n : ℕ) → baseX n (0ₕ n) ≡ 0H*X
  base-neutralX n = base-neutral n

  base-addX : (n : ℕ) → (a b : coHom n X) → baseX n a +H*X baseX n b ≡ baseX n (a +ₕ b)
  base-addX n a b = base-add n a b

  baseY : (n : ℕ) → (x : coHom n Y) → H* Y
  baseY n x = base n x

  base-neutralY : (n : ℕ) → baseY n (0ₕ n) ≡ 0H*Y
  base-neutralY n = base-neutral n

  base-addY : (n : ℕ) → (a b : coHom n Y) → baseY n a +H*Y baseY n b ≡ baseY n (a +ₕ b)
  base-addY n a b = base-add n a b

  baseX⊎Y : (n : ℕ) → (x : coHom n (X ⊎ Y)) → H* (X ⊎ Y)
  baseX⊎Y n x = base n x

  base-neutralX⊎Y : (n : ℕ) → baseX⊎Y n (0ₕ n) ≡ 0H*X⊎Y
  base-neutralX⊎Y n = base-neutral n

  base-addX⊎Y : (n : ℕ) → (a b : coHom n (X ⊎ Y)) → baseX⊎Y n a +H*X⊎Y baseX⊎Y n b ≡ baseX⊎Y n (a +ₕ b)
  base-addX⊎Y n a b = base-add n a b


-----------------------------------------------------------------------------
-- Direct Sens

  H*-X⊎Y→H*-X×H*-Y : H* (X ⊎ Y) → (H* X) × (H* Y)
  H*-X⊎Y→H*-X×H*-Y =
    DS-Rec-Set.f _ _ _ _
    (isSet× isSetH*X isSetH*Y)
    (0H*X , 0H*Y)
    (λ n a → (base n (fst (fun (fst mor) a))) , (base n (snd (fun (fst mor) a))))
    _+H*X×Y_
    +H*X×YAssoc
    +H*X×YRid
    +H*X×YComm
    (λ n → ≡-× ((cong (λ A → baseX n (fst A)) (pres1 (snd mor))) ∙ base-neutral n)
               (((cong (λ B → baseY n (snd B)) (pres1 (snd mor))) ∙ base-neutral n)))
    λ n a b → sym (≡-× (cong (λ A → baseX n (fst A)) (pres· (snd mor) a b)
                        ∙ cong (base n) (helper1 _ _ _)
                        ∙ sym (base-add n _ _))
                   (cong (λ B → baseY n (snd B)) (pres· (snd mor) a b)
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
-- Otherwise

-- 0       , 0        -> 0
-- 0       , base m b -> base m (inv (0 , b)
-- base n a, 0        -> base n (inv (a, 0))
-- base n a, base m b -> base n (inv (a, 0)) + base m (inv (0, b))
-- + by + ?

  H*-X→H*-X⊎Y : H*(X) → H*(X ⊎ Y)
  H*-X→H*-X⊎Y = DS-Rec-Set.f _ _ _ _ isSetH*X⊎Y
       0H*X⊎Y
       (λ n a → base n (inv (fst mor) (a , (0ₕ n))))
       _+H*X⊎Y_
       +H*X⊎YAssoc
       +H*X⊎YRid
       +H*X⊎YComm
       (λ n → cong (base n) (pres1 (snd (invGroupIso mor))) ∙ base-neutral n)
       λ n a a' → base-add _ _ _
                   ∙ cong (base n) (sym (pres· (snd (invGroupIso mor)) _ _))
                   ∙ cong (base n) (cong (inv (fst mor)) (≡-× refl (AbGroupStr.lid (snd (coHomGroup n Y)) (0ₕ n))))

  H*-Y→H*-X⊎Y : H*(Y) → H*(X ⊎ Y)
  H*-Y→H*-X⊎Y = DS-Rec-Set.f _ _ _ _ isSetH*X⊎Y
       0H*X⊎Y
       (λ m b → base m (inv (fst mor) (0ₕ m , b)))
       _+H*X⊎Y_
       +H*X⊎YAssoc
       +H*X⊎YRid
       +H*X⊎YComm
       (λ m → cong (base m) (pres1 (snd (invGroupIso mor))) ∙ base-neutral m)
       λ m b b' → base-add _ _ _
                   ∙ cong (base m) (sym (pres· (snd (invGroupIso mor)) (0ₕ m , b) (0ₕ m , b')))
                   ∙ cong (base m) (cong (inv (fst mor)) (≡-× (AbGroupStr.lid (snd (coHomGroup m X)) (0ₕ m)) refl))


  H*-X×H*-Y→H*-X⊎Y : H*(X) × H*(Y) → H*(X ⊎ Y)
  H*-X×H*-Y→H*-X⊎Y (x , y) = (H*-X→H*-X⊎Y x) +H*X⊎Y (H*-Y→H*-X⊎Y y)

  H*-X×H*-Y→H*-X⊎Y-gmorph : (x y : H*(X) × H*(Y)) → H*-X×H*-Y→H*-X⊎Y (x +× y) ≡ ((H*-X×H*-Y→H*-X⊎Y x) +H*X⊎Y (H*-X×H*-Y→H*-X⊎Y y))
  H*-X×H*-Y→H*-X⊎Y-gmorph (x , y) (x' , y') = RingTheory.+ShufflePairs (H*R (X ⊎ Y)) _ _ _ _

-----------------------------------------------------------------------------
-- Section Sens

  e-sectX : (x : H* X) → H*-X⊎Y→H*-X×H*-Y (H*-X→H*-X⊎Y x) ≡ (x , 0H*Y)
  e-sectX = DS-Ind-Prop.f _ _ _ _ (λ _ → isSet× isSetH*X isSetH*Y _ _)
            refl
            (λ n a → ≡-× (cong (base n) (cong fst (rightInv (fst mor) (a , 0ₕ n))))
                          (cong (base n) (cong snd (rightInv (fst mor) (a , 0ₕ n))))
                     ∙ ≡-× refl (base-neutral n))
            λ {U V} ind-U ind-V → cong₂ _+×_ ind-U ind-V ∙ ≡-× refl (+H*YRid _)

  e-sectY : (y : H* Y) → (H*-X⊎Y→H*-X×H*-Y (H*-Y→H*-X⊎Y y)) ≡ (0H*X , y)
  e-sectY = DS-Ind-Prop.f _ _ _ _ (λ _ → isSet× isSetH*X isSetH*Y _ _)
            refl
            (λ m b → ≡-× (cong (base m) (cong fst (rightInv (fst mor) (0ₕ m , b))))
                          (cong (base m) (cong snd (rightInv (fst mor) (0ₕ m , b))))
                     ∙ ≡-× (base-neutral m) refl)
            λ {U V} ind-U ind-V → cong₂ _+×_ ind-U ind-V ∙ ≡-× (+H*XRid _) refl

  e-sect : (z : H*(X) × H*(Y)) → H*-X⊎Y→H*-X×H*-Y (H*-X×H*-Y→H*-X⊎Y z) ≡ z
  e-sect (x , y) = cong₂ _+×_ (e-sectX x) (e-sectY y) ∙ ≡-× (+H*XRid x) (+H*YLid y)



-----------------------------------------------------------------------------
-- Retraction Sens

  e-retr : (x : H*(X ⊎ Y)) → H*-X×H*-Y→H*-X⊎Y (H*-X⊎Y→H*-X×H*-Y x) ≡ x
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X⊎Y _ _)
           (+H*X⊎YRid _)
           (λ n a → ((base n (T⁻ ((fst (T a)) , 0ₕ n))) +H*X⊎Y (base n (T⁻ (0ₕ n , snd (T a)))))
                           ≡⟨ base-add n _ _ ⟩
                     base n ((T⁻ ((fst (T a)) , 0ₕ n)) +ₕ (T⁻ (0ₕ n , snd (T a))))
                           ≡⟨ cong (base n) (sym (pres· (snd (invGroupIso mor)) ((fst (T a)) , 0ₕ n) (0ₕ n , snd (T a)))) ⟩
                     base n (T⁻ ( fst (T a) +ₕ 0ₕ n , 0ₕ n +ₕ snd (T a)))
                           ≡⟨ cong (base n) (cong T⁻ (≡-× (rUnitₕ n (fst (T a))) (lUnitₕ n (snd (T a))))) ⟩
                     base n (T⁻ ( fst (T a) , snd (T a)))
                           ≡⟨ cong (base n) (cong T⁻ (helper1 _ _ (T a))) ⟩
                     base n (T⁻ (T a))
                           ≡⟨ cong (base n) (leftInv (fst mor) a) ⟩
                     base n a ∎)
           λ {U V} ind-U ind-V → (H*-X×H*-Y→H*-X⊎Y-gmorph _ _) ∙ (cong₂ _+H*X⊎Y_ ind-U ind-V)

           where
           T : {n : ℕ} → coHom n (X ⊎ Y) → coHom n X × coHom n Y
           T {n} = fun (fst (mor {n}))

           T⁻ : {n : ℕ} → coHom n X × coHom n Y → coHom n (X ⊎ Y)
           T⁻ {n} = inv (fst (mor {n}))

           helper1 : (A : Type ℓ) → (B : Type ℓ') → (x : A × B) → (fst x , snd x) ≡ x
           helper1 A B (fst₁ , snd₁) = refl

-----------------------------------------------------------------------------
-- Ring morphism

  map1 : H*-X⊎Y→H*-X×H*-Y 1H*X⊎Y ≡ (1H*X , 1H*Y)
  map1 = refl

  map+ : (x y : H* (X ⊎ Y)) → H*-X⊎Y→H*-X×H*-Y ( x +H*X⊎Y y) ≡ H*-X⊎Y→H*-X×H*-Y x +H*X×Y H*-X⊎Y→H*-X×H*-Y y
  map+ x y = refl

  map· : (x y : H* (X ⊎ Y)) → H*-X⊎Y→H*-X×H*-Y ( x cupX⊎Y y) ≡ H*-X⊎Y→H*-X×H*-Y x cupX×Y H*-X⊎Y→H*-X×H*-Y y
  map· = DS-Ind-Prop.f _ _ _ _ (λ x p q i y → isSetH*X×Y _ _ (p y) (q y) i)
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
         T {n} = fun (fst (mor {n}))

         helperX : {n : ℕ} → {m : ℕ} → (a : coHom n (X ⊎ Y)) → (b : coHom m (X ⊎ Y))
                    → fst (T (a ⌣ b)) ≡ (fst (T a)) ⌣ (fst (T b))
         helperX = sElim (λ x → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i )
                   λ g → sElim (λ _ → isProp→isSet (squash₂ _ _))
                   (λ h → refl)

         helperY : {n : ℕ} → {m : ℕ} → (a : coHom n (X ⊎ Y)) → (b : coHom m (X ⊎ Y))
                   → snd (T (a ⌣ b)) ≡ (snd (T a)) ⌣ (snd (T b))
         helperY = sElim (λ x → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i )
                   λ g → sElim (λ _ → isProp→isSet (squash₂ _ _))
                   (λ h → refl)
