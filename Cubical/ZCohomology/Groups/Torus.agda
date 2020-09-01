{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Prelims
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Algebra.Group

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)

--------- H⁰(T²) ------------
H⁰-T²≅ℤ : GroupEquiv (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
H⁰-T²≅ℤ =
  H⁰-connected (north , north)
    λ (a , b) → pRec propTruncIsProp
                     (λ id1 → pRec propTruncIsProp
                                   (λ id2 → ∣ ΣPathP (id1 , id2) ∣₁)
                                   (Sn-connected 0 b) )
                     (Sn-connected 0 a)

------------------ H¹(T²) -------------------------------

H¹-T²≅ℤ×ℤ : GroupEquiv (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
H¹-T²≅ℤ×ℤ =
    groupequiv (isoToEquiv (setTruncIso (curryIso ⋄ codomainIso S1→K₁≡S1×Int ⋄ toProdIso)
                          ⋄ setTruncOfProdIso))
               (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                    λ f g → ΣPathP ((cong ∣_∣₂
                                     (funExt (λ x → helper (f (x , S¹→S1 base) +ₖ g (x , S¹→S1 base))
                                                   ∙ sym (cong₂ (λ x y → x +ₖ y)
                                                                (helper (f (x , S¹→S1 base)))
                                                                (helper (g (x , S¹→S1 base))))))) ,
                                   (cong ∣_∣₂
                                      (funExt
                                        (suspToPropRec
                                           north
                                           (λ _ → isSetInt _ _)
                                           (cong winding
                                                 (basechange-lemma2
                                                   (λ x → f (north , S¹→S1 x))
                                                   (λ x → g (north , S¹→S1 x))
                                                   λ x → S¹map (trMap S1→S¹ x))
                                          ∙∙ winding-hom
                                              (basechange2⁻
                                                  (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                                  (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i))))))
                                              (basechange2⁻
                                                  (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                                  (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i))))))
                                          ∙∙ sym (addLemma
                                                  (winding
                                                    (basechange2⁻
                                                      (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                                      (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i)))))))
                                                  (winding
                                                    (basechange2⁻
                                                      (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                                      (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i))))))))))))))
  □ dirProdEquiv (invGroupEquiv (Hⁿ-Sⁿ≅ℤ 0)) (H⁰-Sⁿ≅ℤ 0)

  where
  helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ S¹→S1 (S¹map (trMap S1→S¹ x)) ∣ ≡ x
  helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-retr a)

-------------------------------------------------------------


----------------------- H²(T²) ------------------------------
open import Cubical.Foundations.Equiv
H²-T²≅ℤ : GroupEquiv (coHomGr 2 (S₊ 1 × S₊ 1)) intGroup
H²-T²≅ℤ = invGroupEquiv ℤ≅H²-T²
  where
  ℤ≅H²-T² : GroupEquiv intGroup (coHomGr 2 (S₊ 1 × S₊ 1))
  GroupEquiv.eq ℤ≅H²-T² =
    compEquiv (isoToEquiv helper')
      (compEquiv (invEquiv (≃-× (GroupEquiv.eq H²-S¹≅0)
                                (invEquiv (GroupEquiv.eq (Hⁿ-Sⁿ≅ℤ 0)))))
                 (isoToEquiv
                    (invIso setTruncOfProdIso
                   ⋄ invIso (setTruncIso (curryIso
                                        ⋄ codomainIso S1→K2≡K2×K1
                                        ⋄ toProdIso)))))
    where
    helper' : Iso Int (Unit × Int)
    Iso.inv helper' = snd
    Iso.fun helper' x = tt , x
    Iso.leftInv helper' _ = refl
    Iso.rightInv helper' _ = refl

  GroupEquiv.isHom ℤ≅H²-T² a b =
      (λ i → f (GroupEquiv.isHom (invGroupEquiv (dirProdEquiv H²-S¹≅0 (invGroupEquiv (Hⁿ-Sⁿ≅ℤ 0)))) (_ , a) (_ , b) i))
    ∙ ((λ i → f (guyId i , (g a +ₕ g b)))
    ∙∙ helper (g a) (g b)
    ∙∙ (λ i → f (guyId2 (~ i) , g a) +ₕ f (guyId2 (~ i) , g b)))
    where
    f = Iso.fun (((invIso setTruncOfProdIso ⋄ invIso (setTruncIso (curryIso ⋄ codomainIso S1→K2≡K2×K1 ⋄ toProdIso)))))
    g = invEq (GroupEquiv.eq (invGroupEquiv (Hⁿ-Sⁿ≅ℤ 0)))

    isPropH²-S¹ : isProp (coHom 2 (S₊ 1))
    isPropH²-S¹ = transport (λ i → isProp (ua (GroupEquiv.eq H²-S¹≅0) (~ i))) isPropUnit

    guyId : ∣ _ ∣₂ ≡ 0ₕ
    guyId = isPropH²-S¹ _ _

    guyId2 : ∣ _ ∣₂ ≡ 0ₕ
    guyId2 = isPropH²-S¹ _ _

    helper : (x y : ∥ ((S₊ 1) → (hLevelTrunc 3 (S₊ 1) )) ∥₂) →
              f (0ₕ , x +ₕ y) ≡ f (0ₕ , x) +ₕ f (0ₕ , y)
    helper =
      sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
             λ f g i → ∣ (λ x → helper2 (f (fst x)) (g (fst x)) (snd x) i) ∣₂
      where
      helper2 : (x y : coHomK 1) (s : S₊ 1)
             → Iso.inv S1→K2≡K2×K1 (0ₖ , x +ₖ y) s ≡ (Iso.inv S1→K2≡K2×K1 (0ₖ , x)) s +ₖ (Iso.inv S1→K2≡K2×K1 (0ₖ , y)) s
      helper2 =
        trElim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 4 _ _)
               λ a b →
                λ {north → cong₂ (_+ₖ_) (sym (lUnitₖ 0ₖ)) (sym (lUnitₖ 0ₖ))
                ; south → cong₂ (_+ₖ_) (sym (lUnitₖ 0ₖ)) (sym (lUnitₖ 0ₖ))
                ; (merid south i) j →
                  hcomp (λ k → λ {(i = i0) → cong₂ (_+ₖ_) (sym (lUnitₖ 0ₖ)) (sym (lUnitₖ 0ₖ)) (j ∧ k)
                                 ; (i = i1) → cong₂ (_+ₖ_) (sym (lUnitₖ 0ₖ)) (sym (lUnitₖ 0ₖ)) (j ∧ k)
                                 ; (j = i0) → 0ₖ +ₖ Kn→ΩKn+1 1 (∣ a ∣ +ₖ ∣ b ∣) i
                                 ; (j = i1) →  cong₂ (_+ₖ_) (sym (lUnitₖ (Kn→ΩKn+1 1 ∣ a ∣ i))) (sym (lUnitₖ (Kn→ΩKn+1 1 ∣ b ∣ i))) k})
                        (helper3 ∣ a ∣ ∣ b ∣ j i)
                ; (merid north i) → cong₂ (_+ₖ_) (sym (lUnitₖ 0ₖ)) (sym (lUnitₖ 0ₖ)) }
        where
        helper3 : (a b : coHomK 1) → cong (0ₖ +ₖ_) (Kn→ΩKn+1 1 (a +ₖ b)) ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b)
        helper3 a b = (cong (cong (0ₖ +ₖ_)) helper4
                    ∙ congFunct (0ₖ +ₖ_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b))
                   ∙∙ cong (_∙ cong (0ₖ +ₖ_) (Kn→ΩKn+1 1 b)) (helper5 (Kn→ΩKn+1 1 a))
                   ∙∙ sym (cong₂Funct (_+ₖ_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b))
          where
          helper4 : Kn→ΩKn+1 1 (a +ₖ b) ≡ Kn→ΩKn+1 1 a ∙ Kn→ΩKn+1 1 b -- Termination issues unless this is put as a separate lemma...
          helper4 = +ₖ→∙ 1 a b

          helper6 : ∀{ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → p ≡ (refl ∙ refl) ∙ p ∙ refl ∙ refl
          helper6 p = (λ i → rUnit p i) ∙∙ (λ i → lUnit (p ∙ rUnit refl i) i) ∙∙ λ i → rUnit refl i ∙ p ∙ refl ∙ refl
          helper5 : (a : Path (coHomK 2) 0ₖ 0ₖ) → cong (0ₖ +ₖ_) a ≡ cong (_+ₖ 0ₖ) a
          helper5 a = (((helper6 (cong (0ₖ +ₖ_) a))
                   ∙∙ (λ i → ((λ j → lUnitₖ 0ₖ (i ∧ j)) ∙ refl) ∙ cong (λ x → lUnitₖ x i) a ∙ refl ∙ λ j → lUnitₖ 0ₖ (i ∧ (~ j)))
                   ∙∙ λ i → (lUnitₖ 0ₖ ∙ λ j → rUnitₖ 0ₖ ((~ i) ∨ (~ j))) ∙ cong (λ x → rUnitₖ x (~ i)) a ∙ (λ j → rUnitₖ 0ₖ (~ i ∨ j)) ∙ sym (lUnitₖ 0ₖ))
                   ∙∙ (λ i → (lUnitₖ 0ₖ ∙ sym (rUnitₖ 0ₖ)) ∙ isCommΩK-based 2 (0ₖ +ₖ 0ₖ) (cong (_+ₖ 0ₖ) a) (rUnitₖ 0ₖ ∙ sym (lUnitₖ 0ₖ)) i)
                   ∙∙ λ i → assoc (lUnitₖ 0ₖ ∙ sym (rUnitₖ 0ₖ)) (symDistr ((lUnitₖ 0ₖ)) (sym (rUnitₖ 0ₖ)) (~ i)) (cong (_+ₖ 0ₖ) a) i)
                   ∙∙ cong (_∙ (cong (_+ₖ 0ₖ) a)) (rCancel (lUnitₖ 0ₖ ∙ sym (rUnitₖ 0ₖ)))
                   ∙∙ sym (lUnit (cong (_+ₖ 0ₖ) a))
private
  to₂ : coHom 2 (S₊ 1 × S₊ 1) → Int
  to₂ = fst (GroupEquiv.eq H²-T²≅ℤ)

  from₂ : Int → coHom 2 (S₊ 1 × S₊ 1)
  from₂ = invEq (GroupEquiv.eq H²-T²≅ℤ)

  to₁ : coHom 1 (S₊ 1 × S₊ 1) → Int × Int
  to₁ = fst (GroupEquiv.eq H¹-T²≅ℤ×ℤ)

  from₁ : Int × Int → coHom 1 (S₊ 1 × S₊ 1)
  from₁ = invEq (GroupEquiv.eq H¹-T²≅ℤ×ℤ)

  to₀ : coHom 0 (S₊ 1 × S₊ 1) → Int
  to₀ = fst (GroupEquiv.eq H⁰-T²≅ℤ)

  from₀ : Int → coHom 0 (S₊ 1 × S₊ 1)
  from₀ = invEq (GroupEquiv.eq H⁰-T²≅ℤ)
