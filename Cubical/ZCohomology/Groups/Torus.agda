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
open import Cubical.HITs.S1 hiding (inv)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁) hiding (map)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)

open GroupHom
open GroupIso

congLemma2 : (n : ℕ) (p : Path (coHomK n) (0ₖ n) (0ₖ n))
          → Path (0ₖ n +[ n ]ₖ 0ₖ n ≡ 0ₖ n +[ n ]ₖ 0ₖ n)
                  (cong (λ x → 0ₖ n +[ n ]ₖ x) p) (cong (λ x → x +[ n ]ₖ 0ₖ n) p)
congLemma2 n p = congLemma (λ x y → x +[ n ]ₖ y) (λ x → -[ n ]ₖ x)
                           (0ₖ n)
                           (rUnitₖ n) (lUnitₖ n)
                           (rUnitlUnit0 n)
                           p

--------- H⁰(T²) ------------
H⁰-T²≅ℤ : GroupIso (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
H⁰-T²≅ℤ =
  H⁰-connected (north , north)
    λ (a , b) → pRec propTruncIsProp
                     (λ id1 → pRec propTruncIsProp
                                   (λ id2 → ∣ ΣPathP (id1 , id2) ∣₁)
                                   (Sn-connected 0 b) )
                     (Sn-connected 0 a)

------------------ H¹(T²) -------------------------------

H¹-T²≅ℤ×ℤ : GroupIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
H¹-T²≅ℤ×ℤ = theIso □ dirProdGroupIso (invGroupIso (Hⁿ-Sⁿ≅ℤ 0)) (H⁰-Sⁿ≅ℤ 0)
  where
  helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ S¹→S1 (S¹map (trMap S1→S¹ x)) ∣ ≡ x
  helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a i → ∣ (S1→S¹-retr a) i ∣

  typIso : Iso _ _
  typIso = setTruncIso (curryIso ⋄ codomainIso S1→K₁≡S1×Int ⋄ toProdIso)
                      ⋄ setTruncOfProdIso

  theIso : GroupIso _ _
  fun (map theIso) = Iso.fun (typIso)
  isHom (map theIso) = 
    sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
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
                                              (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i)))))))))))))
  inv theIso = Iso.inv typIso
  rightInv theIso = Iso.rightInv typIso
  leftInv theIso = Iso.leftInv typIso

-------------------------------------------------------------


----------------------- H²(T²) ------------------------------
open import Cubical.Foundations.Equiv
H²-T²≅ℤ : GroupIso (coHomGr 2 (S₊ 1 × S₊ 1)) intGroup
H²-T²≅ℤ = invGroupIso ℤ≅H²-T²
  where
  typIso : Iso _ _
  typIso = helper'
        ⋄ (invIso (prodIso (GroupIso→Iso H²-S¹≅0)
                           (invIso (GroupIso→Iso (Hⁿ-Sⁿ≅ℤ 0))))
        ⋄ ((invIso setTruncOfProdIso)
        ⋄ (invIso (setTruncIso (curryIso
                              ⋄ codomainIso S1→K2≡K2×K1
                              ⋄ toProdIso)))))
    where
    helper' : Iso Int (Unit × Int)
    Iso.inv helper' = snd
    Iso.fun helper' x = tt , x
    Iso.leftInv helper' _ = refl
    Iso.rightInv helper' _ = refl

  mapIsHom : isGroupHom intGroup (coHomGr 2 (S₊ 1 × S₊ 1)) (Iso.fun typIso)
  mapIsHom a b =
      (λ i → f (GroupHom.isHom (GroupIso.map (invGroupIso (dirProdGroupIso H²-S¹≅0 (invGroupIso (Hⁿ-Sⁿ≅ℤ 0))))) (_ , a) (_ , b) i))
    ∙ ((λ i → f (guyId i , (g a +ₕ g b)))
    ∙∙ helper (g a) (g b)
    ∙∙ (λ i → f (guyId2 (~ i) , g a) +ₕ f (guyId2 (~ i) , g b)))
    where
    f = Iso.fun (((invIso setTruncOfProdIso ⋄ invIso (setTruncIso (curryIso ⋄ codomainIso S1→K2≡K2×K1 ⋄ toProdIso)))))
    g = GroupIso.inv (invGroupIso (Hⁿ-Sⁿ≅ℤ 0))

    isPropH²-S¹ : isProp (coHom 2 (S₊ 1))
    isPropH²-S¹ = transport (λ i → isProp (isoToPath (GroupIso→Iso H²-S¹≅0) (~ i))) isPropUnit

    guyId : ∣ _ ∣₂ ≡ 0ₕ 2
    guyId = isPropH²-S¹ _ _

    guyId2 : ∣ _ ∣₂ ≡ 0ₕ 2
    guyId2 = isPropH²-S¹ _ _

    helper : (x y : ∥ ((S₊ 1) → (hLevelTrunc 3 (S₊ 1) )) ∥₂) →
              f ((0ₕ 2) , (x +ₕ y)) ≡ f ((0ₕ 2) , x) +ₕ f (0ₕ 2 , y)
    helper =
      sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
             λ f g i → ∣ (λ x → helper2 (f (fst x)) (g (fst x)) (snd x) i) ∣₂
      where
      helper2 : (x y : coHomK 1) (s : S₊ 1)
             → Iso.inv S1→K2≡K2×K1 (0ₖ 2 , x +ₖ y) s ≡ (Iso.inv S1→K2≡K2×K1 (0ₖ 2 , x)) s +ₖ (Iso.inv S1→K2≡K2×K1 (0ₖ 2 , y)) s
      helper2 =
        trElim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 4 _ _)
                λ a b → λ {north → cong₂ (_+ₖ_) (sym (lUnitₖ _ 0₂)) (sym (lUnitₖ _ 0₂))
                          ; south → cong₂ (_+ₖ_) (sym (lUnitₖ _ 0₂)) (sym (lUnitₖ _ 0₂))
                          ; (merid south i) j →
                            hcomp (λ k → λ { (i = i0) → cong₂ (_+ₖ_) (sym (lUnitₖ _ 0₂)) (sym (lUnitₖ _ 0₂)) (j ∧ k)
                                            ; (i = i1) → cong₂ (_+ₖ_) (sym (lUnitₖ _ 0₂)) (sym (lUnitₖ _ 0₂)) (j ∧ k)
                                            ; (j = i0) → 0₂ +ₖ Kn→ΩKn+1 1 (∣ a ∣ +ₖ ∣ b ∣) i
                                            ; (j = i1) →  cong₂ (_+ₖ_) (sym (lUnitₖ _ (Kn→ΩKn+1 1 ∣ a ∣ i)))
                                                                        (sym (lUnitₖ _ (Kn→ΩKn+1 1 ∣ b ∣ i))) k})
                                  (helper3 ∣ a ∣ ∣ b ∣ j i)
                          ; (merid north i) → cong₂ (_+ₖ_) (sym (lUnitₖ _ 0₂)) (sym (lUnitₖ _ 0₂))}
        where

        helper3 : (a b : coHomK 1) → cong (0₂ +ₖ_) (Kn→ΩKn+1 1 (a +ₖ b)) ≡ cong₂ (_+ₖ_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b)
        helper3 a b = cong (cong (0₂ +ₖ_)) helper4
                    ∙ (congFunct (0₂ +ₖ_) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b)
                    ∙∙ cong (_∙ cong (0₂ +ₖ_) (Kn→ΩKn+1 1 b)) (congLemma2 2 (Kn→ΩKn+1 1 a))
                    ∙∙ helper7)
          where
          helper7 : _
          helper7 = sym (cong₂Funct (λ x y → x +[ 2 ]ₖ y) (Kn→ΩKn+1 1 a) (Kn→ΩKn+1 1 b))

          helper4 : Kn→ΩKn+1 1 (a +ₖ b) ≡ Kn→ΩKn+1 1 a ∙ Kn→ΩKn+1 1 b
          helper4 = +ₖ→∙ 1 a b

  ℤ≅H²-T² : GroupIso intGroup (coHomGr 2 (S₊ 1 × S₊ 1))
  fun (map ℤ≅H²-T²) = Iso.fun typIso
  isHom (map ℤ≅H²-T²) = mapIsHom
  inv ℤ≅H²-T² = Iso.inv typIso
  rightInv ℤ≅H²-T² = Iso.rightInv typIso
  leftInv ℤ≅H²-T² = Iso.leftInv typIso

private
  to₂ : coHom 2 (S₊ 1 × S₊ 1) → Int
  to₂ = fun (map H²-T²≅ℤ)

  from₂ : Int → coHom 2 (S₊ 1 × S₊ 1)
  from₂ = inv H²-T²≅ℤ

  to₁ : coHom 1 (S₊ 1 × S₊ 1) → Int × Int
  to₁ = fun (map H¹-T²≅ℤ×ℤ)

  from₁ : Int × Int → coHom 1 (S₊ 1 × S₊ 1)
  from₁ = inv H¹-T²≅ℤ×ℤ

  to₀ : coHom 0 (S₊ 1 × S₊ 1) → Int
  to₀ = fun (map H⁰-T²≅ℤ)

  from₀ : Int → coHom 0 (S₊ 1 × S₊ 1)
  from₀ = inv H⁰-T²≅ℤ
