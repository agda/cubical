{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.S1.S1
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; rec to trRec2 ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.GroupLibrary
open import Cubical.ZCohomology.coHomZero-map
open import Cubical.HITs.Wedge

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)


-- H⁰(T²)
coHom0Torus : grIso (coHomGr 0 (S₊ 1 × S₊ 1)) intGroup
coHom0Torus =
  Iso'→Iso
    (iso'
      (iso (sRec isSetInt (λ f → f (north , north)))
           (λ a → ∣ (λ x → a) ∣₀)
           (λ a → refl)
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → cong ∣_∣₀
                      (funExt λ {(x , y) → suspToPropRec2
                                              {B = λ x y → f (north , north) ≡ f (x , y)}
                                              north
                                              (λ _ _ → isSetInt _ _)
                                              refl
                                              x y})))
      (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
              λ a b → addLemma (a (north , north)) (b (north , north))))



------------------ H¹(T²) -------------------------------

-- We first need the following technical lemma
basechange-lemma2 : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹)
                 → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                  ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                  ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
basechange-lemma2 f g F = coInd f g F (f base) (g base) refl refl
  where
  coInd : (f g : S¹ → hLevelTrunc 3 (S₊ 1)) (F : hLevelTrunc 3 (S₊ 1) → S¹) (x y : hLevelTrunc 3 (S₊ 1))
                   → f base ≡ x
                   → g base ≡ y
                   → ((basechange2⁻ (F (f base +ₖ g base)) λ i → F ((f (loop i)) +ₖ g (loop i)))
                    ≡ basechange2⁻ (F (f base)) (cong (F ∘ f) loop)
                    ∙ basechange2⁻ (F (g base)) (cong (F ∘ g) loop))
  coInd f g F =
    elim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isGroupoidS¹ base base)) _ _ )
          (suspToPropRec2
            north
            (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → isGroupoidS¹ _ _ _ _)
            λ fid gid →
                (λ i → basechange2⁻ (F (f base +ₖ g base)) (cong₂Funct (λ x y → F (f x +ₖ g y)) loop loop i))
              ∙ (basechange2⁻-morph (F (f base +ₖ g base))
                                    (cong (λ x → F (f x +ₖ g base)) loop)
                                    (cong (λ x → F (f base +ₖ g x)) loop))
              ∙ (λ i → basechange2⁻ (F (f base +ₖ gid i)) (cong (λ x → F (f x +ₖ gid i)) loop)
                      ∙ basechange2⁻ (F (fid i +ₖ g base)) (cong (λ x → F (fid i +ₖ g x)) loop))
              ∙ (λ i → basechange2⁻ (F (rUnitₖ (f base) i)) (cong (λ x → F (rUnitₖ (f x) i)) loop)
                      ∙ basechange2⁻ (F (lUnitₖ (g base) i)) (cong (λ x → F (lUnitₖ (g x) i)) loop)))
  


coHom1Torus : grIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (dirProd intGroup intGroup)
coHom1Torus =
  compGrIso
    (Iso'→Iso
      (iso' (compIso
                (setTruncIso (compIso
                               schönfinkelIso
                               (compIso
                                 (codomainIso S1→S1→S1×Int)
                                 toProdIso)))
                (setTruncOfProdIso))
                (sElim2
                    (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                    λ f g → ×≡ (cong ∣_∣₀
                                     (funExt (λ x → helper (f (x , S¹→S1 base) +ₖ g (x , S¹→S1 base))
                                                   ∙ sym (cong₂ (λ x y → x +ₖ y)
                                                                (helper (f (x , S¹→S1 base)))
                                                                (helper (g (x , S¹→S1 base)))))))
                                (cong ∣_∣₀
                                   (funExt
                                     (suspToPropRec
                                        north
                                        (λ _ → isSetInt _ _)
                                        (cong winding
                                              (basechange-lemma2
                                                (λ x → f (north , S¹→S1 x))
                                                (λ x → g (north , S¹→S1 x))
                                                λ x → S¹map (trMap S1→S¹ x))
                                       ∙ winding-hom
                                           (basechange2⁻
                                               (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                               (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i))))))
                                           (basechange2⁻
                                               (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                               (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i))))))
                                       ∙ sym (addLemma
                                               (winding
                                                 (basechange2⁻
                                                   (S¹map (trMap S1→S¹ (f (north , S¹→S1 base))))
                                                   (λ i → S¹map (trMap S1→S¹ (f (north , S¹→S1 (loop i)))))))
                                               (winding
                                                 (basechange2⁻
                                                   (S¹map (trMap S1→S¹ (g (north , S¹→S1 base))))
                                                   (λ i → S¹map (trMap S1→S¹ (g (north , S¹→S1 (loop i)))))))))))))))
    (dirProdIso (invGrIso (coHom-n-Sn 0)) (invGrIso H⁰-S¹≅ℤ))

  where
  helper : (x : hLevelTrunc 3 (S₊ 1)) → ∣ S¹→S1 (S¹map (trMap S1→S¹ x)) ∣ ≡ x
  helper = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ a → cong ∣_∣ (S1→S¹-retr a)

-------------------------------------------------------------


----------------------- H²(T²) ------------------------------

H²-T²≡ℤ : Iso Int (coHom 2 (S₊ 1 × S₊ 1))
H²-T²≡ℤ =
    compIso
          helper'
          (compIso
            (symIso (prodIso (groupIso→Iso H²-S¹≅0)
                             (groupIso→Iso (invGrIso (coHom-n-Sn 0)))))
            (compIso
              (symIso setTruncOfProdIso)
              (symIso
                (setTruncIso
                  (compIso
                    schönfinkelIso
                    (compIso
                      (codomainIso S1→K2≡K2×K1)
                      toProdIso))))))
  where
  helper' : Iso Int (Unit × Int)
  Iso.inv helper' = proj₂
  Iso.fun helper' x = tt , x
  Iso.leftInv helper' x = refl
  Iso.rightInv helper' x = ×≡ refl refl

{-

coHom2Torus : grIso (coHomGr 2 ((S₊ 1) × (S₊ 1))) intGroup
coHom2Torus =
  invGrIso
    (Iso'→Iso
      (iso'
        H²-T²≡ℤ
        λ a b → {!!} {- (λ i → Iso.fun
                             (symIso
                              (setTruncIso
                               (compIso schönfinkelIso (compIso (codomainIso test13) toProdIso))))
                             (Iso.fun (symIso setTruncOfProdIso)
                              (helper'' (Iso.inv (groupIso→Iso coHom2-S1) tt) 0ₕ i , morph.ismorph (grIso.inv (invGrIso coHom1S1)) a b i)))
               ∙ (λ i → Iso.fun
                             (symIso
                              (setTruncIso
                               (compIso schönfinkelIso (compIso (codomainIso test13) toProdIso))))
                               ∣ (λ _ → ∣ north ∣) , {!!} ∣₀)
               ∙ {!toProdIso!} -}))

-}

{-
  where
  helper'' : isProp ∥ (S₊ 1 → hLevelTrunc 4 (S₊ 2)) ∥₀
  helper'' = {!!}

  helper2' : (f g : (S₊ 1 → hLevelTrunc 3 (S₊ 1))) →
                Path (coHom 2 ((S₊ 1) × (S₊ 1))) (Iso.fun
                (symIso
                 (setTruncIso
                  (compIso schönfinkelIso (compIso (codomainIso S1→K2≡K2×K1) toProdIso))))
                (Iso.fun (symIso setTruncOfProdIso) (0ₕ , ∣ f ∣₀ +ₕ ∣ g ∣₀)))
                (Iso.fun (symIso
                 (setTruncIso
                  (compIso schönfinkelIso (compIso (codomainIso S1→K2≡K2×K1) toProdIso))))
                (Iso.fun (symIso setTruncOfProdIso) (0ₕ , ∣ f ∣₀)) +ₕ Iso.fun (symIso
                 (setTruncIso
                  (compIso schönfinkelIso (compIso (codomainIso S1→K2≡K2×K1) toProdIso))))
                (Iso.fun (symIso setTruncOfProdIso) (0ₕ , ∣ g ∣₀)))
  helper2' f g = (λ i → Iso.fun (symIso
                 (setTruncIso
                  (compIso schönfinkelIso ((codomainIso S1→K2≡K2×K1))))) ∣ (λ x → 0ₖ , (f x +ₖ g x)) ∣₀)
               ∙ (λ i →  ∣ Iso.fun (symIso (compIso schönfinkelIso (codomainIso S1→K2≡K2×K1))) (λ x → 0ₖ , (f x +ₖ g x)) ∣₀)
               ∙ (λ i → ∣ Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , (f x +ₖ g x)))) ∣₀)
               ∙ (λ i → ∣ {!!} ∣₀)
               ∙ {!!}
               ∙ {!!}
    where
    fun : S₊ 1 × S₊ 1 → hLevelTrunc 4 (S₊ 2)
    fun (x , north) = 0ₖ +ₖ 0ₖ
    fun (x , south) = 0ₖ +ₖ 0ₖ
    fun (x , (merid south i)) = 0ₖ +ₖ (Kn→ΩKn+1 1 (f x +ₖ g x) i)
    fun (x , (merid north i)) = 0ₖ +ₖ 0ₖ

    helper : Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , (f x +ₖ g x)))) ≡ fun
    helper = funExt λ {(x , north) → refl ; (x , south) → refl ; (x , (merid north i)) → refl ; (x , (merid south i)) → refl}

    helper2 : ∣ Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , (f x +ₖ g x)))) ∣₀
            ≡ (∣ Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , f x))) ∣₀ +ₕ ∣ Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , g x))) ∣₀)
    helper2 =
      cong ∣_∣₀
           (funExt λ {(x , north) → ((λ i → (∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x +ₖ g x) i))
                                            ∙∙ sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ cong (λ x → ((0ₖ +ₖ 0ₖ) +ₖ x)) (rUnitₖ 0ₖ) 
                                            ∙∙ refl)
                    ; (x , south) → refl
                                            ∙∙ sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ cong (λ x → ((0ₖ +ₖ 0ₖ) +ₖ x)) (rUnitₖ 0ₖ) 
                                            ∙∙ (λ i → (∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x) i) +ₖ ∣ north ∣ +ₖ Kn→ΩKn+1 1 (g x) i)
                    ; (x , (merid south i)) j → hcomp (λ k → λ {(j = i0) → ∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x +ₖ g x) (i ∨ (~ k))
                                                                ; (j = i1) → (∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x) (i ∧ k)) +ₖ ∣ north ∣ +ₖ Kn→ΩKn+1 1 (g x) (i ∧ k)})
                                                                 ((sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ cong (λ x → ((0ₖ +ₖ 0ₖ) +ₖ x)) (rUnitₖ 0ₖ)) j)
                    ; (x , (merid north u)) → {!!}})
      where
      anotherone : (x : _) → cong (0ₖ +ₖ_) (Kn→ΩKn+1 1 (f x +ₖ g x)) ≡ {!!}
      anotherone x = {!!}

      helper5 : (x : _) → Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , f x +ₖ g x))) x
                        ≡ (Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , f x))) x) +ₖ (Iso.inv schönfinkelIso (Iso.inv (codomainIso S1→K2≡K2×K1) ((λ x → 0ₖ , g x))) x)
      helper5 (x , north) = sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i)))
      helper5 (x , south) = sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i)))
      helper5 (x , merid north i) = sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i)))
      helper5 (x , merid south i) j =
        {!!}
        where
        helper13 : sym (sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i))))
                ∙ (λ i → ∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x +ₖ g x) i) ∙ (sym (rUnitₖ (0ₖ +ₖ 0ₖ))
                ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i))))
                ≡ λ i → (∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x) i) +ₖ
         ∣ north ∣ +ₖ Kn→ΩKn+1 1 (g x) i
        helper13 = (λ j → sym ((λ i → (rUnitₖ (lUnitₖ 0ₖ (j ∧ (~ i))) (~ i))) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ lUnitₖ 0ₖ (~ i)))
                              ∙ lUnit (rUnit ((λ i → lUnitₖ (Kn→ΩKn+1 1 (f x +ₖ g x) i) j)) j) j
                              ∙ ((λ i → (rUnitₖ (lUnitₖ 0ₖ (j ∧ (~ i))) (~ i)))) ∙ λ i → (0ₖ +ₖ 0ₖ) +ₖ lUnitₖ 0ₖ (~ i))
                 ∙ (λ j → sym ((λ i → (rUnitₖ (lUnitₖ 0ₖ (~ i)) (~ i))) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ lUnitₖ 0ₖ (~ i))) ∙
                           {!!} ∙
                           (λ i → (rUnitₖ (lUnitₖ 0ₖ (~ i)) (~ i))) ∙ λ i → (0ₖ +ₖ 0ₖ) +ₖ lUnitₖ 0ₖ (~ i))
                 ∙ {!!}
                 ∙ {!!}
{-
i = i0 ⊢ (sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i)))) j 
i = i1 ⊢ (sym (rUnitₖ (0ₖ +ₖ 0ₖ)) ∙ (λ i → (0ₖ +ₖ 0ₖ) +ₖ (lUnitₖ 0ₖ (~ i)))) j 
j = i0 ⊢ ∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x +ₖ g x) i
j = i1 ⊢ (∣ north ∣ +ₖ Kn→ΩKn+1 1 (f x) i) +ₖ
         ∣ north ∣ +ₖ Kn→ΩKn+1 1 (g x) i
-}


  helper' : Iso Int (Unit × Int)
  Iso.inv helper' = proj₂
  Iso.fun helper' x = tt , x
  Iso.leftInv helper' x = refl
  Iso.rightInv helper' x = ×≡ refl refl

  helper : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → Iso C Unit → Iso A B → Iso (A × C) B 
  Iso.fun (helper cUnit iAB) x = Iso.fun iAB (proj₁ x)
  Iso.inv (helper cUnit iAB) x = (Iso.inv iAB x) , (Iso.inv cUnit tt )
  Iso.rightInv (helper cUnit iAB) = Iso.rightInv iAB
  Iso.leftInv (helper cUnit iAB) b = ×≡ (Iso.leftInv iAB (proj₁ b)) (Iso.leftInv cUnit (proj₂ b))

  helper2 : Iso (coHom 2 ((S₊ 1) × (S₊ 1))) (coHom 2 ((S₊ 1) × hLevelTrunc 3 (S₊ 1)))
  Iso.fun helper2 = sRec setTruncIsSet (λ f → ∣ (λ {(x , y) → f (x , trRec isGroupoidS1 (idfun (S₊ 1)) y)}) ∣₀) 
  Iso.inv helper2 = sRec setTruncIsSet (λ f → ∣ (λ {(x , y) → f (x , ∣ y ∣)}) ∣₀)
  Iso.rightInv helper2 =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
             (λ f → cong ∣_∣₀
                          (funExt λ {(x , y) →
                              trElim {B = λ y → f (x , ∣ trRec isGroupoidS1 (λ x₁ → x₁) y ∣) ≡ f (x , y)}
                                     (λ _ → isOfHLevelPath' 3 (isOfHLevelTrunc 4) _ _)
                                     (λ a → refl) y}))
  Iso.leftInv helper2 =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                 λ f → cong ∣_∣₀ (funExt λ {(x , y) → refl})
-}
