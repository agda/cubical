{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.Properties



H⁰-Sⁿ≅ℤ : (n : ℕ) → grIso (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ n =
  Iso'''→Iso
    (iso'''
      (mph (sRec isSetInt λ f → f north) (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ f g → addLemma (f north) (g north)))
      (λ a → ∣ (λ _ → a) ∣₀)
      (λ _ → refl)
      (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → cong ∣_∣₀ (funExt (suspToPropRec north (λ _ → isSetInt _ _) refl))))


----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.
coHomPushout≅coHomSn : (n m : ℕ) → grIso (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
morph.fun (grIso.fun (coHomPushout≅coHomSn n m)) =
  sRec setTruncIsSet
       λ f → ∣ (λ {(inl x) → f north
                 ; (inr x) → f south
                 ; (push a i) → f (merid a i)}) ∣₀
morph.ismorph (grIso.fun (coHomPushout≅coHomSn n m)) =
  sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ a b → cong ∣_∣₀ (funExt λ {(inl x) → refl
                                    ; (inr x) → refl
                                    ; (push a i) → refl })
morph.fun (grIso.inv (coHomPushout≅coHomSn n m)) =
  sRec setTruncIsSet
       (λ f → ∣ (λ {north → f (inl tt)
                  ; south → f (inr tt)
                  ; (merid a i) → f (push a i)}) ∣₀)
morph.ismorph (grIso.inv (coHomPushout≅coHomSn n m)) = 
  sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ a b → cong ∣_∣₀ (funExt λ {north → refl
                                    ; south → refl
                                    ; (merid a i) → refl })
grIso.rightInv (coHomPushout≅coHomSn n m) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f → cong ∣_∣₀ (funExt λ {(inl x) → refl
                                  ; (inr x) → refl
                                  ; (push a i) → refl })
grIso.leftInv (coHomPushout≅coHomSn n m) =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
         λ f → cong ∣_∣₀ (funExt λ { north → refl
                                  ; south → refl
                                  ; (merid a i) → refl })


-------------------------- H⁰(S⁰) -----------------------------
S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a north = proj₁ a
S0→Int a south = proj₂ a

H⁰-S⁰≅ℤ×ℤ : grIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
H⁰-S⁰≅ℤ×ℤ =
  Iso'→Iso
    (iso'
      (iso (sRec (isOfHLevelProd 2 isSetInt isSetInt)
                 λ f → (f north) , (f south))
           (λ a → ∣ S0→Int a ∣₀)
           (λ { (a , b) → refl})
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → cong ∣_∣₀ (funExt (λ {north → refl ; south → refl}))))
      (sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 isSetInt isSetInt) _ _)
              λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i))

------------------------ H⁰(S¹) ------------------------------

H⁰-S¹≅ℤ : grIso intGroup (coHomGr 0 (S₊ 1))
H⁰-S¹≅ℤ =
  Iso'→Iso
    (iso'
      (iso
        (λ a → ∣ (λ x → a) ∣₀)
        (sRec isSetInt (λ f → f north))
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
               λ f → cong ∣_∣₀ (funExt (suspToPropRec north (λ _ → isSetInt _ _) refl)))
        (λ a → refl))
      λ a b → cong ∣_∣₀ (funExt λ x → sym (addLemma a b)))

--------------------------H¹(S¹) -----------------------------------


H¹-S¹≅ℤ : grIso intGroup (coHomGr 1 (S₊ 1))
H¹-S¹≅ℤ =
  compGrIso
    (diagonalIso1
      _
      (coHomGr 0 (S₊ 0))
      _
      (invGrIso H⁰-S⁰≅ℤ×ℤ)
      (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
      (λ x → MV.Ker-i⊂Im-d _ _(S₊ 0) (λ _ → tt) (λ _ → tt) 0 x
                           (×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)
                               (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)))
      (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
             (λ x inker
                   → pRec propTruncIsProp
                           (λ {((f , g) , id') → helper x f g id' inker})
                           ((MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₀ inker))))
      (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
             λ F surj
               → pRec (setTruncIsSet _ _)
                       (λ { (x , id) → MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ ∣
                                 (∣ (λ _ → x) ∣₀ , ∣ (λ _ → 0) ∣₀) ,
                                              (cong ∣_∣₀ (funExt (surjHelper x))) ∙ sym id ∣₋₁ }) surj) )
    (invGrIso (coHomPushout≅coHomSn 0 1))
                                              
  where
  surjHelper :  (x : Int) (x₁ : S₊ 0) → x +ₖ (-ₖ pos 0) ≡ S0→Int (x , x) x₁
  surjHelper x north = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x
  surjHelper x south = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x

  helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₀)
           (id : morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₀)
         → isInKer (coHomGr 0 (S₊ 0))
                    (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                    (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
                    ∣ F ∣₀
         → ∃[ x ∈ Int ] ∣ F ∣₀ ≡ morph.fun (grIso.inv H⁰-S⁰≅ℤ×ℤ) (x , x)
  helper F =
    sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f g id inker
             → pRec propTruncIsProp
                     (λ {((a , b) , id2)
                        → sElim2 {B = λ f g → morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₀ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₋₁)
                                  a b id2})
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₀ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] morph.fun (grIso.inv H⁰-S⁰≅ℤ×ℤ) (x , x)
             ≡ morph.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (∣ f ∣₀ , ∣ g ∣₀)
    helper2 f g = (f _ +ₖ (-ₖ g _) ) , cong ∣_∣₀ (funExt (λ {north → refl ; south → refl})) 


---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------

Hⁿ-Sⁿ≅ℤ : (n : ℕ) → grIso intGroup (coHomGr (suc n) (S₊ (suc n)))
Hⁿ-Sⁿ≅ℤ zero = H¹-S¹≅ℤ
Hⁿ-Sⁿ≅ℤ (suc n) =
  compGrIso
    (compGrIso
      (Hⁿ-Sⁿ≅ℤ n)
      theIso)
    (invGrIso (coHomPushout≅coHomSn (suc n) (suc (suc n))))
  where
  theIso : grIso (coHomGr (suc n) (S₊ (suc n))) (coHomGr (suc (suc n))
                 (Pushout {A = S₊ (suc n)} (λ _ → tt) (λ _ → tt)))
  theIso =
    SES→Iso
      (×coHomGr (suc n) Unit Unit)
      (×coHomGr (suc (suc n)) Unit Unit)
      (ses (λ p q → ×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (proj₁ p) (proj₁ q))
                        (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (proj₂ p) (proj₂ q)))
           (λ p q → ×≡ (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (proj₁ p) (proj₁ q))
                        (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (proj₂ p) (proj₂ q)))
           (MV.Δ _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.i _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (2 + n))
           (MV.d _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.Ker-d⊂Im-Δ _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n))
           (MV.Ker-i⊂Im-d _ _ (S₊ (suc n)) (λ _ → tt) (λ _ → tt) (suc n)))
--------------------------------------------------------------------


------------------------- H¹(S⁰) ≅ 0 -------------------------------
H¹-S⁰≅0 : grIso (coHomGr 1 (S₊ 0)) trivialGroup 
H¹-S⁰≅0 =
  Iso'→Iso
    (iso'
      (iso (λ _ → tt)
           (λ _ → 0ₕ)
           (λ _ → refl)
           (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                  λ f → pRec (setTruncIsSet _ _)
                              (λ id → cong ∣_∣₀ (sym id))
                              (helper f (f north) (f south) refl refl)))
      λ _ _ → refl)
  where
   helper : (f : S₊ 0 → coHomK 1) → (x y : coHomK 1) → (f north ≡ x) → (f south ≡ y) → ∥ f ≡ (λ _ → 0ₖ) ∥₋₁
   helper f =
     elim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 propTruncIsProp)
           (suspToPropRec2 north (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → propTruncIsProp)
           λ id id2 → ∣ funExt (λ {north → id ; south → id2}) ∣₋₁) 

------------------------- H²(S¹) ≅ 0 -------------------------------

H²-S¹≅0 : grIso (coHomGr 2 (S₊ 1)) trivialGroup
H²-S¹≅0 =
  invGrIso
    (compGrIso
      (invGrIso H¹-S⁰≅0)
      (compGrIso helpIso
      (invGrIso (coHomPushout≅coHomSn 0 2) )))
  where
  helpIso : grIso (coHomGr 1 (S₊ 0)) (coHomGr 2 (Pushout (λ _ → tt) (λ _ → tt)))
  helpIso =
    SES→Iso
      (×coHomGr 1 Unit Unit)
      (×coHomGr 2 Unit Unit)
      (ses
        (isOfHLevelSuc 0 (isOfHLevelProd 0 (isContrHⁿ-Unit 0) (isContrHⁿ-Unit 0)))
        (isOfHLevelSuc 0 (isOfHLevelProd 0 (isContrHⁿ-Unit 1) (isContrHⁿ-Unit 1)))
        (MV.Δ _ _ _ _ _ 1)
        (MV.i _ _ _ _ _ 2)
        (MV.d _ _ _ _ _ 1)
        (MV.Ker-d⊂Im-Δ _ _ _ _ _ 1)
        (sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
               λ f → MV.Ker-i⊂Im-d _ _ _ _ _ 1 ∣ f ∣₀))

-------------------------------------------------------------------

--------------- H¹(S²) --------------------------------------------
H¹-S²≅0 : grIso (coHomGr 1 (S₊ 2)) trivialGroup
H¹-S²≅0 =
  compGrIso (coHomPushout≅coHomSn 1 1)
    (compGrIso
      (Iso''→Iso
        (iso'' (MV.i _ _ (S₊ 1) (λ _ → tt) (λ _ → tt) 1)
               (λ x inker → helper x inker)
               λ x → ∣ 0ₕ , isOfHLevelSuc 0 (isOfHLevelProd 0 (isContrHⁿ-Unit 0) (isContrHⁿ-Unit 0)) _ x ∣₋₁))
      (compGrIso
        (dirProdIso
           (Hⁿ-Unit≅0 0) (Hⁿ-Unit≅0 0))
           lUnitGroupIso))
  where
  abstract
    surj-helper : (x : coHom 0 (S₊ 1))
            → isInIm (×coHomGr 0 Unit Unit) (coHomGr 0 _) (MV.Δ _ _ _ _ _ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
             λ f → ∣ (∣ (λ _ → f north) ∣₀ , 0ₕ)
                   , (cong ∣_∣₀ (funExt (suspToPropRec north
                                          (λ _ → isSetInt _ _) (cong (f north +ₖ_) -0ₖ  ∙ rUnitₖ (f north))))) ∣₋₁

    helper : (x : coHom 1 (Pushout (λ _ → tt) (λ _ → tt)))
            → isInKer (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt))) (×coHomGr 1 Unit Unit)
                       (MV.i Unit Unit (S₊ 1) (λ _ → tt) (λ _ → tt) 1) x
            → x ≡ 0ₕ
    helper x inker =
      pRec (setTruncIsSet _ _)
           (λ { (f , id) → sym id ∙ MV.Im-Δ⊂Ker-d _ _ _ _ _ 0 f (surj-helper f) })
           (MV.Ker-i⊂Im-d _ _ _ _ _ _ x inker)


--------- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

S¹map : hLevelTrunc 3 S¹ → S¹
S¹map = trRec isGroupoidS¹ (idfun _)

S¹map-id : (x : hLevelTrunc 3 S¹) → Path (hLevelTrunc 3 S¹) ∣ S¹map x ∣ x
S¹map-id = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → refl

S1map : hLevelTrunc 3 (S₊ 1) → (S₊ 1)
S1map = trRec isGroupoidS1 (idfun _)


S¹→S¹≡S¹×Int : Iso (S¹ → hLevelTrunc 3 S¹) (S¹ × Int)
Iso.fun S¹→S¹≡S¹×Int f = S¹map (f base)
                 , winding (basechange2⁻ (S¹map (f base)) λ i → S¹map (f (loop i)))
Iso.inv S¹→S¹≡S¹×Int (s , int) base = ∣ s ∣
Iso.inv S¹→S¹≡S¹×Int (s , int) (loop i) = ∣ basechange2 s (intLoop int) i ∣
Iso.rightInv S¹→S¹≡S¹×Int (s , int) = ×≡ refl ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                       ∙ windingIntLoop int)
Iso.leftInv S¹→S¹≡S¹×Int f = funExt λ { base → S¹map-id (f base)
                               ; (loop i) j → helper2 j i}
  where
  helper2 : PathP (λ i → S¹map-id (f base) i ≡ S¹map-id (f base) i)
                  (λ i → ∣ basechange2 (S¹map (f base))
                             (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁)))))) i ∣)
                  (cong f loop)
  helper2 i j = 
    hcomp (λ k → λ { (i = i0) → cong ∣_∣ (basechange2 (S¹map (f base))
                                           (intLoop (winding (basechange2⁻ (S¹map (f base)) (λ i₁ → S¹map (f (loop i₁))))))) j
                    ; (i = i1) → S¹map-id (f (loop j)) k
                    ; (j = i0) → S¹map-id (f base) (i ∧ k)
                    ; (j = i1) → S¹map-id (f base) (i ∧ k)})
          (helper4 i j)
    where
    helper4 : Path (Path (hLevelTrunc 3 _) _ _)
                   (cong ∣_∣ (basechange2 (S¹map (f base))
                                         (intLoop
                                           (winding
                                             (basechange2⁻ (S¹map (f base))
                                                           (λ i₁ → S¹map (f (loop i₁))))))))
                   λ i → ∣ S¹map (f (loop i)) ∣
    helper4 i =
      cong ∣_∣
           ((cong (basechange2 (S¹map (f base)))
                   (decodeEncode base (basechange2⁻ (S¹map (f base))
                                                    (λ i₁ → S¹map (f (loop i₁)))))
            ∙ basechange2-sect (S¹map (f base))
                               (λ i → S¹map (f (loop i)))) i)

S¹→S¹≡S1→S1 : Iso (S₊ 1 → hLevelTrunc 3 (S₊ 1)) (S¹ → hLevelTrunc 3 S¹)
Iso.fun S¹→S¹≡S1→S1 f x = trMap S1→S¹ (f (S¹→S1 x))
Iso.inv S¹→S¹≡S1→S1 f x = trMap S¹→S1 (f (S1→S¹ x))
Iso.rightInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-sect x i)) i
  where
  helper2 : (x : hLevelTrunc 3 S¹) → trMap S1→S¹ (trMap S¹→S1 x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-sect a)
Iso.leftInv S¹→S¹≡S1→S1 F = funExt λ x i → helper2 (F (S1→S¹-retr x i)) i
  where
  helper2 : (x : hLevelTrunc 3 (S₊ 1)) → trMap S¹→S1 (trMap S1→S¹ x) ≡ x
  helper2 = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ a → cong ∣_∣ (S1→S¹-retr a)




basechange-lemma : ∀ {ℓ} {A : Type ℓ} {a : A} (x y : S¹) (F : a ≡ a → S¹) (f : S¹ → a ≡ a) (g : S¹ → a ≡ a)
                  → (f base ≡ refl)
                  → (g base ≡ refl)
                  → basechange2⁻ (F (f base ∙ g base)) (cong₂ {A = S¹} {B = λ x → S¹} (λ x y → F (f x ∙ g y)) loop loop)
                   ≡ basechange2⁻ (F (f base)) (cong (λ x → F (f x)) loop) ∙ basechange2⁻ (F (g base)) (cong (λ x → F (g x)) loop)
basechange-lemma x y F f g frefl grefl  =
    ((λ i → basechange2⁻ (F (f base ∙ g base)) (cong₂Funct (λ x y → F (f x ∙ g y)) loop loop i))
  ∙∙ (λ i → basechange2⁻ (F (f base ∙ g base)) (cong (λ x₁ → F (f x₁ ∙ g base)) loop ∙ cong (λ y₁ → F (f base ∙ g y₁)) loop))
  ∙∙ basechange2⁻-morph (F (f base ∙ g base)) _ _)
  ∙∙ (λ j → basechange2⁻ (F (f base ∙ grefl j))
                        (λ i → F (f (loop i) ∙ grefl j))
          ∙ basechange2⁻ (F (frefl j ∙ g base))
                        (λ i → F (frefl j ∙ g (loop i))))
  ∙∙ ((λ j → basechange2⁻ (F (rUnit (f base) (~ j)))
                        (λ i → F (rUnit (f (loop i)) (~ j)))
          ∙ basechange2⁻ (F (lUnit (g base) (~ j)))
                        (λ i → F (lUnit (g (loop i)) (~ j)))))



coHom1S1≃ℤ : grIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ =
  Iso'→Iso
    (iso'
      (iso
        (sRec isSetInt (λ f → proj₂ (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) -- fun
        (λ a → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)) ∣₀) -- inv
         (λ a → (λ i → proj₂ (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)))))) -- rInv
              ∙ (λ i → proj₂ (Iso.fun S¹→S¹≡S¹×Int (Iso.rightInv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)) i)))
              ∙ λ i → proj₂ (Iso.rightInv S¹→S¹≡S¹×Int (base , a) i)) 
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)  -- lInv
               λ f → (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , proj₂ (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
                    ∙∙ ((λ i → sRec setTruncIsSet
                                  (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₀)
                                  (sRec setTruncIsSet
                                        (λ x → ∣ Iso.inv S¹→S¹≡S¹×Int (x , (proj₂ (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₀)
                                        (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (proj₁ (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) i)))
                     ∙ (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.leftInv S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f) i) ∣₀))
                    ∙∙ (λ i → ∣ Iso.leftInv S¹→S¹≡S1→S1 f i ∣₀)))
      (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) -- isMorph
              λ f g → (λ i → winding (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))))
                                       (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))))
                    ∙∙ cong winding (helper (f (S¹→S1 base)) (g (S¹→S1 base)) f g refl refl)
                    ∙∙ winding-hom ((basechange2⁻ (S¹map (trMap S1→S¹ (f north)))
                                                 (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))))
                                   ((basechange2⁻ (S¹map (trMap S1→S¹ (g north)))
                                                 (λ i → S¹map (trMap S1→S¹ (g (S¹→S1 (loop i)))))))))


  where
  helper : (x y : coHomK 1) (f g : S₊ 1 → coHomK 1)
        → (f (S¹→S1 base)) ≡ x
        → (g (S¹→S1 base)) ≡ y
        → (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base)))))))
                        (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))
          ≡ (basechange2⁻ (S¹map (trMap S1→S¹ ((f (S¹→S1 base))))))
                          (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))
          ∙ (basechange2⁻ (S¹map (trMap S1→S¹ ((g (S¹→S1 base)))))
                          (λ i → S¹map (trMap S1→S¹ ((g (S¹→S1 (loop i)))))))
  helper = elim2
             (λ _ _ → isGroupoidΠ4 λ _ _ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 3 (isGroupoidS¹) base base) _ _)
             (suspToPropRec2 {A = S₊ 0} north
                  (λ _ _ → isPropΠ4 λ _ _ _ _ → isGroupoidS¹ _ _ _ _)
                  λ f g reflf reflg →
                 (basechange-lemma
                    base
                    base
                    (λ x → S¹map (trMap S1→S¹ (ΩKn+1→Kn x)))
                    (λ x → Kn→ΩKn+1 1 (f (S¹→S1 x))) ((λ x → Kn→ΩKn+1 1 (g (S¹→S1 x))))
                    (cong (Kn→ΩKn+1 1) reflf ∙ Kn→ΩKn+10ₖ 1)
                    (cong (Kn→ΩKn+1 1) reflg ∙ Kn→ΩKn+10ₖ 1))
               ∙ λ j → basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 base)) j)))
                                     (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 (loop i))) j)))
                      ∙ basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 base)) j)))
                                     (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 (loop i))) j))))
