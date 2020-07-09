{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Connected
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

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit
open import Cubical.Structures.Group

open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Equiv


Sn-connected : (n : ℕ) (x : S₊ (suc n)) → ∥ north ≡ x ∥₋₁
Sn-connected n = suspToPropRec north (λ _ → propTruncIsProp) ∣ refl ∣₋₁

H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupEquiv (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ n = GrIsoToGrEquiv (H⁰-connected' north (Sn-connected n))

-- ----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.

coHomPushout≅coHomSn : (n m : ℕ) → GroupEquiv (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
coHomPushout≅coHomSn n m = transport (λ i → GroupEquiv (coHomGr m (PushoutSusp≡Susp {A = S₊ n} i))
                                       (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))) (idGroupEquiv _)

-------------------------- H⁰(S⁰) -----------------------------
S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a north = fst a
S0→Int a south = snd a

H⁰-S⁰≅ℤ×ℤ : GroupEquiv (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
GroupEquiv.eq H⁰-S⁰≅ℤ×ℤ =
  isoToEquiv (iso (sRec (isOfHLevelΣ 2 isSetInt λ _ → isSetInt) λ f → (f north) , (f south))
                  (λ a → ∣ S0→Int a ∣₂)
                  (λ _ → refl)
                  (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ f → cong ∣_∣₂ (funExt (λ {north → refl ; south → refl}))))
GroupEquiv.isHom H⁰-S⁰≅ℤ×ℤ =
  sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 isSetInt (λ _ → isSetInt)) _ _)
         λ a b i → addLemma (a north) (b north) i , addLemma (a south) (b south) i


-- --------------------------H¹(S¹) -----------------------------------


{-
In order to apply Mayer-Vietoris, we need the following lemma.
Given the following diagram
  a ↦ (a , 0)   ψ         ϕ
 A -->  A × A -------> B --->  C
If ψ is an isomorphism and ϕ is surjective with ker ϕ ≡ {ψ (a , a) ∣ a ∈ A}, then C ≅ B
-}

open GroupEquiv
diagonalIso : ∀ {ℓ ℓ' ℓ''} {A : Group {ℓ}} (B : Group {ℓ'}) {C : Group {ℓ''}}
               (ψ : GroupEquiv (dirProd A A) B) (ϕ : GroupHom B C)
             → isSurjective _ _ ϕ
             → ((x : ⟨ B ⟩) → isInKer B C ϕ x
                                    → ∃[ y ∈ ⟨ A ⟩ ] x ≡ fst (eq ψ) (y , y))
             → ((x : ⟨ B ⟩) → (∃[ y ∈ ⟨ A ⟩ ] x ≡ fst (eq ψ) (y , y))
                                    → isInKer B C ϕ x)
             → GroupEquiv A C
diagonalIso {A = A} B {C = C} ψ ϕ issurj ker→diag diag→ker =
  Iso'ToGroupEquiv
    (iso' (compGroupHom fstProj (compGroupHom (grouphom (fst (eq ψ)) (isHom ψ)) ϕ))
          (λ a inker
           → pRec (isSetCarrier A _ _)
                   (λ {(a' , id) → cong fst (sym (secEq (eq ψ) (a , 0g A)) ∙∙ cong (invEq (eq ψ)) id ∙∙ secEq (eq ψ) (a' , a'))
                                  ∙ cong snd (sym (secEq (eq ψ) (a' , a')) ∙∙ cong (invEq (eq ψ)) (sym id) ∙∙ secEq (eq ψ) (a , 0g A))})
                   (ker→diag _ inker))
          λ c → pRec propTruncIsProp
                     (λ { (b , id) → ∣ (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b))) -- (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)))
                                     , (sym (Group.rid C _)
                                     ∙∙ cong ((fun ϕ) (equivFun (eq ψ) (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)) , 0g A)) C.+_)
                                            (sym (diag→ker (equivFun (eq ψ) ((snd (ψ⁻ b)) , (snd (ψ⁻ b))))
                                                            ∣ (snd (ψ⁻ b)) , refl ∣₋₁))
                                     ∙∙ sym ((isHom ϕ) _ _))
                                     ∙∙ cong (fun ϕ) (sym ((isHom ψ) _ _)
                                                  ∙∙ cong (equivFun (eq ψ)) (ΣPathP (sym (Group.assoc A _ _ _)
                                                                                     ∙∙ cong (fst (ψ⁻ b) A.+_) (Group.invl A _)
                                                                                     ∙∙ Group.rid A _
                                                                                  , (Group.lid A _)))
                                                  ∙∙ retEq (eq ψ) b)
                                     ∙∙ id ∣₋₁ })
                     (issurj c))
  where
  open Group
  open IsGroup
  open GroupHom
  module A = Group A
  module B = Group B
  module C = Group C
  module A×A = Group (dirProd A A)
  module ψ = GroupEquiv ψ
  module ϕ = GroupHom ϕ
  ψ⁻ = fst (invEquiv (eq ψ))

  fstProj : GroupHom A (dirProd A A)
  GroupHom.fun fstProj a = a , 0g A
  GroupHom.isHom fstProj g0 g1 i = (g0 A.+ g1) , Group.lid A (0g A) (~ i)


H¹-S¹≅ℤ : GroupEquiv intGroup (coHomGr 1 (S₊ 1))
H¹-S¹≅ℤ =
    diagonalIso (coHomGr 0 (S₊ 0))
                (invGroupEquiv H⁰-S⁰≅ℤ×ℤ)
                (MV.d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
                (λ x → MV.Ker-i⊂Im-d _ _(S₊ 0) (λ _ → tt) (λ _ → tt) 0 x
                                     (ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _
                                            , isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                        (λ x inker
                            → pRec propTruncIsProp
                                    (λ {((f , g) , id') → helper x f g id' inker})
                                    ((MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ x ∣₂ inker)))))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ F surj
                           → pRec (setTruncIsSet _ _)
                                   (λ { (x , id) → MV.Im-Δ⊂Ker-d _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₂
                                                      ∣ (∣ (λ _ → x) ∣₂ , ∣ (λ _ → 0) ∣₂) ,
                                                       (cong ∣_∣₂ (funExt (surjHelper x))) ∙ sym id ∣₋₁ })
                                   surj) )
  □ invGroupEquiv (coHomPushout≅coHomSn 0 1)
  where

  surjHelper :  (x : Int) (x₁ : S₊ 0) → x +ₖ (-ₖ pos 0) ≡ S0→Int (x , x) x₁
  surjHelper x north = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x
  surjHelper x south = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x

  helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₂)
           (id : GroupHom.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₂)
         → isInKer (coHomGr 0 (S₊ 0))
                    (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                    (MV.d Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0)
                    ∣ F ∣₂
         → ∃[ x ∈ Int ] ∣ F ∣₂ ≡ equivFun (invEquiv (eq H⁰-S⁰≅ℤ×ℤ)) (x , x)
  helper F =
    sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f g id inker
             → pRec propTruncIsProp
                     (λ {((a , b) , id2)
                        → sElim2 {B = λ f g → GroupHom.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (f , g) ≡ ∣ F ∣₂ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₋₁)
                                  a b id2})
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₂ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] (equivFun (invEquiv (eq H⁰-S⁰≅ℤ×ℤ))) (x , x)
             ≡ GroupHom.fun (MV.Δ Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt) 0) (∣ f ∣₂ , ∣ g ∣₂)
    helper2 f g = (f _ +ₖ (-ₖ g _) ) , cong ∣_∣₂ (funExt (λ {north → refl ; south → refl}))

------------------------- H¹(S⁰) ≅ 0 -------------------------------


H¹-S⁰≅0 : GroupEquiv (coHomGr 1 (S₊ 0)) trivialGroup
eq H¹-S⁰≅0 =
  isoToEquiv
    (iso (λ _ → tt)
         (λ _ → 0ₕ)
         (λ _ → refl)
         (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                (λ f → pRec (setTruncIsSet _ _)
                             (λ id → cong ∣_∣₂ (sym id))
                             (helper f (f north) (f south) refl refl))))
  where
  helper : (f : S₊ 0 → coHomK 1) → (x y : coHomK 1) → (f north ≡ x) → (f south ≡ y) → ∥ f ≡ (λ _ → 0ₖ) ∥₋₁
  helper f =
    elim2 (λ _ _ → isOfHLevelΠ 3 λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 propTruncIsProp)
          (suspToPropRec2 north (λ _ _ → isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → propTruncIsProp)
          λ id id2 → ∣ funExt (λ {north → id ; south → id2}) ∣₋₁)
isHom H¹-S⁰≅0 _ _ = refl

------------------------- H²(S¹) ≅ 0 -------------------------------

H²-S¹≅0 : GroupEquiv (coHomGr 2 (S₊ 1)) trivialGroup
H²-S¹≅0 =
    coHomPushout≅coHomSn 0 2
  □ (invGroupEquiv (vSES→GroupEquiv _ _ vSES-helper))
  □ H¹-S⁰≅0
  where
  module I = MV Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt)
  vSES-helper : vSES (coHomGr 1 (S₊ 0)) (coHomGr 2 (Pushout (λ _ → tt) (λ _ → tt)))
                     _ _
  vSES.isTrivialLeft vSES-helper = isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit 0) (λ _ → isContrHⁿ-Unit 0))
  vSES.isTrivialRight vSES-helper = isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit 1) (λ _ → isContrHⁿ-Unit 1))
  vSES.left vSES-helper = I.Δ 1
  vSES.right vSES-helper = I.i 2
  vSES.ϕ vSES-helper = I.d 1
  vSES.Ker-ϕ⊂Im-left vSES-helper = I.Ker-d⊂Im-Δ 1
  vSES.Ker-right⊂Im-ϕ vSES-helper = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp) -- doesn't terminate without elimination
                                          λ a → I.Ker-i⊂Im-d 1 ∣ a ∣₂


-------------------------------------------------------------------

--------------- H¹(S²) --------------------------------------------

H¹-S²≅0 : GroupEquiv (coHomGr 1 (S₊ 2)) trivialGroup
H¹-S²≅0 =
    coHomPushout≅coHomSn 1 1
  □ Iso'ToGroupEquiv
      (iso' (I.i 1)
            helper
            λ x → ∣ 0ₕ , isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit 0) (λ _ → isContrHⁿ-Unit 0)) _ x ∣₋₁)
  □ dirProdEquiv (Hⁿ-Unit≅0 0) (Hⁿ-Unit≅0 0)
  □ lUnitGroupIso
  where
    module I = MV Unit Unit (S₊ 1) (λ _ → tt) (λ _ → tt)
    surj-helper : (x : ⟨ coHomGr 0 (S₊ 1) ⟩) → isInIm _ _ (I.Δ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
             λ f → ∣ (∣ (λ _ → f north) ∣₂ , 0ₕ)
                   , (cong ∣_∣₂ (funExt (suspToPropRec north
                                         (λ _ → isSetInt _ _)
                                         (cong (f north +ₖ_) -0ₖ  ∙ rUnitₖ (f north))))) ∣₋₁
    helper : isInjective _ _ (I.i 1)
    helper =
      sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 (setTruncIsSet _ _))  -- useless elimination speeds things up significantly
             λ x inker → pRec (setTruncIsSet _ _)
                               (sigmaElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                           λ a id → sym id ∙ I.Im-Δ⊂Ker-d 0 ∣ a ∣₂ (surj-helper _))
                               (I.Ker-i⊂Im-d 0 ∣ x ∣₂ inker)


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
Iso.rightInv S¹→S¹≡S¹×Int (s , int) = ΣPathP (refl , ((λ i → winding (basechange2-retr s (λ i → intLoop int i) i))
                                                      ∙ windingIntLoop int))
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



coHom1S1≃ℤ : GroupEquiv (coHomGr 1 (S₊ 1)) intGroup
eq coHom1S1≃ℤ =
  isoToEquiv
    (iso (sRec isSetInt (λ f → snd (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f))))                                                 -- fun
         (λ a → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)) ∣₂)                                                           -- inv
         (λ a → (λ i → snd (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)))))) -- rInv
              ∙ (λ i → snd (Iso.fun S¹→S¹≡S¹×Int (Iso.rightInv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , a)) i)))
              ∙ λ i → snd (Iso.rightInv S¹→S¹≡S¹×Int (base , a) i))
         ((sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)                                                                            -- lInv
                 λ f → (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.inv S¹→S¹≡S¹×Int (base , snd (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₂)
                      ∙∙ ((λ i → sRec setTruncIsSet
                                    (λ x → ∣ Iso.inv S¹→S¹≡S1→S1 x ∣₂)
                                    (sRec setTruncIsSet
                                          (λ x → ∣ Iso.inv S¹→S¹≡S¹×Int (x , (snd (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) ∣₂)
                                          (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (fst (Iso.fun S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f)))) i)))
                       ∙ (λ i → ∣ Iso.inv S¹→S¹≡S1→S1 (Iso.leftInv S¹→S¹≡S¹×Int (Iso.fun S¹→S¹≡S1→S1 f) i) ∣₂))
                      ∙∙ (λ i → ∣ Iso.leftInv S¹→S¹≡S1→S1 f i ∣₂))))
isHom coHom1S1≃ℤ =
  (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)                                                                                       -- isMorph
           λ f g → (λ i → winding (basechange2⁻ (S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))))
                                    (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i)))))))))
                 ∙∙ cong winding (helper (f (S¹→S1 base)) (g (S¹→S1 base)) f g refl refl)
                 ∙∙ winding-hom ((basechange2⁻ (S¹map (trMap S1→S¹ (f north)))
                                              (λ i → S¹map (trMap S1→S¹ (f (S¹→S1 (loop i)))))))
                                ((basechange2⁻ (S¹map (trMap S1→S¹ (g north)))
                                              (λ i → S¹map (trMap S1→S¹ (g (S¹→S1 (loop i))))))))
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
  helper = elim2 (λ _ _ → isGroupoidΠ4 λ _ _ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 3 (isGroupoidS¹) base base) _ _)
                 (suspToPropRec2 {A = S₊ 0} north
                      (λ _ _ → isPropΠ4 λ _ _ _ _ → isGroupoidS¹ _ _ _ _)
                      λ f g reflf reflg →
                     (basechange-lemma
                        base
                        base
                        (λ x → S¹map (trMap S1→S¹ (ΩKn+1→Kn x)))
                        (λ x → Kn→ΩKn+1 1 (f (S¹→S1 x)))
                        ((λ x → Kn→ΩKn+1 1 (g (S¹→S1 x))))
                        (cong (Kn→ΩKn+1 1) reflf ∙ Kn→ΩKn+10ₖ 1)
                        (cong (Kn→ΩKn+1 1) reflg ∙ Kn→ΩKn+10ₖ 1))
                   ∙ λ j → basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 base)) j)))
                                         (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 (loop i))) j)))
                          ∙ basechange2⁻ (S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 base)) j)))
                                         (λ i → S¹map (trMap S1→S¹ (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 (loop i))) j))))



---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------

Hⁿ-Sⁿ≅ℤ : (n : ℕ) → GroupEquiv intGroup (coHomGr (suc n) (S₊ (suc n)))
Hⁿ-Sⁿ≅ℤ zero = invGroupEquiv coHom1S1≃ℤ
Hⁿ-Sⁿ≅ℤ (suc n) =
    Hⁿ-Sⁿ≅ℤ n
  □ vSES→GroupEquiv _ _ theIso
  □ invGroupEquiv (coHomPushout≅coHomSn (suc n) (suc (suc n)))
  where
  module I = MV Unit Unit (S₊ (suc n)) (λ _ → tt) (λ _ → tt)
  theIso : vSES (coHomGr (suc n) (S₊ (suc n))) (coHomGr (suc (suc n))
                (Pushout {A = S₊ (suc n)} (λ _ → tt) (λ _ → tt)))
                _
                _
  vSES.isTrivialLeft theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (fst p) (fst q)
                                        , isOfHLevelSuc 0 (isContrHⁿ-Unit n) (snd p) (snd q))
  vSES.isTrivialRight theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (fst p) (fst q)
                                         , isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (snd p) (snd q))
  vSES.left theIso = I.Δ (suc n)
  vSES.right theIso = I.i (2 + n)
  vSES.ϕ theIso = I.d (suc n)
  vSES.Ker-ϕ⊂Im-left theIso = I.Ker-d⊂Im-Δ  (suc n)
  vSES.Ker-right⊂Im-ϕ theIso = I.Ker-i⊂Im-d (suc n)
