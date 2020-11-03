{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification  #-}
module Cubical.ZCohomology.pathComp.Groups2.Sn where

open import Cubical.ZCohomology.pathComp.Base
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.EilenbergIso
open import Cubical.ZCohomology.pathComp.Groups2.Unit
open import Cubical.ZCohomology.pathComp.Groups2.Connected
open import Cubical.ZCohomology.pathComp.MayerVietoris2
open import Cubical.ZCohomology.pathComp.Groups2.Prelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁) hiding (map)

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit

open import Cubical.Homotopy.Connected

open import Cubical.Algebra.Group

infixr 31 _□_
_□_ : _
_□_ = compGroupIso

open GroupEquiv
open vSES
open GroupIso
open GroupHom
open BijectionIso

Sn-connected : (n : ℕ) → isConnected 2 (S₊ (suc n))
Sn-connected zero = sphereConnected 1
Sn-connected (suc n) = ∣ north ∣ , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                                         (suspToPropElim (ptSn (suc n)) (λ _ → isOfHLevelTrunc 2 _ _) refl)

H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ n = H⁰-connected (ptSn (suc n)) (Sn-connected n)

-- -- ----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.


S1Iso : Iso S¹ (Pushout {A = Bool} (λ _ → tt) λ _ → tt)
S1Iso = S¹IsoSuspBool ⋄ invIso PushoutSuspIsoSusp

coHomPushout≅coHomSn : (n m : ℕ) → GroupIso (coHomGr m (S₊ (suc n)))
                                             (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
coHomPushout≅coHomSn zero m =
  Iso+Hom→GrIso (setTruncIso (domIso S1Iso))
                (sElim2 (λ _ _ → isSet→isGroupoid setTruncIsSet _ _) (λ _ _ → refl))
coHomPushout≅coHomSn (suc n) m =
  Iso+Hom→GrIso (setTruncIso (domIso (invIso PushoutSuspIsoSusp)))
                (sElim2 (λ _ _ → isSet→isGroupoid setTruncIsSet _ _) (λ _ _ → refl))

-------------------------- H⁰(S⁰) -----------------------------
S0→Int : (a : Int × Int) → S₊ 0 → loopK 0
S0→Int a true = Iso.inv IsoLoopK₀Int (fst a)
S0→Int a false = Iso.inv IsoLoopK₀Int (snd a)

H⁰-S⁰≅ℤ×ℤ : GroupIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
H⁰-S⁰≅ℤ×ℤ = Iso+Hom→GrIso help
                           (sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× isSetInt isSetInt) _ _)
                                   λ f g → ΣPathP (addLemma (f true) (g true) , addLemma (f false) (g false)))
  where
  help : Iso (coHom' 0 Bool) (Int × Int)
  Iso.fun help = sRec (isSet× isSetInt isSetInt) λ f → (Iso.fun IsoLoopK₀Int (f true)) , Iso.fun IsoLoopK₀Int (f false)
  Iso.inv help a = ∣ S0→Int a ∣₂
  Iso.rightInv help b = ΣPathP (Iso.rightInv IsoLoopK₀Int (fst b) , Iso.rightInv IsoLoopK₀Int (snd b))
  Iso.leftInv help =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ f → cong ∣_∣₂ (funExt λ {true → Iso.leftInv IsoLoopK₀Int (f true)
                                  ; false → Iso.leftInv IsoLoopK₀Int (f false)})

-- ------------------------- H¹(S⁰) ≅ 0 -------------------------------


private
  Hⁿ-S0≃loopKₙ×loopKₙ : (n : ℕ) → Iso (S₊ 0 → loopK (suc n)) (loopK (suc n) × loopK (suc n))
  Iso.fun (Hⁿ-S0≃loopKₙ×loopKₙ n) f = (f true) , (f false)
  Iso.inv (Hⁿ-S0≃loopKₙ×loopKₙ n) (a , b) true = a
  Iso.inv (Hⁿ-S0≃loopKₙ×loopKₙ n) (a , b) false = b
  Iso.rightInv (Hⁿ-S0≃loopKₙ×loopKₙ n) a = refl
  Iso.leftInv (Hⁿ-S0≃loopKₙ×loopKₙ n) b = funExt λ {true → refl ; false → refl}

  isContrHⁿ-S0 : (n : ℕ) → isContr (coHom' (suc n) (S₊ 0))
  isContrHⁿ-S0 n = isOfHLevelRetractFromIso 0 (compIso (setTruncIso (Hⁿ-S0≃loopKₙ×loopKₙ n)) (compIso setTruncTrunc2Iso (truncOfProdIso 2)))
                                  (isOfHLevel× 0 (is2ConnectedLoopK n) (is2ConnectedLoopK n))

H¹-S⁰≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ 0)) trivialGroup
H¹-S⁰≅0 n = IsoContrGroupTrivialGroup (isContrHⁿ-S0 n)

------------------------- H²(S¹) ≅ 0 -------------------------------

Hⁿ-S¹≅0 : (n : ℕ) → GroupIso (coHomGr (2 + n) (S₊ 1)) trivialGroup
Hⁿ-S¹≅0 n = IsoContrGroupTrivialGroup helper3
  where
  helper : Iso (coHom' (2 + n) (S₊ 1)) ∥ Σ[ x ∈ loopK (2 + n) ] ∥ x ≡ x ∥₂ ∥₂
  helper = compIso (setTruncIso IsoFunSpaceS¹) IsoSetTruncateSndΣ

  helper3 : isContr (coHom' (2 + n) (S₊ 1))
  helper3 = (0ₕ (2 + n))
          , coHomPointedElim (suc n) base (λ _ → setTruncIsSet _ _)
                             λ f id → trRec (setTruncIsSet _ _)
                                             (λ p → cong ∣_∣₂ (funExt λ {base → sym id
                                                                      ; (loop i) j → hcomp (λ k → λ { (i = i0) → id (~ j)
                                                                                                      ; (i = i1) → id (~ j)
                                                                                                      ; (j = i0) → 0ₖ (suc (suc n))
                                                                                                      ; (j = i1) → p (~ k) i})
                                                                                            (id (~ j))}))
                                             (Iso.fun (PathIdTruncIso _) (isOfHLevelSuc 0 (helper4 (f base)) ∣ cong f loop ∣ ∣ refl ∣))
    where
    lossy : isConnected (4 + n) (coHomK (3 + n))
    lossy = isConnectedKn (2 + n)

    helper4 : (x : loopK (2 + n)) → isConnected 2 (x ≡ x) 
    helper4 x = isConnectedRetractFromIso 2
                   (maybe2 (2 + n) x)
                   (isConnectedPath 2
                     (isConnectedPath 3
                       (isConnectedSubtr 4 n (subst (λ x → isConnected x (coHomK (3 + n))) (+-comm 4 n)
                                         lossy))  _ _)  _ _)

-- --------------- H¹(Sⁿ), n ≥ 1 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupIso (coHomGr 1 (S₊ (2 + n))) trivialGroup
H¹-Sⁿ≅0 zero = IsoContrGroupTrivialGroup
                (isOfHLevelRetractFromIso 0
                  addTrunc
                  isContrH¹S²-ish) -- isContrH¹S²
  where
  addTrunc : Iso ∥ (S₊ 2 → loopK 1) ∥₂ ∥ (S₊ 2 → ∥ loopK 1 ∥ 3) ∥₂
  addTrunc = setTruncIso (codomainIso (invIso (truncIdempotentIso 3 (isOfHLevelTrunc 4 _ _)))) 

  isContrH¹S²-ish : isContr (∥ (S₊ 2 → ∥ loopK 1 ∥ 3) ∥₂)
  isContrH¹S²-ish = ∣ (λ _ → ∣ refl ∣) ∣₂
              , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                      λ f → helper f (f north) refl
    where
    helper : (f : (Susp S¹ → ∥ loopK 1 ∥ 3)) (x : ∥ loopK 1 ∥ 3) → f north ≡ x →  ∣ (λ _ → ∣ (λ _ → ∣ north ∣) ∣) ∣₂ ≡ ∣ f ∣₂
    helper f = Iso.inv (elim.isIsoPrecompose {A = Unit} (λ _ → ∣ refl ∣)
                       1
                       (λ _ → _ , isPropΠ λ _ → setTruncIsSet _ _)
                       (isConnectedPoint 1 (isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso 2 1))
                                                                       (isConnectedLoopK 0))
                                           ∣ refl ∣))
                       λ _ p → cong ∣_∣₂ (funExt (λ x → sym p ∙∙ sym (spoke f north) ∙∙ spoke f x))
H¹-Sⁿ≅0 (suc n) = IsoContrGroupTrivialGroup isContrH¹S³⁺ⁿ
-- IsoContrGroupTrivialGroup isContrH¹S³⁺ⁿ
  where
  anIso : Iso ⟨ coHomGr 1 (S₊ (3 + n)) ⟩ ∥ (S₊ (3 + n) → hLevelTrunc (4 + n) (loopK 1)) ∥₂
  anIso = setTruncIso (codomainIso (invIso (truncIdempotentIso (4 + n) (isOfHLevelPlus' {n = n} 4 (isOfHLevelSuc 3 (isOfHLevelTrunc 4 _ _))))))

  isContrH¹S³⁺ⁿ-ish : (f : ⟨ coHomGr 1 (S₊ (3 + n)) ⟩)
                   → ∣ (λ _ → ∣ refl ∣) ∣₂ ≡ Iso.fun anIso f
  isContrH¹S³⁺ⁿ-ish =
    coHomPointedElim zero north
                     (λ _ → setTruncIsSet _ _)
                     λ f p → cong ∣_∣₂ (funExt λ x → cong ∣_∣ (sym p) ∙∙ sym (spoke (λ a → ∣ f a ∣) north) ∙∙ spoke (λ a → ∣ f a ∣) x)

  isContrH¹S³⁺ⁿ : isContr ⟨ coHomGr 1 (S₊ (3 + n)) ⟩
  isContrH¹S³⁺ⁿ =
    isOfHLevelRetractFromIso 0
      anIso
      (∣ (λ _ → ∣ refl ∣) ∣₂
      , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → isContrH¹S³⁺ⁿ-ish (Iso.inv anIso ∣ f ∣₂) ∙ Iso.rightInv anIso ∣ f ∣₂)

-- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

coHom1S1≃ℤ : GroupIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ =
  compGroupIso
    halfway
      (compGroupIso (dirProdGroupIso halfway2 (IsoContrGroupTrivialGroup help))
                    rUnitGroupIso)

  where
  help : isContr ⟨ auxGr ((∥ Susp S¹ ∥ 4) , ∣ north ∣) ⟩
  help =
    isOfHLevelRetractFromIso 0 setTruncTrunc2Iso
      (isConnectedPath 2 (isConnectedKn 1) _ _)

--- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------
{-
Hⁿ-Sⁿ≅ℤ : (n : ℕ) → GroupIso intGroup (coHomGr (suc n) (S₊ (suc n)))
Hⁿ-Sⁿ≅ℤ zero = invGroupIso coHom1S1≃ℤ
Hⁿ-Sⁿ≅ℤ (suc n) =
    Hⁿ-Sⁿ≅ℤ n
  □ vSES→GroupIso _ _ theIso
  □ invGroupIso (coHomPushout≅coHomSn (suc n) (suc (suc n)))
  where
  module K = MV Unit Unit (S₊ (suc n)) (λ _ → tt) (λ _ → tt)
  theIso : vSES (coHomGr (suc n) (S₊ (suc n))) (coHomGr (suc (suc n))
                (Pushout {A = S₊ (suc n)} (λ _ → tt) (λ _ → tt)))
                _
                _
  isTrivialLeft theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (fst p) (fst q)
                                        , isOfHLevelSuc 0 (isContrHⁿ-Unit n) (snd p) (snd q))
  isTrivialRight theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (fst p) (fst q)
                                         , isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (snd p) (snd q))
  left theIso = K.Δ (suc n)
  right theIso = K.i (2 + n)
  vSES.ϕ theIso = K.d (suc n)
  Ker-ϕ⊂Im-left theIso = K.Ker-d⊂Im-Δ  (suc n)
  Ker-right⊂Im-ϕ theIso = K.Ker-i⊂Im-d (suc n)
-}
{-
In order to apply Mayer-Vietoris, we need the following lemma.
Given the following diagram
  a ↦ (a , 0)   ψ         ϕ
 A -->  A × A -------> B --->  C
If ψ is an isomorphism and ϕ is surjective with ker ϕ ≡ {ψ (a , a) ∣ a ∈ A}, then C ≅ B
-}


diagonalIso : ∀ {ℓ ℓ' ℓ''} {A : Group {ℓ}} (B : Group {ℓ'}) {C : Group {ℓ''}}
               (ψ : GroupIso (dirProd A A) B) (ϕ : GroupHom B C)
             → isSurjective _ _ ϕ
             → ((x : ⟨ B ⟩) → isInKer B C ϕ x
                                    → ∃[ y ∈ ⟨ A ⟩ ] x ≡ (fun (map ψ)) (y , y))
             → ((x : ⟨ B ⟩) → (∃[ y ∈ ⟨ A ⟩ ] x ≡ (fun (map ψ)) (y , y))
                                    → isInKer B C ϕ x)
             → GroupIso A C
diagonalIso {A = A} B {C = C} ψ ϕ issurj ker→diag diag→ker = BijectionIsoToGroupIso bijIso
  where
  open GroupStr
  module A = GroupStr (snd A)
  module B = GroupStr (snd B)
  module C = GroupStr (snd C)
  module A×A = GroupStr (snd (dirProd A A))
  module ψ = GroupIso ψ
  module ϕ = GroupHom ϕ
  ψ⁻ = inv ψ

  fstProj : GroupHom A (dirProd A A)
  fun fstProj a = a , GroupStr.0g (snd A)
  isHom fstProj g0 g1 i = (g0 A.+ g1) , GroupStr.lid (snd A) (GroupStr.0g (snd A)) (~ i)

  bijIso : BijectionIso A C
  map' bijIso = compGroupHom fstProj (compGroupHom (map ψ) ϕ)
  inj bijIso a inker = pRec (isSetCarrier A _ _)
                             (λ {(a' , id) → (cong fst (sym (leftInv ψ (a , GroupStr.0g (snd A))) ∙∙ cong ψ⁻ id ∙∙ leftInv ψ (a' , a')))
                                           ∙ cong snd (sym (leftInv ψ (a' , a')) ∙∙ cong ψ⁻ (sym id) ∙∙ leftInv ψ (a , GroupStr.0g (snd A)))})
                             (ker→diag _ inker)
  surj bijIso c =
    pRec propTruncIsProp
         (λ { (b , id) → ∣ (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)))
                          , ((sym (GroupStr.rid (snd C) _)
                           ∙∙ cong ((fun ϕ) ((fun (map ψ)) (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)) , GroupStr.0g (snd A))) C.+_)
                                  (sym (diag→ker (fun (map ψ) ((snd (ψ⁻ b)) , (snd (ψ⁻ b))))
                                                  ∣ (snd (ψ⁻ b)) , refl ∣₁))
                           ∙∙ sym ((isHom ϕ) _ _))
                           ∙∙ cong (fun ϕ) (sym ((isHom (map ψ)) _ _)
                                        ∙∙ cong (fun (map ψ)) (ΣPathP (sym (GroupStr.assoc (snd A) _ _ _)
                                                                           ∙∙ cong (fst (ψ⁻ b) A.+_) (GroupStr.invl (snd A) _)
                                                                           ∙∙ GroupStr.rid (snd A) _
                                                                        , (GroupStr.lid (snd A) _)))
                                        ∙∙ rightInv ψ b)
                           ∙∙ id) ∣₁ })
         (issurj c)

H¹-S¹≅ℤ : GroupIso intGroup (coHomGr 1 (S₊ 1))
H¹-S¹≅ℤ =
    diagonalIso (coHomGr 0 (S₊ 0))
                (invGroupIso H⁰-S⁰≅ℤ×ℤ)
                (K.d 0)
                (λ x → K.Ker-i⊂Im-d 0 x
                                     (ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _
                                            , isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                        (λ x inker
                            → pRec propTruncIsProp
                                    (λ {((f , g) , id') → helper x f g id' inker})
                                    ((K.Ker-d⊂Im-Δ 0 ∣ x ∣₂ inker)))))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ F surj
                           → pRec (setTruncIsSet _ _)
                                   (λ { (x , id) → K.Im-Δ⊂Ker-d 0 ∣ F ∣₂
                                                      ∣ (∣ (λ _ → x) ∣₂ , ∣ (λ _ → 0) ∣₂) ,
                                                       (cong ∣_∣₂ (funExt (surjHelper x))) ∙ sym id ∣₁ })
                                   surj) )
  □ invGroupIso (coHomPushout≅coHomSn 0 1)
  where
  module K = MV Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt)

  surjHelper :  (x : Int) (x₁ : S₊ 0) → ? --  x -[ 0 ]ₖ 0 ≡ S0→Int (x , x) x₁
  surjHelper x true = Iso.leftInv (Iso-Kn-ΩKn+1 0) x
  surjHelper x false = Iso.leftInv (Iso-Kn-ΩKn+1 0) x

  helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₂)
           (id : GroupHom.fun (K.Δ 0) (f , g) ≡ ∣ F ∣₂)
         → isInKer (coHomGr 0 (S₊ 0))
                    (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                    (K.d 0)
                    ∣ F ∣₂
         → ∃[ x ∈ Int ] ∣ F ∣₂ ≡ inv H⁰-S⁰≅ℤ×ℤ (x , x)
  helper F =
    sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f g id inker
             → pRec propTruncIsProp
                     (λ ((a , b) , id2)
                        → sElim2 {C = λ f g → GroupHom.fun (K.Δ 0) (f , g) ≡ ∣ F ∣₂ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₁)
                                  a b id2)
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₂ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] (inv H⁰-S⁰≅ℤ×ℤ (x , x))
             ≡ GroupHom.fun (K.Δ 0) (∣ f ∣₂ , ∣ g ∣₂)
    helper2 f g = (f _ -[ 0 ]ₖ g _) , cong ∣_∣₂ (funExt λ {true → refl ; false → refl})
