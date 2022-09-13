{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +Comm to +ℤ-comm ; +Assoc to +ℤ-assoc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as T

open import Cubical.Homotopy.Connected

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Prelims

infixr 31 _□_
_□_ : _
_□_ = compGroupIso

open IsGroupHom
open BijectionIso
open Iso



-------------------------- H⁰(Sⁿ) for n > 1 -----------------------------

Sn-connected : (n : ℕ) (x : typ (S₊∙ (suc n))) → ∥ pt (S₊∙ (suc n)) ≡ x ∥₁
Sn-connected zero = toPropElim (λ _ → isPropPropTrunc) ∣ refl ∣₁
Sn-connected (suc zero) = suspToPropElim base (λ _ → isPropPropTrunc) ∣ refl ∣₁
Sn-connected (suc (suc n)) = suspToPropElim north (λ _ → isPropPropTrunc) ∣ refl ∣₁

suspensionAx-Sn : (n m : ℕ) → GroupIso (coHomGr (2 + n) (S₊ (2 + m)))
                                         (coHomGr (suc n) (S₊ (suc m)))
suspensionAx-Sn n m =
  compIso (setTruncIso (invIso funSpaceSuspIso)) helperIso ,
  makeIsGroupHom funIsHom
  where
  helperIso : Iso ∥ (Σ[ x ∈ coHomK (2 + n) ]
                  Σ[ y ∈ coHomK (2 + n) ]
                   (S₊ (suc m) → x ≡ y)) ∥₂
              (coHom (suc n) (S₊ (suc m)))
  Iso.fun helperIso =
    ST.rec isSetSetTrunc
         (uncurry
           (coHomK-elim _
             (λ _ → isOfHLevelΠ (2 + n)
                λ _ → isOfHLevelPlus' {n = n} 2 isSetSetTrunc)
             (uncurry
               (coHomK-elim _
                 (λ _ → isOfHLevelΠ (2 + n)
                    λ _ → isOfHLevelPlus' {n = n} 2 isSetSetTrunc)
                 λ f → ∣ (λ x → ΩKn+1→Kn (suc n) (f x)) ∣₂))))
  Iso.inv helperIso =
    ST.map λ f → (0ₖ _) , (0ₖ _ , λ x → Kn→ΩKn+1 (suc n) (f x))
  Iso.rightInv helperIso =
    coHomPointedElim _ (ptSn (suc m)) (λ _ → isSetSetTrunc _ _)
      λ f fId → cong ∣_∣₂ (funExt (λ x → Iso.leftInv (Iso-Kn-ΩKn+1 _) (f x)))
  Iso.leftInv helperIso =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
      (uncurry
        (coHomK-elim _
          (λ _ → isProp→isOfHLevelSuc (suc n) (isPropΠ λ _ → isSetSetTrunc _ _))
          (uncurry
            (coHomK-elim _
              (λ _ → isProp→isOfHLevelSuc (suc n) (isPropΠ λ _ → isSetSetTrunc _ _))
              λ f → cong ∣_∣₂
                      (ΣPathP (refl ,
                        ΣPathP (refl ,
                          (λ i x → Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (f x) i))))))))

  theFun : coHom (2 + n) (S₊ (2 + m)) → coHom (suc n) (S₊ (suc m))
  theFun = Iso.fun (compIso (setTruncIso (invIso funSpaceSuspIso))
                             helperIso)

  funIsHom : (x y : coHom (2 + n) (S₊ (2 + m)))
          → theFun (x +ₕ y) ≡ theFun x +ₕ theFun y
  funIsHom =
    coHomPointedElimSⁿ _ _ (λ _ → isPropΠ λ _ → isSetSetTrunc _ _)
      λ f → coHomPointedElimSⁿ _ _ (λ _ → isSetSetTrunc _ _)
        λ g → cong ∣_∣₂ (funExt λ x → cong (ΩKn+1→Kn (suc n)) (sym (∙≡+₂ n (f x) (g x)))
                                    ∙ ΩKn+1→Kn-hom (suc n) (f x) (g x))


H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr 0 (S₊ (suc n))) ℤGroup
H⁰-Sⁿ≅ℤ zero = H⁰-connected base (Sn-connected 0)
H⁰-Sⁿ≅ℤ (suc n) = H⁰-connected north (Sn-connected (suc n))

----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.


S1Iso : Iso S¹ (Pushout {A = Bool} (λ _ → tt) λ _ → tt)
S1Iso = S¹IsoSuspBool ⋄ invIso PushoutSuspIsoSusp

coHomPushout≅coHomSn : (n m : ℕ) → GroupIso (coHomGr m (S₊ (suc n)))
                                             (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
coHomPushout≅coHomSn zero m =
  setTruncIso (domIso S1Iso) ,
  makeIsGroupHom (ST.elim2 (λ _ _ → isSet→isGroupoid isSetSetTrunc _ _) (λ _ _ → refl))
coHomPushout≅coHomSn (suc n) m =
  setTruncIso (domIso (invIso PushoutSuspIsoSusp)) ,
  makeIsGroupHom (ST.elim2 (λ _ _ → isSet→isGroupoid isSetSetTrunc _ _) (λ _ _ → refl))

-------------------------- H⁰(S⁰) -----------------------------
S0→ℤ : (a : ℤ × ℤ) → S₊ 0 → ℤ
S0→ℤ a true = fst a
S0→ℤ a false = snd a

H⁰-S⁰≅ℤ×ℤ : GroupIso (coHomGr 0 (S₊ 0)) (DirProd ℤGroup ℤGroup)
fun (fst H⁰-S⁰≅ℤ×ℤ) = ST.rec (isSet× isSetℤ isSetℤ) λ f → (f true) , (f false)
inv (fst H⁰-S⁰≅ℤ×ℤ) a = ∣ S0→ℤ a ∣₂
rightInv (fst H⁰-S⁰≅ℤ×ℤ) _ = refl
leftInv (fst H⁰-S⁰≅ℤ×ℤ) =
  ST.elim (λ _ → isSet→isGroupoid isSetSetTrunc _ _)
        (λ f → cong ∣_∣₂ (funExt (λ {true → refl ; false → refl})))
snd H⁰-S⁰≅ℤ×ℤ =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isSet→isGroupoid (isSet× isSetℤ isSetℤ) _ _) λ a b → refl)


------------------------- Hⁿ(S⁰) ≅ 0 for n ≥ 1 -------------------------------


private
  Hⁿ-S0≃Kₙ×Kₙ : (n : ℕ) → Iso (S₊ 0 → coHomK (suc n)) (coHomK (suc n) × coHomK (suc n))
  Iso.fun (Hⁿ-S0≃Kₙ×Kₙ n) f = (f true) , (f false)
  Iso.inv (Hⁿ-S0≃Kₙ×Kₙ n) (a , b) true = a
  Iso.inv (Hⁿ-S0≃Kₙ×Kₙ n) (a , b) false = b
  Iso.rightInv (Hⁿ-S0≃Kₙ×Kₙ n) a = refl
  Iso.leftInv (Hⁿ-S0≃Kₙ×Kₙ n) b = funExt λ {true → refl ; false → refl}

  isContrHⁿ-S0 : (n : ℕ) → isContr (coHom (suc n) (S₊ 0))
  isContrHⁿ-S0 n = isContrRetract (Iso.fun (setTruncIso (Hⁿ-S0≃Kₙ×Kₙ n)))
                                  (Iso.inv (setTruncIso (Hⁿ-S0≃Kₙ×Kₙ n)))
                                  (Iso.leftInv (setTruncIso (Hⁿ-S0≃Kₙ×Kₙ n)))
                                  (isContrHelper n)
    where
    isContrHelper : (n : ℕ) → isContr (∥ (coHomK (suc n) × coHomK (suc n)) ∥₂)
    fst (isContrHelper zero) = ∣ (0₁ , 0₁) ∣₂
    snd (isContrHelper zero) = ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                                  λ y → T.elim2 {B = λ x y → ∣ (0₁ , 0₁) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isOfHLevelPlus {n = 2} 2 isSetSetTrunc _ _)
                                  (toPropElim2 (λ _ _ → isSetSetTrunc _ _) refl) (fst y) (snd y)
    isContrHelper (suc zero) = ∣ (0₂ , 0₂) ∣₂
                          , ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                                  λ y → T.elim2 {B = λ x y → ∣ (0₂ , 0₂) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isOfHLevelPlus {n = 2} 3 isSetSetTrunc _ _)
                                  (suspToPropElim2 base (λ _ _ → isSetSetTrunc _ _) refl) (fst y) (snd y)
    isContrHelper (suc (suc n)) = ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂
                          , ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                                  λ y → T.elim2 {B = λ x y → ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isProp→isOfHLevelSuc (4 + n) (isSetSetTrunc _ _))
                                  (suspToPropElim2 north (λ _ _ → isSetSetTrunc _ _) refl) (fst y) (snd y)

Hⁿ-S⁰≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ 0)) UnitGroup₀
Hⁿ-S⁰≅0 n = contrGroupIsoUnit (isContrHⁿ-S0 n)

------------------------- Hⁿ(S¹) ≅ 0 , for n ≥ 2  -------------------------------

Hⁿ-S¹≅0 : (n : ℕ) → GroupIso (coHomGr (2 + n) (S₊ 1)) UnitGroup₀
Hⁿ-S¹≅0 n = contrGroupIsoUnit
            (isOfHLevelRetractFromIso 0 helper
              (_ , helper2))
  where
  helper : Iso ⟨ coHomGr (2 + n) (S₊ 1)⟩ ∥ Σ (hLevelTrunc (4 + n) (S₊ (2 + n))) (λ x → ∥ x ≡ x ∥₂) ∥₂
  helper = compIso (setTruncIso IsoFunSpaceS¹) IsoSetTruncateSndΣ

  helper2 : (x : ∥ Σ (hLevelTrunc (4 + n) (S₊ (2 + n))) (λ x → ∥ x ≡ x ∥₂) ∥₂) → ∣ ∣ north ∣ , ∣ refl ∣₂ ∣₂ ≡ x
  helper2 =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
          (uncurry
            (T.elim (λ _ → isOfHLevelΠ (4 + n) λ _ → isProp→isOfHLevelSuc (3 + n) (isSetSetTrunc _ _))
              (suspToPropElim (ptSn (suc n)) (λ _ → isPropΠ λ _ → isSetSetTrunc _ _)
                (ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                       λ p
                    → cong ∣_∣₂ (ΣPathP (refl , isContr→isProp helper3 _ _))))))
    where
    helper4 : isConnected (n + 3) (hLevelTrunc (4 + n) (S₊ (2 + n)))
    helper4 = subst (λ m → isConnected m (hLevelTrunc (4 + n) (S₊ (2 + n)))) (+-comm 3 n)
                    (isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (3 + n) 1)) (sphereConnected (2 + n)))

    helper3 : isContr ∥ ∣ north ∣ ≡ ∣ north ∣ ∥₂
    helper3 = isOfHLevelRetractFromIso 0 setTruncTrunc2Iso
                                         (isConnectedPath 2 (isConnectedSubtr 3 n helper4) _ _)

--------------- H¹(Sⁿ), n ≥ 2 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupIso (coHomGr 1 (S₊ (2 + n))) UnitGroup₀
H¹-Sⁿ≅0 zero = contrGroupIsoUnit isContrH¹S²
  where
  isContrH¹S² : isContr ⟨ coHomGr 1 (S₊ 2) ⟩
  isContrH¹S² = ∣ (λ _ → ∣ base ∣) ∣₂
              , coHomPointedElim 0 north (λ _ → isSetSetTrunc _ _)
                   λ f p → cong ∣_∣₂ (funExt λ x → sym p ∙∙ sym (spoke f north) ∙∙ spoke f x)
H¹-Sⁿ≅0 (suc n) = contrGroupIsoUnit isContrH¹S³⁺ⁿ
  where
  anIso : Iso ⟨ coHomGr 1 (S₊ (3 + n)) ⟩ ∥ (S₊ (3 + n) → hLevelTrunc (4 + n) (coHomK 1)) ∥₂
  anIso =
    setTruncIso
      (codomainIso
        (invIso (truncIdempotentIso (4 + n) (isOfHLevelPlus' {n = 1 + n} 3 (isOfHLevelTrunc 3)))))

  isContrH¹S³⁺ⁿ-ish : (f : (S₊ (3 + n) → hLevelTrunc (4 + n) (coHomK 1)))
                   → ∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂ ≡ ∣ f ∣₂
  isContrH¹S³⁺ⁿ-ish f = ind-helper (f north) refl
    where
    ind-helper : (x : hLevelTrunc (4 + n) (coHomK 1))
       → x ≡ f north
       → ∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂ ≡ ∣ f ∣₂
    ind-helper = T.elim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPlus' {n = (3 + n)} 1 (isSetSetTrunc _ _))
              (T.elim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 (isSetSetTrunc _ _))
              (toPropElim (λ _ → isPropΠ λ _ → isSetSetTrunc _ _)
              λ p → cong ∣_∣₂ (funExt λ x → p ∙∙ sym (spoke f north) ∙∙ spoke f x)))
  isContrH¹S³⁺ⁿ : isContr ⟨ coHomGr 1 (S₊ (3 + n)) ⟩
  isContrH¹S³⁺ⁿ =
    isOfHLevelRetractFromIso 0
      anIso
      (∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂
      , ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _) isContrH¹S³⁺ⁿ-ish)

--------- H¹(S¹) ≅ ℤ -------
{-
Idea :
H¹(S¹) := ∥ S¹ → K₁ ∥₂
        ≃ ∥ S¹ → S¹ ∥₂
        ≃ ∥ S¹ × ℤ ∥₂
        ≃ ∥ S¹ ∥₂ × ∥ ℤ ∥₂
        ≃ ℤ
-}
H¹-S¹≅ℤ : GroupIso (coHomGr 1 (S₊ 1)) ℤGroup
H¹-S¹≅ℤ = theIso
  where
  F = Iso.fun S¹→S¹≡S¹×ℤ
  F⁻ = Iso.inv S¹→S¹≡S¹×ℤ

  theIso : GroupIso (coHomGr 1 (S₊ 1)) ℤGroup
  fun (fst theIso) = ST.rec isSetℤ (λ f → snd (F f))
  inv (fst theIso) a = ∣ (F⁻ (base , a)) ∣₂
  rightInv (fst theIso) a = cong snd (Iso.rightInv S¹→S¹≡S¹×ℤ (base , a))
  leftInv (fst theIso) =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                          λ f → cong ((ST.rec isSetSetTrunc ∣_∣₂)
                                        ∘ ST.rec isSetSetTrunc λ x → ∣ F⁻ (x , (snd (F f))) ∣₂)
                                      (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (fst (F f))))
                              ∙ cong ∣_∣₂ (Iso.leftInv S¹→S¹≡S¹×ℤ f)
  snd theIso =
    makeIsGroupHom
      (coHomPointedElimS¹2 _ (λ _ _ → isSetℤ _ _)
        λ p q → (λ i → winding (guy ∣ base ∣ (cong S¹map (help p q i))))
              ∙∙ (λ i → winding (guy ∣ base ∣ (congFunct S¹map p q i)))
              ∙∙ winding-hom (guy ∣ base ∣ (cong S¹map p))
                             (guy ∣ base ∣ (cong S¹map q)))
    where
    guy = basechange2⁻ ∘ S¹map
    help : (p q : Path (coHomK 1) ∣ base ∣ ∣ base ∣) → cong₂ _+ₖ_ p q ≡ p ∙ q
    help p q = cong₂Funct _+ₖ_ p q ∙ (λ i → cong (λ x → rUnitₖ 1 x i) p ∙ cong (λ x → lUnitₖ 1 x i) q)



---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------
Hⁿ-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ (suc n))) ℤGroup
Hⁿ-Sⁿ≅ℤ zero = H¹-S¹≅ℤ
Hⁿ-Sⁿ≅ℤ (suc n) = suspensionAx-Sn n n □ Hⁿ-Sⁿ≅ℤ n

-------------- Hⁿ(Sᵐ) ≅ ℤ for n , m ≥ 1 with n ≠ m ----------------
Hⁿ-Sᵐ≅0 : (n m : ℕ) → ¬ (n ≡ m) → GroupIso (coHomGr (suc n) (S₊ (suc m))) UnitGroup₀
Hⁿ-Sᵐ≅0 zero zero pf = ⊥.rec (pf refl)
Hⁿ-Sᵐ≅0 zero (suc m) pf = H¹-Sⁿ≅0 m
Hⁿ-Sᵐ≅0 (suc n) zero pf = Hⁿ-S¹≅0 n
Hⁿ-Sᵐ≅0 (suc n) (suc m) pf = suspensionAx-Sn n m
                           □ Hⁿ-Sᵐ≅0 n m λ p → pf (cong suc p)


-------------- A nice packaging for the Hⁿ-Sⁿ  ----------------

code : (n m : ℕ) → Type ℓ-zero
code  zero    zero   = GroupIso (coHomGr 0 (S₊ 0)) (DirProd ℤGroup ℤGroup)
code  zero   (suc m) = GroupIso (coHomGr 0 (S₊ (suc m))) ℤGroup
code (suc n)  zero   = GroupIso (coHomGr (suc n) (S₊ 0)) UnitGroup₀
code (suc n) (suc m) with (discreteℕ n m)
... | yes p = GroupIso (coHomGr (suc n) (S₊ (suc n))) ℤGroup
... | no ¬p = GroupIso (coHomGr (suc n) (S₊ (suc m))) UnitGroup₀

Hⁿ-Sᵐ : (n m : ℕ) → code n m
Hⁿ-Sᵐ  zero    zero   = H⁰-S⁰≅ℤ×ℤ
Hⁿ-Sᵐ  zero   (suc m) = H⁰-Sⁿ≅ℤ m
Hⁿ-Sᵐ (suc n)  zero   = Hⁿ-S⁰≅0 n
Hⁿ-Sᵐ (suc n) (suc m) with discreteℕ n m
... | yes p = Hⁿ-Sⁿ≅ℤ n
... | no ¬p = Hⁿ-Sᵐ≅0 n m ¬p

-- Test functions
private
  to₁ : coHom 1 S¹ → ℤ
  to₁ = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 0))

  to₂ : coHom 2 (S₊ 2) → ℤ
  to₂ = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 1))

  to₃ : coHom 3 (S₊ 3) → ℤ
  to₃ = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 2))


  from₁ : ℤ → coHom 1 S¹
  from₁ = Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0))

  from₂ : ℤ → coHom 2 (S₊ 2)
  from₂ = Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 1))

  from₃ : ℤ → coHom 3 (S₊ 3)
  from₃ = Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 2))

{-
Strangely, the following won't compute
test₀ : to₂ (from₂ 1 +ₕ from₂ 1) ≡ 2
test₀ = refl
However, the same example works for S¹ ∨ S¹ ∨ S², where the functions are essentially the same as here
(although somewhat more complicated).

But with our new strange addition +'ₕ, it computes just fine:

test₀ : to₂ (from₂ 1 +'ₕ from₂ 1) ≡ 2
test₀ = refl

-}
