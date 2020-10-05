{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.KcompPrelims
open import Cubical.ZCohomology.Groups.Prelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
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
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁) hiding (map)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit

open import Cubical.Algebra.Group

infixr 31 _□_
_□_ : _
_□_ = compGroupIso

open GroupEquiv
open vSES
open GroupIso
open GroupHom
open BijectionIso

Sn-connected : (n : ℕ) (x : typ (S₊∙ (suc n))) → ∥ pt (S₊∙ (suc n)) ≡ x ∥₁
Sn-connected zero = toPropElim (λ _ → propTruncIsProp) ∣ refl ∣₁
Sn-connected (suc zero) = suspToPropRec base (λ _ → propTruncIsProp) ∣ refl ∣₁
Sn-connected (suc (suc n)) = suspToPropRec north (λ _ → propTruncIsProp) ∣ refl ∣₁

H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ zero = H⁰-connected base (Sn-connected 0)
H⁰-Sⁿ≅ℤ (suc n) = H⁰-connected north (Sn-connected (suc n))

-- -- ----------------------------------------------------------------------

--- We will need to switch between Sⁿ defined using suspensions and using pushouts
--- in order to apply Mayer Vietoris.
open import Cubical.Data.Bool

S1Iso : Iso S¹ (Pushout {A = Bool} (λ _ → tt) λ _ → tt)
S1Iso = S¹IsoSuspBool ⋄ invIso PushoutSuspIsoSusp

coHomPushout≅coHomSn : (n m : ℕ) → GroupIso (coHomGr m (S₊ (suc n))) (coHomGr m (Pushout {A = S₊ n} (λ _ → tt) λ _ → tt))
coHomPushout≅coHomSn zero m =
  Iso+Hom→GrIso (setTruncIso (domIso S1Iso))
                 (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ f g → cong ∣_∣₂ (funExt λ { (inl tt) → refl
                                                      ; (inr tt) → refl
                                                      ; (push a i) → refl}))
coHomPushout≅coHomSn (suc n) m =
  Iso+Hom→GrIso (setTruncIso (domIso (invIso PushoutSuspIsoSusp)))
                 (sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ f g → cong ∣_∣₂ (funExt λ { (inl tt) → refl
                                                      ; (inr tt) → refl
                                                      ; (push a i) → refl}))

-------------------------- H⁰(S⁰) -----------------------------
S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a true = fst a
S0→Int a false = snd a

H⁰-S⁰≅ℤ×ℤ : GroupIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
fun (map H⁰-S⁰≅ℤ×ℤ) = sRec (isOfHLevelΣ 2 isSetInt λ _ → isSetInt) λ f → (f true) , (f false)
isHom (map H⁰-S⁰≅ℤ×ℤ) = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 isSetInt (λ _ → isSetInt)) _ _)
                                λ a b i → addLemma (a true) (b true) i , addLemma (a false) (b false) i
inv H⁰-S⁰≅ℤ×ℤ a = ∣ S0→Int a ∣₂
rightInv H⁰-S⁰≅ℤ×ℤ _ = refl
leftInv H⁰-S⁰≅ℤ×ℤ = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                           λ f → cong ∣_∣₂ (funExt (λ {true → refl ; false → refl}))


-- --------------------------H¹(S¹) -----------------------------------
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
  open Group
  module A = Group A
  module B = Group B
  module C = Group C
  module A×A = Group (dirProd A A)
  module ψ = GroupIso ψ
  module ϕ = GroupHom ϕ
  ψ⁻ = inv ψ

  fstProj : GroupHom A (dirProd A A)
  fun fstProj a = a , 0g A
  isHom fstProj g0 g1 i = (g0 A.+ g1) , Group.lid A (0g A) (~ i)

  bijIso : BijectionIso A C
  map' bijIso = compGroupHom fstProj (compGroupHom (map ψ) ϕ)
  inj bijIso a inker = pRec (isSetCarrier A _ _)
                             (λ {(a' , id) → (cong fst (sym (leftInv ψ (a , 0g A)) ∙∙ cong ψ⁻ id ∙∙ leftInv ψ (a' , a')))
                                           ∙ cong snd (sym (leftInv ψ (a' , a')) ∙∙ cong ψ⁻ (sym id) ∙∙ leftInv ψ (a , 0g A))})
                             (ker→diag _ inker)
  surj bijIso c =
    pRec propTruncIsProp
         (λ { (b , id) → ∣ (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)))
                          , ((sym (Group.rid C _)
                           ∙∙ cong ((fun ϕ) ((fun (map ψ)) (fst (ψ⁻ b) A.+ (A.- snd (ψ⁻ b)) , 0g A)) C.+_)
                                  (sym (diag→ker (fun (map ψ) ((snd (ψ⁻ b)) , (snd (ψ⁻ b))))
                                                  ∣ (snd (ψ⁻ b)) , refl ∣₁))
                           ∙∙ sym ((isHom ϕ) _ _))
                           ∙∙ cong (fun ϕ) (sym ((isHom (map ψ)) _ _)
                                        ∙∙ cong (fun (map ψ)) (ΣPathP (sym (Group.assoc A _ _ _)
                                                                           ∙∙ cong (fst (ψ⁻ b) A.+_) (Group.invl A _)
                                                                           ∙∙ Group.rid A _
                                                                        , (Group.lid A _)))
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

  surjHelper :  (x : Int) (x₁ : S₊ 0) → x -[ 0 ]ₖ (pos 0) ≡ S0→Int (x , x) x₁
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
                        → sElim2 {B = λ f g → GroupHom.fun (K.Δ 0) (f , g) ≡ ∣ F ∣₂ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₁)
                                  a b id2)
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₂ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] (inv H⁰-S⁰≅ℤ×ℤ (x , x))
             ≡ GroupHom.fun (K.Δ 0) (∣ f ∣₂ , ∣ g ∣₂)
    helper2 f g = (f _ -[ 0 ]ₖ g _) , cong ∣_∣₂ (funExt λ {true → refl ; false → refl})

------------------------- H¹(S⁰) ≅ 0 -------------------------------


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
    snd (isContrHelper zero) = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                  λ y → elim2 {B = λ x y → ∣ (0₁ , 0₁) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isOfHLevelPlus {n = 2} 2 setTruncIsSet _ _)
                                  (toPropElim2 (λ _ _ → setTruncIsSet _ _) refl) (fst y) (snd y)
    isContrHelper (suc zero) = ∣ (0₂ , 0₂) ∣₂
                          , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                  λ y → elim2 {B = λ x y → ∣ (0₂ , 0₂) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isOfHLevelPlus {n = 2} 3 setTruncIsSet _ _)
                                  (suspToPropRec2 base (λ _ _ → setTruncIsSet _ _) refl) (fst y) (snd y)
    isContrHelper (suc (suc n)) = ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂
                          , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                  λ y → elim2 {B = λ x y → ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isProp→isOfHLevelSuc (4 + n) (setTruncIsSet _ _))
                                  (suspToPropRec2 north (λ _ _ → setTruncIsSet _ _) refl) (fst y) (snd y)

H¹-S⁰≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ 0)) trivialGroup
H¹-S⁰≅0 n = IsoContrGroupTrivialGroup (isContrHⁿ-S0 n)

------------------------- H²(S¹) ≅ 0 -------------------------------

H²-S¹≅0 : GroupIso (coHomGr 2 (S₊ 1)) trivialGroup
H²-S¹≅0 =
    coHomPushout≅coHomSn 0 2
  □ invGroupIso (vSES→GroupIso _ _ vSES-helper)
  □ H¹-S⁰≅0 0

  where
  module I = MV Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt)
  vSES-helper : vSES (coHomGr 1 (S₊ 0)) (coHomGr 2 (Pushout (λ _ → tt) (λ _ → tt)))
                     _ _
  isTrivialLeft vSES-helper = isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit 0) (λ _ → isContrHⁿ-Unit 0))
  isTrivialRight vSES-helper = isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit 1) (λ _ → isContrHⁿ-Unit 1))
  left vSES-helper = I.Δ 1
  right vSES-helper = I.i 2
  vSES.ϕ vSES-helper = I.d 1
  Ker-ϕ⊂Im-left vSES-helper = I.Ker-d⊂Im-Δ 1
  Ker-right⊂Im-ϕ vSES-helper = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp) -- doesn't terminate without elimination
                                          λ a → I.Ker-i⊂Im-d 1 ∣ a ∣₂

-- --------------- H¹(Sⁿ), n ≥ 1 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupIso (coHomGr 1 (S₊ (2 + n))) trivialGroup
H¹-Sⁿ≅0 zero = coHomPushout≅coHomSn 1 1
             □ BijectionIsoToGroupIso bijIso
             □ dirProdGroupIso (Hⁿ-Unit≅0 0) (Hⁿ-Unit≅0 0)
             □ lUnitGroupIso
  where
  module K = MV Unit Unit (S₊ 1) (λ _ → tt) (λ _ → tt)
  surj-helper : (x : ⟨ coHomGr 0 (S₊ _) ⟩) → isInIm _ _ (K.Δ 0) x
  surj-helper =
    sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f → ∣ (∣ (λ _ → f base) ∣₂ , 0ₕ 0)
                 , (cong ∣_∣₂ (funExt (toPropElim
                                       (λ _ → isSetInt _ _)
                                       (cong (λ x → f base +[ 0 ]ₖ x) (-0ₖ {n = 0})  ∙ rUnitₖ 0 (f base))))) ∣₁
  helper : isInjective _ _ (K.i 1)
  helper =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 (setTruncIsSet _ _))
           λ x inker → pRec (setTruncIsSet _ _)
                            (sigmaElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                        λ a id → sym id ∙ K.Im-Δ⊂Ker-d 0 ∣ a ∣₂ (surj-helper _))
                            (K.Ker-i⊂Im-d 0 ∣ x ∣₂ inker)
  bijIso : BijectionIso (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                                   (dirProd (coHomGr 1 Unit) (coHomGr 1 Unit))
  map' bijIso = K.i 1
  inj bijIso = helper
  surj bijIso x = ∣ 0ₕ _ , isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit zero) (λ _ → isContrHⁿ-Unit 0)) _ x ∣₁
H¹-Sⁿ≅0 (suc n) = coHomPushout≅coHomSn (2 + n) 1
                 □ BijectionIsoToGroupIso bijIso
                 □ dirProdGroupIso (Hⁿ-Unit≅0 0) (Hⁿ-Unit≅0 0)
                 □ lUnitGroupIso
  where
  module K = MV Unit Unit (S₊ (2 + n)) (λ _ → tt) (λ _ → tt)
  surj-helper : (x : ⟨ coHomGr 0 (S₊ _) ⟩) → isInIm _ _ (K.Δ 0) x
  surj-helper =
    sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f → ∣ (∣ (λ _ → f north) ∣₂ , 0ₕ 0)
                 , cong ∣_∣₂ (funExt (suspToPropRec
                                        (masterTheorem n)
                                        (λ _ → isSetInt _ _)
                                        (cong (λ x → f north +[ 0 ]ₖ x) (-0ₖ {n = 0})  ∙ rUnitₖ 0 (f north)))) ∣₁
    where
    masterTheorem : (n : ℕ) → S₊ (suc n)
    masterTheorem zero = base
    masterTheorem (suc n) = north
  helper : isInjective _ _ (K.i 1)
  helper =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 (setTruncIsSet _ _))
           λ x inker → pRec (setTruncIsSet _ _)
                            (sigmaElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                        λ a id → sym id ∙ K.Im-Δ⊂Ker-d 0 ∣ a ∣₂ (surj-helper _))
                            (K.Ker-i⊂Im-d 0 ∣ x ∣₂ inker)
  bijIso : BijectionIso (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                                   (dirProd (coHomGr 1 Unit) (coHomGr 1 Unit))
  map' bijIso = K.i 1
  inj bijIso = helper
  surj bijIso x = ∣ 0ₕ _ , isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit zero) (λ _ → isContrHⁿ-Unit 0)) _ x ∣₁

--------- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

-- The strategy is to use the proof that ΩS¹ ≃ ℤ. Since we only have this for S¹ with the base/loop definition
-- we begin with some functions translating between H¹(S₊ 1) and ∥ S¹ → S¹ ∥₀.  The latter type is easy to characterise,
-- by (S¹ → S¹) ≃ S¹ × ℤ (see Cubical.ZCohomology.Groups.Prelims). Truncating this leaves only ℤ, since S¹ is connected.

-- The translation mentioned above uses the basechange function. We use basechange-lemma (Cubical.ZCohomology.Groups.Prelims) to prove the basechange2⁻ preserves
-- path composition (in a more general sense than what is proved in basechange2⁻-morph)

-- We can now give the group equivalence. The first bit is just a big composition of our previously defined translations and is pretty uninteresting.
-- The harder step is proving that the equivalence is a morphism. This relies heavily on the fact that addition the cohomology groups essentially is defined using an
-- application of cong₂, which allows us to use basechange-lemma.

coHom1S1≃ℤ : GroupIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ = theIso
  where
  F = Iso.fun S¹→S¹≡S¹×Int
  F⁻ = Iso.inv S¹→S¹≡S¹×Int

  theIso : GroupIso (coHomGr 1 (S₊ 1)) intGroup
  fun (map theIso) = sRec isSetInt (λ f → snd (F f))
  isHom (map theIso) = sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
                              λ f g → ((λ i → winding (guy (ΩKn+1→Kn 1 (Kn→ΩKn+1 1 (f base) ∙ Kn→ΩKn+1 1 (g base)))
                                              (λ i → S¹map (ΩKn+1→Kn 1 (Kn→ΩKn+1 1 (f (loop i)) ∙ Kn→ΩKn+1 1 (g (loop i))))))))
                                   ∙∙ cong winding (helper (f base) (g base) f g refl refl)
                                   ∙∙ winding-hom (guy (f base) (λ i → S¹map (f (loop i))))
                                                  (guy (g base) (λ i → S¹map (g (loop i))))
    where
    guy = basechange2⁻ ∘ S¹map

    helper : (x y : coHomK 1) (f g : S₊ 1 → coHomK 1)
           → (f base) ≡ x
           → (g base) ≡ y
           → (guy (ΩKn+1→Kn 1 (Kn→ΩKn+1 1 (f base) ∙ Kn→ΩKn+1 1 (g base)))
                   (λ i → S¹map ((ΩKn+1→Kn 1 (Kn→ΩKn+1 1 (f (loop i)) ∙ Kn→ΩKn+1 1 (g (loop i)))))))
             ≡ (guy (f base)
                    (λ i → S¹map (f (loop i))))
             ∙ (guy (g base)
                    (λ i → S¹map ((g (loop i)))))
    helper =
      elim2 (λ _ _ → isGroupoidΠ4 λ _ _ _ _ → isOfHLevelPath 3 (isOfHLevelSuc 3 (isGroupoidS¹) base base) _ _)
            (toPropElim2
              (λ _ _ → isPropΠ4 λ _ _ _ _ → isGroupoidS¹ _ _ _ _)
              λ f g reflf reflg →
              basechange-lemma base base
                (S¹map ∘ (ΩKn+1→Kn 1))
                ((Kn→ΩKn+1 1) ∘ f) ((Kn→ΩKn+1 1) ∘ g)
                (cong (Kn→ΩKn+1 1) reflf ∙ Kn→ΩKn+10ₖ 1) (cong (Kn→ΩKn+1 1) reflg ∙ Kn→ΩKn+10ₖ 1)
              ∙ λ j → guy (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f base) j)
                          (λ i → S¹map (Iso.leftInv (Iso-Kn-ΩKn+1 1) (f (loop i)) j))
                    ∙ guy (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g base) j)
                          (λ i → S¹map (Iso.leftInv (Iso-Kn-ΩKn+1 1) (g (loop i)) j)))
  inv theIso a = ∣ (F⁻ (base , a)) ∣₂
  rightInv theIso a = cong snd (Iso.rightInv S¹→S¹≡S¹×Int (base , a))
  leftInv theIso = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                          λ f → cong ((sRec setTruncIsSet ∣_∣₂)
                                        ∘ sRec setTruncIsSet λ x → ∣ F⁻ (x , (snd (F f))) ∣₂)
                                      (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (fst (F f))))
                              ∙ cong ∣_∣₂ (Iso.leftInv S¹→S¹≡S¹×Int f)

---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------

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
