{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.CohomologyGroups where

open import Cubical.Experiments.ZCohomologyOld.Base
open import Cubical.Experiments.ZCohomologyOld.Properties
open import Cubical.Experiments.ZCohomologyOld.MayerVietorisUnreduced
open import Cubical.Experiments.ZCohomologyOld.Groups.Unit
open import Cubical.Experiments.ZCohomologyOld.KcompPrelims
open import Cubical.Experiments.ZCohomologyOld.Groups.Sn

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
  hiding (map)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
  hiding (map)

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Int

open import Cubical.Algebra.Group

open GroupIso
open GroupHom
open BijectionIso

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

  surjHelper :  (x : Int) (x₁ : S₊ 0) → x -[ 0 ]ₖ 0 ≡ S0→Int (x , x) x₁
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
