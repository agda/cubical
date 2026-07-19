{-# OPTIONS --lossy-unification #-}
module Cubical.ZCohomology.Groups.RP2 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.RPn.Base

open import Cubical.Homotopy.Connected

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.KleinBottle
open import Cubical.ZCohomology.Groups.Connected

private
  variable
    ℓ : Level
    A : Type ℓ



funSpaceIso-RP² : Iso (RP² → A) (Σ[ x ∈ A ] Σ[ p ∈ x ≡ x ] p ≡ sym p)
Iso.fun funSpaceIso-RP² f = f point , (cong f line , λ i j → f (square i j))
Iso.inv funSpaceIso-RP² (x , p , P) point = x
Iso.inv funSpaceIso-RP² (x , p , P) (line i) = p i
Iso.inv funSpaceIso-RP² (x , p , P) (square i j) = P i j
Iso.rightInv funSpaceIso-RP² (x , p , P) i = x , p , P
Iso.leftInv funSpaceIso-RP² f _ point = f point
Iso.leftInv funSpaceIso-RP² f _ (line i) = f (line i)
Iso.leftInv funSpaceIso-RP² f _ (square i j) = f (square i j)

private
  pathIso : {x : A} {p : x ≡ x} → Iso (p ≡ sym p) (p ∙ p ≡ refl)
  pathIso {p = p} = compIso (congIso (equivToIso (_ , compPathr-isEquiv p)))
                            (pathToIso (cong (p ∙ p ≡_) (lCancel p)))


--- H⁰(RP²) ≅ ℤ ----
connectedRP¹ : (x : RP²) → ∥ point ≡ x ∥₁
connectedRP¹ point = ∣ refl ∣₁
connectedRP¹ (line i) =
  isOfHLevel→isOfHLevelDep 1 {B = λ x → ∥ point ≡ x ∥₁}
    (λ _ → isPropPropTrunc) ∣ refl ∣₁ ∣ refl ∣₁ line i
connectedRP¹ (square i j) = helper i j
  where
  helper : SquareP (λ i j → ∥ point ≡ square i j ∥₁)
                   (isOfHLevel→isOfHLevelDep 1 {B = λ x → ∥ point ≡ x ∥₁}
                     (λ _ → isPropPropTrunc) ∣ refl ∣₁ ∣ refl ∣₁ line)
                   (symP (isOfHLevel→isOfHLevelDep 1 {B = λ x → ∥ point ≡ x ∥₁}
                           (λ _ → isPropPropTrunc) ∣ refl ∣₁ ∣ refl ∣₁ line))
                   refl refl
  helper = toPathP (isOfHLevelPathP 1 isPropPropTrunc _ _ _ _)


H⁰-RP²≅ℤ : GroupIso (coHomGr 0 RP²) ℤGroup
H⁰-RP²≅ℤ = H⁰-connected point connectedRP¹

--- H¹(RP²) ≅ 0 ----
isContr-H¹-RP²-helper : isContr ∥ Σ[ x ∈ coHomK 1 ] Σ[ p ∈ x ≡ x ] p ∙ p ≡ refl ∥₂
fst isContr-H¹-RP²-helper = ∣ 0ₖ 1 , refl , sym (rUnit refl) ∣₂
snd isContr-H¹-RP²-helper =
  ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
    (uncurry
      (T.elim (λ _ → isGroupoidΠ λ _ → isOfHLevelPlus {n = 1} 2 (isSetSetTrunc _ _))
      (toPropElim (λ _ → isPropΠ (λ _ → isSetSetTrunc _ _))
         λ {(p , nilp)
            → cong ∣_∣₂ (ΣPathP (refl , Σ≡Prop (λ _ → isOfHLevelTrunc 3 _ _ _ _)
                                         (rUnit refl
                                       ∙∙ cong (Kn→ΩKn+1 0) (sym (nilpotent→≡0 (ΩKn+1→Kn 0 p)
                                                                                 (sym (ΩKn+1→Kn-hom 0 p p)
                                                                                ∙ cong (ΩKn+1→Kn 0) nilp)))
                                       ∙∙ Iso.rightInv (Iso-Kn-ΩKn+1 0) p)))})))

H¹-RP²≅0 : GroupIso (coHomGr 1 RP²) UnitGroup₀
H¹-RP²≅0 =
  contrGroupIsoUnit
    (isOfHLevelRetractFromIso 0
      (setTruncIso (compIso funSpaceIso-RP²
                            (Σ-cong-iso-snd (λ _ → Σ-cong-iso-snd λ _ → pathIso))))
      isContr-H¹-RP²-helper)

--- H²(RP²) ≅ ℤ/2ℤ ----

Iso-H²-RP²₁ : Iso ∥ Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] p ≡ sym p ∥₂
                  ∥ Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ≡ sym p ∥₂
Iso.fun Iso-H²-RP²₁ =
  ST.rec isSetSetTrunc
    (uncurry
      (T.elim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 2} 2 isSetSetTrunc)
        (sphereElim _ (λ _ → isSetΠ (λ _ → isSetSetTrunc))
          λ p → ∣ fst p , snd p ∣₂)))
Iso.inv Iso-H²-RP²₁ = ST.map λ p → (0ₖ 2) , p
Iso.rightInv Iso-H²-RP²₁ = ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
                           λ _ → refl
Iso.leftInv Iso-H²-RP²₁ =
  ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
    (uncurry (T.elim (λ _ → is2GroupoidΠ λ _ → isOfHLevelPlus {n = 1} 3 (isSetSetTrunc _ _))
      (sphereToPropElim _ (λ _ → isPropΠ (λ _ → isSetSetTrunc _ _))
        λ p → refl)))

Iso-H²-RP²₂ : Iso ∥ Σ[ p ∈ 0ₖ 2 ≡ 0ₖ 2 ] p ≡ sym p ∥₂ Bool
Iso-H²-RP²₂ = compIso (setTruncIso (Σ-cong-iso-snd λ _ → pathIso))
                (compIso Iso-H²-𝕂²₂ testIso)


H²-RP²≅Bool : GroupIso (coHomGr 2 RP²) BoolGroup
H²-RP²≅Bool = invGroupIso (≅Bool (compIso
                                    (compIso (setTruncIso funSpaceIso-RP²)
                                             Iso-H²-RP²₁)
                                    Iso-H²-RP²₂))

-- Higher groups
Hⁿ-RP²Contr : (n : ℕ) → isContr (coHom (3 + n) RP²)
Hⁿ-RP²Contr n =
  subst isContr
    (isoToPath (setTruncIso (invIso (funSpaceIso-RP²))))
    (∣ c ∣₂ , c-id)
  where
  c : Σ[ x ∈ coHomK (3 + n) ] Σ[ p ∈ x ≡ x ] p ≡ sym p
  c = (0ₖ _) , refl , refl

  c-id : (p : ∥ _ ∥₂) → ∣ c ∣₂ ≡ p
  c-id =
    ST.elim (λ _ → isSetPathImplicit)
      (uncurry (coHomK-elim _
        (λ _ → isOfHLevelΠ (3 + n) λ _ → isProp→isOfHLevelSuc (2 + n) (squash₂ _ _))
          (uncurry λ p q →
            T.rec (isProp→isOfHLevelSuc (suc n) (squash₂ _ _)) (λ pp →
              T.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
                (λ qq → cong ∣_∣₂ (ΣPathP (refl , ΣPathP (pp , qq))))
                (isConnectedPathP _ {A = (λ i → pp i ≡ sym (pp i))}
                  (isConnectedPath _
                    (isConnectedPath _ (isConnectedKn (2 + n)) _ _) _ _)
                      refl q .fst))
              (Iso.fun (PathIdTruncIso _)
                (isContr→isProp
                  (isConnectedPath _ (isConnectedKn (2 + n)) _ _) ∣ refl ∣ ∣ p ∣)))))

Hⁿ-RP²≅0 : (n : ℕ) → GroupIso (coHomGr (3 + n) RP²) (UnitGroup₀)
Hⁿ-RP²≅0 n = contrGroupIsoUnit (Hⁿ-RP²Contr n)
