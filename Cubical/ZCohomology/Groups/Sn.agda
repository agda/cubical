{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Prelims

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

Sn-connected : (n : ℕ) (x : typ (S₊∙ (suc n))) → ∥ pt (S₊∙ (suc n)) ≡ x ∥₁
Sn-connected zero = toPropElim (λ _ → propTruncIsProp) ∣ refl ∣₁
Sn-connected (suc zero) = suspToPropElim base (λ _ → propTruncIsProp) ∣ refl ∣₁
Sn-connected (suc (suc n)) = suspToPropElim north (λ _ → propTruncIsProp) ∣ refl ∣₁

H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ zero = H⁰-connected base (Sn-connected 0)
H⁰-Sⁿ≅ℤ (suc n) = H⁰-connected north (Sn-connected (suc n))

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
S0→Int : (a : Int × Int) → S₊ 0 → Int
S0→Int a true = fst a
S0→Int a false = snd a

H⁰-S⁰≅ℤ×ℤ : GroupIso (coHomGr 0 (S₊ 0)) (dirProd intGroup intGroup)
fun (map H⁰-S⁰≅ℤ×ℤ) = sRec (isSet× isSetInt isSetInt) λ f → (f true) , (f false)
isHom (map H⁰-S⁰≅ℤ×ℤ) = sElim2 (λ _ _ → isSet→isGroupoid (isSet× isSetInt isSetInt) _ _)
                                λ a b → refl
inv H⁰-S⁰≅ℤ×ℤ a = ∣ S0→Int a ∣₂
rightInv H⁰-S⁰≅ℤ×ℤ _ = refl
leftInv H⁰-S⁰≅ℤ×ℤ = sElim (λ _ → isSet→isGroupoid setTruncIsSet _ _)
                           λ f → cong ∣_∣₂ (funExt (λ {true → refl ; false → refl}))


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
                                  (suspToPropElim2 base (λ _ _ → setTruncIsSet _ _) refl) (fst y) (snd y)
    isContrHelper (suc (suc n)) = ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂
                          , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                  λ y → elim2 {B = λ x y → ∣ (0ₖ (3 + n) , 0ₖ (3 + n)) ∣₂ ≡ ∣(x , y) ∣₂ }
                                  (λ _ _ → isProp→isOfHLevelSuc (4 + n) (setTruncIsSet _ _))
                                  (suspToPropElim2 north (λ _ _ → setTruncIsSet _ _) refl) (fst y) (snd y)

H¹-S⁰≅0 : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ 0)) trivialGroup
H¹-S⁰≅0 n = IsoContrGroupTrivialGroup (isContrHⁿ-S0 n)

------------------------- H²(S¹) ≅ 0 -------------------------------

Hⁿ-S¹≅0 : (n : ℕ) → GroupIso (coHomGr (2 + n) (S₊ 1)) trivialGroup
Hⁿ-S¹≅0 n = IsoContrGroupTrivialGroup
            (isOfHLevelRetractFromIso 0 helper
              (_ , helper2))
  where
  helper : Iso ⟨ coHomGr (2 + n) (S₊ 1)⟩ ∥ Σ (hLevelTrunc (4 + n) (S₊ (2 + n))) (λ x → ∥ x ≡ x ∥₂) ∥₂
  helper = compIso (setTruncIso IsoFunSpaceS¹) IsoSetTruncateSndΣ

  helper2 : (x : ∥ Σ (hLevelTrunc (4 + n) (S₊ (2 + n))) (λ x → ∥ x ≡ x ∥₂) ∥₂) → ∣ ∣ north ∣ , ∣ refl ∣₂ ∣₂ ≡ x
  helper2 =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          (uncurry
            (trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isProp→isOfHLevelSuc (3 + n) (setTruncIsSet _ _))
              (suspToPropElim (ptSn (suc n)) (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
                (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                       λ p
                    → cong ∣_∣₂ (ΣPathP (refl , isContr→isProp helper3 _ _))))))
    where
    helper4 : isConnected (n + 3) (hLevelTrunc (4 + n) (S₊ (2 + n)))
    helper4 = subst (λ m → isConnected m (hLevelTrunc (4 + n) (S₊ (2 + n)))) (+-comm 3 n)
                    (isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (3 + n) 1)) (sphereConnected (2 + n)))

    helper3 : isContr ∥ ∣ north ∣ ≡ ∣ north ∣ ∥₂
    helper3 = isOfHLevelRetractFromIso 0 setTruncTrunc2Iso
                                         (isConnectedPath 2 (isConnectedSubtr 3 n helper4) _ _)

-- --------------- H¹(Sⁿ), n ≥ 1 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupIso (coHomGr 1 (S₊ (2 + n))) trivialGroup
H¹-Sⁿ≅0 zero = IsoContrGroupTrivialGroup isContrH¹S²
  where
  isContrH¹S² : isContr ⟨ coHomGr 1 (S₊ 2) ⟩
  isContrH¹S² = ∣ (λ _ → ∣ base ∣) ∣₂
              , coHomPointedElim 0 north (λ _ → setTruncIsSet _ _)
                   λ f p → cong ∣_∣₂ (funExt λ x → sym p ∙∙ sym (spoke f north) ∙∙ spoke f x)
H¹-Sⁿ≅0 (suc n) = IsoContrGroupTrivialGroup isContrH¹S³⁺ⁿ
  where
  anIso : Iso ⟨ coHomGr 1 (S₊ (3 + n)) ⟩ ∥ (S₊ (3 + n) → hLevelTrunc (4 + n) (coHomK 1)) ∥₂
  anIso =
    setTruncIso
      (codomainIso
        (invIso (truncIdempotentIso (4 + n) (isOfHLevelPlus' {n = 1 + n} 3 (isOfHLevelTrunc 3)))))

  isContrH¹S³⁺ⁿ-ish : (f : (S₊ (3 + n) → hLevelTrunc (4 + n) (coHomK 1)))
                   → ∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂ ≡ ∣ f ∣₂
  isContrH¹S³⁺ⁿ-ish f = ind (f north) refl
    where
    ind : (x : hLevelTrunc (4 + n) (coHomK 1))
       → x ≡ f north
       → ∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂ ≡ ∣ f ∣₂
    ind = trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPlus' {n = (3 + n)} 1 (setTruncIsSet _ _))
              (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 (setTruncIsSet _ _))
              (toPropElim (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
              λ p → cong ∣_∣₂ (funExt λ x → p ∙∙ sym (spoke f north) ∙∙ spoke f x)))
  isContrH¹S³⁺ⁿ : isContr ⟨ coHomGr 1 (S₊ (3 + n)) ⟩
  isContrH¹S³⁺ⁿ =
    isOfHLevelRetractFromIso 0
      anIso
      (∣ (λ _ → ∣ ∣ base ∣ ∣) ∣₂
      , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) isContrH¹S³⁺ⁿ-ish)

--------- H¹(S¹) ≅ ℤ -------
{-
Idea :
H¹(S¹) := ∥ S¹ → K₁ ∥₂
        ≃ ∥ S¹ → S¹ ∥₂
        ≃ ∥ S¹ × ℤ ∥₂
        ≃ ∥ S¹ ∥₂ × ∥ ℤ ∥₂
        ≃ ℤ
-}
coHom1S1≃ℤ : GroupIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ = theIso
  where
  F = Iso.fun S¹→S¹≡S¹×Int
  F⁻ = Iso.inv S¹→S¹≡S¹×Int

  theIso : GroupIso (coHomGr 1 (S₊ 1)) intGroup
  fun (map theIso) = sRec isSetInt (λ f → snd (F f))
  isHom (map theIso) =
    coHomPointedElimS¹2 _ (λ _ _ → isSetInt _ _)
      λ p q → (λ i → winding (guy ∣ base ∣ (cong S¹map (help p q i))))
            ∙∙ (λ i → winding (guy ∣ base ∣ (congFunct S¹map p q i)))
            ∙∙ winding-hom (guy ∣ base ∣ (cong S¹map p))
                           (guy ∣ base ∣ (cong S¹map q))

    where
    guy = basechange2⁻ ∘ S¹map
    help : (p q : Path (coHomK 1) ∣ base ∣ ∣ base ∣) → cong₂ _+ₖ_ p q ≡ p ∙ q
    help p q = cong₂Funct _+ₖ_ p q ∙ (λ i → cong (λ x → rUnitₖ 1 x i) p ∙ cong (λ x → lUnitₖ 1 x i) q)
  inv theIso a = ∣ (F⁻ (base , a)) ∣₂
  rightInv theIso a = cong snd (Iso.rightInv S¹→S¹≡S¹×Int (base , a))
  leftInv theIso = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                          λ f → cong ((sRec setTruncIsSet ∣_∣₂)
                                        ∘ sRec setTruncIsSet λ x → ∣ F⁻ (x , (snd (F f))) ∣₂)
                                      (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (fst (F f))))
                              ∙ cong ∣_∣₂ (Iso.leftInv S¹→S¹≡S¹×Int f)

---------------------------- Hⁿ(Sⁿ) ≅ ℤ , n ≥ 1 -------------------
{-
The proof of the inductive step below is a compact version of the following equations. Let n ≥ 1.
Hⁿ⁺¹(Sⁿ⁺¹) := ∥ Sⁿ⁺¹ → Kₙ₊₁ ∥₂
           ≅ ∥ Σ[ (a , b) ∈ Kₙ₊₁ ] (Sⁿ → a ≡ b) ∥₂       (characterisation of functions from suspensions)
           ≅ ∥ Kₙ₊₁ × Kₙ₊₁ × (Sⁿ → ΩKₙ₊₁) ∥₂             (base change in ΩKₙ₊₁)
           ≅ ∥ Kₙ₊₁ ∥₂ × ∥ Kₙ₊₁ ∥₂ × ∥ (Sⁿ → ΩKₙ₊₁) ∥₂
           ≅ ∥ Sⁿ → ΩKₙ₊₁ ∥₂                             (connectivity of Kₙ₊₁)
           ≅ ∥ Sⁿ → Kₙ ∥₂                                (ΩKₙ₊₁ ≃ Kₙ)
          := Hⁿ(Sⁿ)
           ≅ ℤ                                           (ind. hyp)

The inverse function Hⁿ(Sⁿ) → Hⁿ⁺¹(Sⁿ⁺¹) is just the function d from Mayer-Vietoris.
However, we can construct d⁻¹ directly in this case, thus avoiding computationally
heavier proofs concerning exact sequences. -}

Hⁿ-Sⁿ≅ℤ : (n : ℕ) → GroupIso (coHomGr (suc n) (S₊ (suc n))) intGroup
Hⁿ-Sⁿ≅ℤ zero = coHom1S1≃ℤ
Hⁿ-Sⁿ≅ℤ (suc n) = invGroupIso helper □ invGroupIso (coHom≅coHomΩ (suc n) _) □ (Hⁿ-Sⁿ≅ℤ n)
  where
  basePointInd : (p : _) (a : _)
    → (p (ptSn (suc n)) ≡ refl) → sym (rCancelₖ (2 + n) ∣ north ∣)
                                 ∙∙ (λ i →  (elimFunSⁿ (suc n) n p) ((merid a ∙ sym (merid (ptSn (suc n)))) i) +ₖ ∣ north ∣)
                                 ∙∙ rCancelₖ (2 + n) ∣ north ∣
                               ≡ p a
  basePointInd p a prefl =
        cong (λ z → sym z ∙∙ ((λ i →  (elimFunSⁿ (suc n) n p) ((merid a ∙ sym (merid (ptSn (suc n)))) i) +ₖ ∣ north ∣)) ∙∙ z)
             (transportRefl refl)
     ∙∙ sym (rUnit _)
     ∙∙ (λ j i → rUnitₖ (2 + n) (elimFunSⁿ (suc n) n p ((merid a ∙ sym (merid (ptSn (suc n)))) i)) j)
     ∙∙ congFunct (elimFunSⁿ (suc n) n p) (merid a) (sym (merid (ptSn (suc n))))
     ∙∙ (cong (p a ∙_) (cong sym prefl)
     ∙ sym (rUnit (p a)))

  helper : GroupIso (coHomGrΩ (suc n) (S₊ (suc n))) (coHomGr (2 + n) (S₊ (2 + n)))
  fun (map helper) = sMap λ f → λ { north → ∣ north ∣
                                   ; south → ∣ north ∣
                                   ; (merid a i) → f a i}
  isHom (map helper) =
    sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
           λ f g → cong ∣_∣₂ (funExt λ { north → refl
                                       ; south → refl
                                       ; (merid a i) j → ∙≡+₂ n (f a) (g a) j i})
  inv helper = sMap λ f x → sym (rCancelₖ (2 + n) (f north))
                          ∙∙ (λ i → f ((merid x ∙ sym (merid (ptSn (suc n)))) i) -ₖ f north)
                          ∙∙ rCancelₖ (2 + n) (f north)
  rightInv helper =
    coHomPointedElimSⁿ (suc n) n (λ _ → setTruncIsSet _ _)
      λ p → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                   (λ prefl → cong ∣_∣₂ (funExt λ {north → refl
                                                 ; south → refl
                                                 ; (merid a i) j → basePointInd p a prefl j i}))
                   (Iso.fun (PathIdTruncIso _)
                            (isOfHLevelSuc 0 (isConnectedPathKn _ ∣ north ∣ ∣ north ∣)
                            (∣ p (ptSn (suc n)) ∣) ∣ refl ∣))
  leftInv helper =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ f → (trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                        (λ frefl → cong ∣_∣₂ (funExt λ x → basePointInd f x frefl))
                        ((Iso.fun (PathIdTruncIso _)
                            (isOfHLevelSuc 0 (isConnectedPathKn _ ∣ north ∣ ∣ north ∣)
                            (∣ f (ptSn (suc n)) ∣) ∣ refl ∣))))
