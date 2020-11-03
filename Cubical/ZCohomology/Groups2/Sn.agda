{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification  #-}
module Cubical.ZCohomology.Groups2.Sn where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties2
open import Cubical.ZCohomology.EilenbergIso
open import Cubical.ZCohomology.Groups2.Unit
open import Cubical.ZCohomology.Groups2.Connected
open import Cubical.ZCohomology.MayerVietoris2
open import Cubical.ZCohomology.Groups2.Prelims

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

loopK-connected : (n : ℕ) → isConnected 2 (loopK (suc n))
loopK-connected n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso' 2 (suc n)))
                                               (isConnectedPath 2
                                                 (isConnectedSubtr 3 n
                                                   (subst (λ m → isConnected m (S₊ (2 + n)))
                                                          (+-comm 3 n)
                                                          (sphereConnected (2 + n)))) _ _)

loopK-nConnected : (n : ℕ) → isConnected (suc n) (loopK n)
loopK-nConnected n =
  isOfHLevelRetractFromIso 0
    (invIso (truncOfTruncIso (suc n) 1))
    (isConnectedPath (suc n) (sphereConnected (suc n)) _ _)

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
                                  (isOfHLevel× 0 (loopK-connected n) (loopK-connected n))

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
    helper4 : (x : loopK (2 + n)) → isConnected 2 (x ≡ x) 
    helper4 x = isConnectedRetractFromIso 2
                   (maybe2 (2 + n) x)
                   (isConnectedPath 2
                   (isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso' _ _))
                   (isConnectedPath 3 (isConnectedSubtr 4 n (subst (λ m → isConnected m (S₊ (3 + n))) (+-comm 4 n) (sphereConnected (3 + n))))
                     _ _)) _ _)

-- --------------- H¹(Sⁿ), n ≥ 1 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupIso (coHomGr 1 (S₊ (2 + n))) trivialGroup
H¹-Sⁿ≅0 zero = IsoContrGroupTrivialGroup isContrH¹S²
  where
  isContrH¹S² : isContr ⟨ coHomGr 1 (S₊ 2) ⟩
  isContrH¹S² = ∣ (λ _ → ∣ refl ∣) ∣₂
              , (coHomPointedElim 0 north
                    (λ _ → setTruncIsSet _ _)
                    λ f p → cong ∣_∣₂ (funExt λ x → sym p ∙∙ sym (spoke f north) ∙∙ spoke f x))
H¹-Sⁿ≅0 (suc n) = IsoContrGroupTrivialGroup isContrH¹S³⁺ⁿ
  where
  anIso : Iso ⟨ coHomGr 1 (S₊ (3 + n)) ⟩ ∥ (S₊ (3 + n) → hLevelTrunc (4 + n) (loopK 1)) ∥₂
  anIso = setTruncIso (codomainIso (invIso (truncIdempotentIso (4 + n) (test2 (isOfHLevelTrunc 3)))))
    where
    test2 : ∀ {ℓ} {A : Type ℓ} → isOfHLevel 3 A → isOfHLevel (4 + n) A
    test2 x = isOfHLevelPlus' {n  = n} 4 (isOfHLevelSuc 3 x)

  isContrH¹S³⁺ⁿ-ish : (f : ⟨ coHomGr 1 (S₊ (3 + n)) ⟩)
                   → ∣ (λ _ → ∣ ∣ refl ∣ ∣) ∣₂ ≡ Iso.fun anIso f
  isContrH¹S³⁺ⁿ-ish =
    coHomPointedElim zero north
                     (λ _ → setTruncIsSet _ _)
                     λ f p → cong ∣_∣₂ (funExt λ x → cong ∣_∣ (sym p) ∙∙ sym (spoke (λ a → ∣ f a ∣) north) ∙∙ spoke (λ a → ∣ f a ∣) x)

  isContrH¹S³⁺ⁿ : isContr ⟨ coHomGr 1 (S₊ (3 + n)) ⟩
  isContrH¹S³⁺ⁿ =
    isOfHLevelRetractFromIso 0
      anIso
      (∣ (λ _ → ∣ ∣ refl ∣ ∣) ∣₂
      , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ f → isContrH¹S³⁺ⁿ-ish (Iso.inv anIso ∣ f ∣₂) ∙ Iso.rightInv anIso ∣ f ∣₂)

-- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

coHom1S1≃ℤ : GroupIso (coHomGr 1 (S₊ 1)) intGroup
coHom1S1≃ℤ = Iso+Hom→GrIso theIso test2
  where
  oki : isProp ∥ loopK 1 ∥₂
  oki = isOfHLevelSuc 0 (isOfHLevelRetractFromIso 0 (setTruncTrunc2Iso) (loopK-nConnected 1))

  helper : Iso (∥ loopK 1 ∥₂ × ∥ Int ∥₂) Int
  Iso.fun helper = uncurry λ _ → sRec isSetInt λ a → a
  Iso.inv helper a = ∣ ∣ refl ∣ ∣₂ , ∣ a ∣₂
  Iso.rightInv helper _ = refl
  Iso.leftInv helper = uncurry λ p → sElim (λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
                               λ a → ΣPathP (oki _ _ , refl)

  theIso : Iso ⟨ coHomGr 1 (S₊ 1) ⟩ Int
  theIso = compIso (setTruncIso nice!TOTAL) (compIso setTruncOfProdIso helper)

  test2 : isGroupHom (coHomGr 1 (S₊ 1)) intGroup (Iso.fun theIso)
  test2 = coHomPointedElim2 0 base base
            (λ _ _ → isSetInt _ _)
            agda
    where
    homHelp : ∀ {ℓ} {A : Pointed ℓ}  (f g : S¹ → loopK 1) →
              (f base ≡ ∣ refl ∣) → (g base ≡ ∣ refl ∣)
           → (F : (x : loopK 1) → (x ≡ x) → pt A ≡ pt A)
           → ((x : loopK 1) → (p q : x ≡ x) → F x (p ∙ q) ≡ F x p ∙ F x q)
           → F (f base +[ 1 ]ₖ g base) (cong (λ x → f x +[ 1 ]ₖ g x) loop)
                                    ≡ F (f base) (cong f loop) ∙ F (g base) (cong g loop)
    homHelp f g fId gId F funct =
         cong (F (f base +[ 1 ]ₖ g base)) (cong₂Funct (λ x y → f x +[ 1 ]ₖ g y) loop loop)
      ∙∙ funct (f base +[ 1 ]ₖ g base) (cong (λ x → (f x) +[ 1 ]ₖ (g base)) loop) (cong (λ x → (f base) +[ 1 ]ₖ (g x)) loop)
      ∙∙ (λ i → F (f base +[ 1 ]ₖ gId i) (cong (λ x → (f x) +[ 1 ]ₖ (gId i)) loop) ∙ F (fId i +[ 1 ]ₖ g base) (cong (λ x → (fId i) +[ 1 ]ₖ (g x)) loop))
      ∙∙ (λ i → F (rUnitₖ 1 (f base) i) (cong (λ x → rUnitₖ 1 (f x) i) loop) ∙ F (lUnitₖ 1 (g base) i) (cong (λ x → lUnitₖ 1 (g x) i) loop))
      ∙∙ refl

    agda : (f g : S¹ → loopK 1) → (f base ≡ coHom'-pt 1) → (g base ≡ coHom'-pt 1)
         → Iso.fun theIso (∣ f ∣₂ +[ 1 ]ₕ ∣ g ∣₂) ≡ (Iso.fun theIso ∣ f ∣₂) +ℤ (Iso.fun theIso ∣ g ∣₂)
    agda f g fId gId = cong (Iso.fun test) (homHelp f g fId gId (λ x → Iso.fun (maybe2 1 x)) (agdaHelp 1))
                          ∙ testFunct (Iso.fun (maybe2 1 (f base)) (cong f loop)) (Iso.fun (maybe2 1 (g base)) (cong g loop))

      where
      agdaHelp : (n : ℕ) → (x : loopK n) (p q : x ≡ x) →
                 Iso.fun (maybe2 n x) (p ∙ q) ≡
                 Iso.fun (maybe2 n x) p ∙ Iso.fun (maybe2 n x) q
      agdaHelp n x p q = cong (Iso.fun (hahah2 n x)) (congFunct (Iso.fun (hahah n x)) p q)
                       ∙ wrapFunct (cong (λ y → -'ₖ-syntax n y x) p) (cong (λ y → -'ₖ-syntax n y x) q) (rCancelₖ n x)

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
