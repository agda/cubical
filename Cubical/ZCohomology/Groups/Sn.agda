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
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec)
open import Cubical.Data.Unit

open import Cubical.Algebra.Group

infixr 31 _□_
_□_ : _
_□_ = compGroupEquiv

open GroupEquiv
open vSES

Sn-connected : (n : ℕ) (x : S₊ (suc n)) → ∥ north ≡ x ∥₁
Sn-connected n = suspToPropRec north (λ _ → propTruncIsProp) ∣ refl ∣₁

H⁰-Sⁿ≅ℤ : (n : ℕ) → GroupEquiv (coHomGr 0 (S₊ (suc n))) intGroup
H⁰-Sⁿ≅ℤ n = H⁰-connected north (Sn-connected n)

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
eq H⁰-S⁰≅ℤ×ℤ =
  isoToEquiv (iso (sRec (isOfHLevelΣ 2 isSetInt λ _ → isSetInt) λ f → (f north) , (f south))
                  (λ a → ∣ S0→Int a ∣₂)
                  (λ _ → refl)
                  (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ f → cong ∣_∣₂ (funExt (λ {north → refl ; south → refl}))))
isHom H⁰-S⁰≅ℤ×ℤ =
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

diagonalIso : ∀ {ℓ ℓ' ℓ''} {A : Group {ℓ}} (B : Group {ℓ'}) {C : Group {ℓ''}}
               (ψ : GroupEquiv (dirProd A A) B) (ϕ : GroupHom B C)
             → isSurjective _ _ ϕ
             → ((x : ⟨ B ⟩) → isInKer B C ϕ x
                                    → ∃[ y ∈ ⟨ A ⟩ ] x ≡ fst (eq ψ) (y , y))
             → ((x : ⟨ B ⟩) → (∃[ y ∈ ⟨ A ⟩ ] x ≡ fst (eq ψ) (y , y))
                                    → isInKer B C ϕ x)
             → GroupEquiv A C
diagonalIso {A = A} B {C = C} ψ ϕ issurj ker→diag diag→ker =
  BijectionIsoToGroupEquiv
    (bij-iso (compGroupHom fstProj (compGroupHom (grouphom (fst (eq ψ)) (isHom ψ)) ϕ))
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
                                                            ∣ (snd (ψ⁻ b)) , refl ∣₁))
                                     ∙∙ sym ((isHom ϕ) _ _))
                                     ∙∙ cong (fun ϕ) (sym ((isHom ψ) _ _)
                                                  ∙∙ cong (equivFun (eq ψ)) (ΣPathP (sym (Group.assoc A _ _ _)
                                                                                     ∙∙ cong (fst (ψ⁻ b) A.+_) (Group.invl A _)
                                                                                     ∙∙ Group.rid A _
                                                                                  , (Group.lid A _)))
                                                  ∙∙ retEq (eq ψ) b)
                                     ∙∙ id ∣₁ })
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
  fun fstProj a = a , 0g A
  isHom fstProj g0 g1 i = (g0 A.+ g1) , Group.lid A (0g A) (~ i)


H¹-S¹≅ℤ : GroupEquiv intGroup (coHomGr 1 (S₊ 1))
H¹-S¹≅ℤ =
    diagonalIso (coHomGr 0 (S₊ 0))
                (invGroupEquiv H⁰-S⁰≅ℤ×ℤ)
                (I.d 0)
                (λ x → I.Ker-i⊂Im-d 0 x
                                     (ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _
                                            , isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                        (λ x inker
                            → pRec propTruncIsProp
                                    (λ {((f , g) , id') → helper x f g id' inker})
                                    ((I.Ker-d⊂Im-Δ 0 ∣ x ∣₂ inker)))))
                ((sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                         λ F surj
                           → pRec (setTruncIsSet _ _)
                                   (λ { (x , id) → I.Im-Δ⊂Ker-d 0 ∣ F ∣₂
                                                      ∣ (∣ (λ _ → x) ∣₂ , ∣ (λ _ → 0) ∣₂) ,
                                                       (cong ∣_∣₂ (funExt (surjHelper x))) ∙ sym id ∣₁ })
                                   surj) )
  □ invGroupEquiv (coHomPushout≅coHomSn 0 1)
  where
  module I = MV Unit Unit (S₊ 0) (λ _ → tt) (λ _ → tt)

  surjHelper :  (x : Int) (x₁ : S₊ 0) → x +ₖ (-ₖ pos 0) ≡ S0→Int (x , x) x₁
  surjHelper x north = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x
  surjHelper x south = cong (x +ₖ_) (-0ₖ) ∙ rUnitₖ x

  helper : (F : S₊ 0 → Int) (f g : ∥ (Unit → Int) ∥₂)
           (id : GroupHom.fun (I.Δ 0) (f , g) ≡ ∣ F ∣₂)
         → isInKer (coHomGr 0 (S₊ 0))
                    (coHomGr 1 (Pushout (λ _ → tt) (λ _ → tt)))
                    (I.d 0)
                    ∣ F ∣₂
         → ∃[ x ∈ Int ] ∣ F ∣₂ ≡ equivFun (invEquiv (eq H⁰-S⁰≅ℤ×ℤ)) (x , x)
  helper F =
    sElim2 (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
           λ f g id inker
             → pRec propTruncIsProp
                     (λ ((a , b) , id2)
                        → sElim2 {B = λ f g → GroupHom.fun (I.Δ 0) (f , g) ≡ ∣ F ∣₂ → _ }
                                  (λ _ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                                  (λ f g id → ∣ (helper2 f g .fst) , (sym id ∙ sym (helper2 f g .snd)) ∣₁)
                                  a b id2)
                     (MV.Ker-d⊂Im-Δ _ _ (S₊ 0) (λ _ → tt) (λ _ → tt) 0 ∣ F ∣₂ inker)
    where
    helper2 : (f g : Unit → Int)
            → Σ[ x ∈ Int ] (equivFun (invEquiv (eq H⁰-S⁰≅ℤ×ℤ))) (x , x)
             ≡ GroupHom.fun (I.Δ 0) (∣ f ∣₂ , ∣ g ∣₂)
    helper2 f g = (f _ +ₖ (-ₖ g _) ) , cong ∣_∣₂ (funExt (λ {north → refl ; south → refl}))

------------------------- H¹(S⁰) ≅ 0 -------------------------------

private
  Hⁿ-S0≃Kₙ×Kₙ : (n : ℕ) → Iso (S₊ 0 → coHomK (suc n)) (coHomK (suc n) × coHomK (suc n))
  Iso.fun (Hⁿ-S0≃Kₙ×Kₙ n) f = (f north) , (f south)
  Iso.inv (Hⁿ-S0≃Kₙ×Kₙ n) (a , b) north = a
  Iso.inv (Hⁿ-S0≃Kₙ×Kₙ n) (a , b) south = b
  Iso.rightInv (Hⁿ-S0≃Kₙ×Kₙ n) a = refl
  Iso.leftInv (Hⁿ-S0≃Kₙ×Kₙ n) b = funExt λ {north → refl ; south → refl}

  isContrHⁿ-S0 : (n : ℕ) → isContr (coHom (suc n) (S₊ 0))
  isContrHⁿ-S0 n =
    transport (λ i → isContr ∥ isoToPath (Hⁿ-S0≃Kₙ×Kₙ n) (~ i) ∥₂)
      (transport (λ i → isContr (isoToPath (setTruncOfProdIso {A = coHomK (suc n)} {B = coHomK (suc n)} ) (~ i)))
         ((∣ 0ₖ ∣₂ , ∣ 0ₖ ∣₂)
         , prodElim (λ _ → isOfHLevelSuc 1 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet) _ _))
            (elim2 (λ _ _ → isProp→isOfHLevelSuc (2 + n) (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet) _ _))
              (suspToPropRec2 north (λ _ _ → isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet) _ _) refl))))

H¹-S⁰≅0 : (n : ℕ) → GroupEquiv (coHomGr (suc n) (S₊ 0)) trivialGroup
H¹-S⁰≅0 n = contrGroup≅trivialGroup (isContrHⁿ-S0 n)

------------------------- H²(S¹) ≅ 0 -------------------------------

H²-S¹≅0 : GroupEquiv (coHomGr 2 (S₊ 1)) trivialGroup
H²-S¹≅0 =
    coHomPushout≅coHomSn 0 2
  □ (invGroupEquiv (vSES→GroupEquiv _ _ vSES-helper))
  □ (H¹-S⁰≅0 0)
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

--------------- H¹(Sⁿ), n ≥ 1 --------------------------------------------

H¹-Sⁿ≅0 : (n : ℕ) → GroupEquiv (coHomGr 1 (S₊ (2 + n))) trivialGroup
H¹-Sⁿ≅0 n = coHomPushout≅coHomSn (1 + n) 1
         □ BijectionIsoToGroupEquiv
            (bij-iso (I.i 1)
                     helper
                     λ x → ∣ 0ₕ , isOfHLevelSuc 0 (isOfHLevelΣ 0 (isContrHⁿ-Unit zero) (λ _ → isContrHⁿ-Unit zero)) _ x ∣₁)
         □ dirProdEquiv (Hⁿ-Unit≅0 zero) (Hⁿ-Unit≅0 zero)
         □ lUnitGroupIso
  where
    module I = MV Unit Unit (S₊ (1 + n)) (λ _ → tt) (λ _ → tt)
    surj-helper : (x : ⟨ coHomGr 0 (S₊ _) ⟩) → isInIm _ _ (I.Δ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
             λ f → ∣ (∣ (λ _ → f north) ∣₂ , 0ₕ)
                   , (cong ∣_∣₂ (funExt (suspToPropRec north
                                         (λ _ → isSetInt _ _)
                                         (cong (f north +ₖ_) -0ₖ  ∙ rUnitₖ (f north))))) ∣₁
    helper : isInjective _ _ (I.i 1)
    helper =
      sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 (setTruncIsSet _ _))  -- useless elimination speeds things up significantly
             λ x inker → pRec (setTruncIsSet _ _)
                              (sigmaElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                          λ a id → sym id ∙ I.Im-Δ⊂Ker-d 0 ∣ a ∣₂ (surj-helper _))
                              (I.Ker-i⊂Im-d 0 ∣ x ∣₂ inker)

--------- Direct proof of H¹(S¹) ≅ ℤ without Mayer-Vietoris -------

-- The strategy is to use the proof that ΩS¹ ≃ ℤ. Since we only have this for S¹ with the base/loop definition
-- we begin with some functions translating between H¹(S₊ 1) and ∥ S¹ → S¹ ∥₀.  The latter type is easy to characterise,
-- by (S¹ → S¹) ≃ S¹ × ℤ (see Cubical.ZCohomology.Groups.Prelims). Truncating this leaves only ℤ, since S¹ is connected.

-- The translation mentioned above uses the basechange function. We use basechange-lemma (Cubical.ZCohomology.Groups.Prelims) to prove the basechange2⁻ preserves
-- path composition (in a more general sense than what is proved in basechange2⁻-morph)

-- We can now give the group equivalence. The first bit is just a big composition of our previously defined translations and is pretty uninteresting.
-- The harder step is proving that the equivalence is a morphism. This relies heavily on the fact that addition the cohomology groups essentially is defined using an
-- application of cong₂, which allows us to use basechange-lemma.

coHom1S1≃ℤ : GroupEquiv (coHomGr 1 (S₊ 1)) intGroup
eq coHom1S1≃ℤ = isoToEquiv theIso
  where
  F = Iso.fun S¹→S¹≡S¹×Int
  F⁻ = Iso.inv S¹→S¹≡S¹×Int
  G = Iso.fun S1→S1≡S¹→S¹
  G⁻ = Iso.inv S1→S1≡S¹→S¹

  theIso : Iso ⟨ coHomGr 1 (S₊ 1) ⟩ ⟨ intGroup ⟩
  Iso.fun theIso = sRec isSetInt (λ f → snd (F (G f)))
  Iso.inv theIso a = ∣ G⁻ (F⁻ (base , a)) ∣₂
  Iso.rightInv theIso a =
      (cong (snd ∘ F) (Iso.rightInv S1→S1≡S¹→S¹ (F⁻ (base , a)))
     ∙ cong snd (Iso.rightInv S¹→S¹≡S¹×Int (base , a)))
  Iso.leftInv theIso =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ f → cong ((sRec setTruncIsSet (λ x → ∣ G⁻ x ∣₂))
                        ∘ sRec setTruncIsSet λ x → ∣ F⁻ (x , (snd (F (G f)))) ∣₂)
                      (Iso.inv PathIdTrunc₀Iso (isConnectedS¹ (fst (F (G f)))))
               ∙∙ cong (∣_∣₂ ∘ G⁻) (Iso.leftInv S¹→S¹≡S¹×Int (G f))
               ∙∙ cong ∣_∣₂ (Iso.leftInv S1→S1≡S¹→S¹ f)
isHom coHom1S1≃ℤ =
  sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _)
           λ f g → (λ i → winding (guy (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))
                                    (λ i → pre-guy (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i))))))))
                 ∙∙ cong winding (helper (f (S¹→S1 base)) (g (S¹→S1 base)) f g refl refl)
                 ∙∙ winding-hom (guy (f north)
                                     (λ i → pre-guy (f (S¹→S1 (loop i)))))
                                (guy (g north)
                                     (λ i → pre-guy (g (S¹→S1 (loop i)))))
  where
  pre-guy = S¹map ∘ trMap S1→S¹
  guy = basechange2⁻ ∘ pre-guy

  helper : (x y : coHomK 1) (f g : S₊ 1 → coHomK 1)
        → (f (S¹→S1 base)) ≡ x
        → (g (S¹→S1 base)) ≡ y
        → (guy (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 base)) ∙ Kn→ΩKn+1 1 (g (S¹→S1 base))))
                (λ i → S¹map (trMap S1→S¹ (ΩKn+1→Kn (Kn→ΩKn+1 1 (f (S¹→S1 (loop i))) ∙ Kn→ΩKn+1 1 (g (S¹→S1 (loop i))))))))
          ≡ (guy (f (S¹→S1 base))
                 (λ i → pre-guy (f (S¹→S1 (loop i)))))
          ∙ (guy (g (S¹→S1 base))
                 (λ i → pre-guy ((g (S¹→S1 (loop i))))))
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
                   ∙ λ j → guy (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 base)) j)
                                (λ i → pre-guy (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (f (S¹→S1 (loop i))) j))
                         ∙ guy (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 base)) j)
                               (λ i → pre-guy (Iso.leftInv (Iso3-Kn-ΩKn+1 1) (g (S¹→S1 (loop i))) j)))



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
  isTrivialLeft theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit n) (fst p) (fst q)
                                        , isOfHLevelSuc 0 (isContrHⁿ-Unit n) (snd p) (snd q))
  isTrivialRight theIso p q = ΣPathP (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (fst p) (fst q)
                                         , isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)) (snd p) (snd q))
  left theIso = I.Δ (suc n)
  right theIso = I.i (2 + n)
  vSES.ϕ theIso = I.d (suc n)
  Ker-ϕ⊂Im-left theIso = I.Ker-d⊂Im-Δ  (suc n)
  Ker-right⊂Im-ϕ theIso = I.Ker-i⊂Im-d (suc n)
