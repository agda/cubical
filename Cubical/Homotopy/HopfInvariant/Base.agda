{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.HopfInvariant.Base where

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.SuspensionMap

open import Cubical.Relation.Nullary

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.GradedCommutativity
open import Cubical.ZCohomology.Gysin

open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Truncation
  renaming (rec to trRec)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec)

-- The pushout of the hopf invariant
HopfInvariantPush : (n : ℕ)
             → (f : S₊ (3 +ℕ n +ℕ n) → S₊ (2 +ℕ n))
             → Type _
HopfInvariantPush n f = Pushout (λ _ → tt) f

Hopfα : (n : ℕ)
     → (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
     → coHom (2 +ℕ n) (HopfInvariantPush n (fst f))
Hopfα n f = ∣ (λ { (inl x) → 0ₖ _
                ; (inr x) → ∣ x ∣
                ; (push a i) → help a (~ i)}) ∣₂
  where
  help : (a : S₊ (3 +ℕ n +ℕ n)) → ∣ fst f a ∣ ≡ 0ₖ (2 +ℕ n)
  help = sphereElim _ (λ _ → isOfHLevelPlus' {n = n} (3 +ℕ n)
         (isOfHLevelPath' (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n)) _ _))
                                    (cong ∣_∣ₕ (snd f))

Hopfβ : (n : ℕ)
     → (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
     → coHom (4 +ℕ (n +ℕ n)) (HopfInvariantPush n (fst f))
Hopfβ n f = fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n)) ∣ ∣_∣ ∣₂

-- To define the Hopf invariant, we need to establish the
-- non-trivial isos of Hⁿ(HopfInvariant).
module _ (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n)) where
  module M = MV _ _ _ (λ _ → tt) (fst f)
  ¬lemHopf : (n m : ℕ) → ¬ suc (suc (m +ℕ n)) ≡ suc n
  ¬lemHopf zero zero p = snotz (cong predℕ p)
  ¬lemHopf (suc n) zero p = ¬lemHopf n zero (cong predℕ p)
  ¬lemHopf zero (suc m) p = snotz (cong predℕ p)
  ¬lemHopf (suc n) (suc m) p =
    ¬lemHopf n (suc m) (cong (suc ∘ suc )
      (sym (+-suc m n)) ∙ (cong predℕ p))

  SphereHopfCohomIso :
    GroupEquiv
      (coHomGr (3 +ℕ n +ℕ n) (S₊ (3 +ℕ n +ℕ n)))
      ((coHomGr (suc (3 +ℕ n +ℕ n)) (HopfInvariantPush _ (fst f))))
  fst (fst SphereHopfCohomIso) =
    fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n))
  snd (fst SphereHopfCohomIso) = help
    where
      abstract
        help : isEquiv (fst (MV.d _ _ _ (λ _ → tt) (fst f)
                                 (3 +ℕ n +ℕ n)))
        help =
          SES→isEquiv
            (isContr→≡UnitGroup
              (isContrΣ (GroupIsoUnitGroup→isContr (invGroupIso (Hⁿ-Unit≅0 _)))
                        λ _ → GroupIsoUnitGroup→isContr
                            (invGroupIso (Hⁿ-Sᵐ≅0 _ _ (¬lemHopf n n)))))
            (isContr→≡UnitGroup
              (isContrΣ (GroupIsoUnitGroup→isContr
                        (invGroupIso (Hⁿ-Unit≅0 _)))
                        λ _ → GroupIsoUnitGroup→isContr
                          (invGroupIso (Hⁿ-Sᵐ≅0 _ _ (¬lemHopf n (suc n))))))
              (M.Δ (3 +ℕ n +ℕ n))
              (M.d (3 +ℕ n +ℕ n))
              (M.i (4 +ℕ n +ℕ n))
              (M.Ker-d⊂Im-Δ _)
              (M.Ker-i⊂Im-d _)
  snd SphereHopfCohomIso = d-inv
    where
      -- Currently, type checking is very slow without the abstract flag.
      -- TODO : Remove abstract
      abstract
        d-inv : IsGroupHom (snd (coHomGr (3 +ℕ n +ℕ n) (S₊ (3 +ℕ n +ℕ n))))
                  (fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n)))
                  (snd (coHomGr (suc (3 +ℕ n +ℕ n))
                       (Pushout (λ _ → tt) (fst f))))
        d-inv = snd (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n))

  Hopfβ-Iso : GroupIso (coHomGr (suc (3 +ℕ n +ℕ n))
                                (HopfInvariantPush _ (fst f)))
                       ℤGroup
  fst Hopfβ-Iso = compIso (invIso (equivToIso (fst SphereHopfCohomIso)))
                           (fst (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))
  snd Hopfβ-Iso = grHom
    where
      abstract
        grHom :
          IsGroupHom (coHomGr (suc (3 +ℕ n +ℕ n))
                              (Pushout (λ _ → tt) (fst f)) .snd)
                     (λ x → Iso.fun (fst ((Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n))))))
                       (invEq (fst SphereHopfCohomIso) x))
                     (ℤGroup .snd)
        grHom = snd (compGroupIso
                  (GroupEquiv→GroupIso (invGroupEquiv (SphereHopfCohomIso)))
                  (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))

Hⁿ-Sⁿ≅ℤ-nice-generator : (n : ℕ) → Iso.inv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) 1 ≡ ∣ ∣_∣ ∣₂
Hⁿ-Sⁿ≅ℤ-nice-generator zero = Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ (suc zero))) _
Hⁿ-Sⁿ≅ℤ-nice-generator (suc n) =
  (λ i → Iso.inv (fst (suspensionAx-Sn (suc n) (suc n)))
                  (Hⁿ-Sⁿ≅ℤ-nice-generator n i))
     ∙ cong ∣_∣₂
       (funExt λ { north → refl
                 ; south → cong ∣_∣ₕ (merid north)
                 ; (merid a i) j → ∣ compPath-filler (merid a)
                                      (sym (merid north)) (~ j) i ∣ₕ})

Hopfβ↦1 : (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n))
  → Iso.fun (fst (Hopfβ-Iso n f)) (Hopfβ n f) ≡ 1
Hopfβ↦1 n f =
    sym (cong (Iso.fun (fst (Hopfβ-Iso n f))) lem)
  ∙ Iso.rightInv (fst (Hopfβ-Iso n f)) (pos 1)
  where
  lem : Iso.inv (fst (Hopfβ-Iso n f)) (pos 1) ≡ Hopfβ n f
  lem = (λ i → fst (MV.d _ _ _ (λ _ → tt) (fst f) (3 +ℕ n +ℕ n))
               (Hⁿ-Sⁿ≅ℤ-nice-generator _ i))
    ∙ cong ∣_∣₂ (funExt (λ { (inl x) → refl
                          ; (inr x) → refl
                          ; (push a i) → refl}))

module _ (n : ℕ) (f : S₊∙ (3 +ℕ n +ℕ n) →∙ S₊∙ (2 +ℕ n)) where
  private
    2+n = 2 +ℕ n
    H = HopfInvariantPush n (fst f)

    H→Sphere : coHom 2+n H → coHom 2+n (S₊ (suc (suc n)))
    H→Sphere = sMap (_∘ inr)

    grHom : IsGroupHom (snd (coHomGr 2+n H))
                       H→Sphere (snd (coHomGr 2+n (S₊ (suc (suc n)))))
    grHom =
      makeIsGroupHom
        (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
          λ f g → refl)

    preSphere→H : (g : (S₊ (suc (suc n)) → coHomK 2+n))
                 → H → coHomK (2 +ℕ n)
    preSphere→H g (inl x) = 0ₖ _
    preSphere→H g (inr x) = g x -ₖ g north
    preSphere→H g (push a i) = lem a i
      where
      lem : (a : S₊ (suc (suc (suc (n +ℕ n)))))
          → 0ₖ (suc (suc n)) ≡ g (fst f a) -ₖ g north
      lem =
        sphereElim _
          (λ x → isOfHLevelPlus' {n = n} (3 +ℕ n)
                    (isOfHLevelTrunc (4 +ℕ n) _ _))
                    (sym (rCancelₖ _ (g north))
                     ∙ cong (λ x → g x -ₖ g north) (sym (snd f)))

    Sphere→H : coHom 2+n (S₊ (suc (suc n))) → coHom 2+n H
    Sphere→H = sMap preSphere→H

    conCohom2+n : (x : _) → ∥ x ≡ 0ₖ (suc (suc n)) ∥₁
    conCohom2+n =
      coHomK-elim _ (λ _ → isProp→isOfHLevelSuc (suc n) squash₁) ∣ refl ∣₁

  HIPSphereCohomIso :
    Iso (coHom (2 +ℕ n) (HopfInvariantPush n (fst f)))
        (coHom (2 +ℕ n) (S₊ (2 +ℕ n)))
  Iso.fun HIPSphereCohomIso = H→Sphere
  Iso.inv HIPSphereCohomIso = Sphere→H
  Iso.rightInv HIPSphereCohomIso =
    sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      λ g → pRec (squash₂ _ _)
                  (λ p → cong ∣_∣₂ (funExt λ x → cong (g x +ₖ_) (cong (-ₖ_) p)
                                 ∙ rUnitₖ _ (g x)))
                  (conCohom2+n (g north))
  Iso.leftInv HIPSphereCohomIso =
    sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      λ g →
       pRec (squash₂ _ _)
        (pRec (isPropΠ (λ _ → squash₂ _ _))
         (λ gn gtt →
          trRec (isProp→isOfHLevelSuc n (squash₂ _ _))
            (λ r → cong ∣_∣₂ (funExt λ {
                          (inl x) → sym gtt
                        ; (inr x) → (λ i → g (inr x) -ₖ gn i)
                                    ∙ rUnitₖ _ (g (inr x))
                        ; (push a i)
                          → sphereElim _
                               {A = λ a →
                                 PathP (λ i → preSphere→H (λ x → g (inr x))
                                                            (push a i)
                                      ≡ g (push a i))
                                     (sym gtt)
                                     ((λ i → g (inr (fst f a)) -ₖ gn i)
                                     ∙ rUnitₖ _ (g (inr (fst f a))))}
               (λ _ → isOfHLevelPathP' (suc (suc (suc (n +ℕ n))))
                        (isOfHLevelPath (suc (suc (suc (suc (n +ℕ n)))))
                         (isOfHLevelPlus' {n = n} (suc (suc (suc (suc n))))
                          (isOfHLevelTrunc (suc (suc (suc (suc n)))))) _ _) _ _)
                               r a i}))
                       (push-helper g gtt gn))
               (conCohom2+n (g (inr north))))
             (conCohom2+n (g (inl tt)))
    where
    push-helper : (g : HopfInvariantPush n (fst f) → coHomK (suc (suc n)))
     → (gtt : g (inl tt) ≡ 0ₖ (suc (suc n)))
     → (gn : g (inr north) ≡ 0ₖ (suc (suc n)))
     → hLevelTrunc (suc n)
             (PathP (λ i → preSphere→H (λ x → g (inr x)) (push north i)
                          ≡ g (push north i))
             (sym gtt)
             ((λ i → g (inr (fst f north)) -ₖ gn i)
              ∙ rUnitₖ _ (g (inr (fst f north)))))
    push-helper g gtt gn =
      isConnectedPathP _ (isConnectedPath _ (isConnectedKn _) _ _) _ _ .fst

  Hopfα-Iso : GroupIso (coHomGr (2 +ℕ n) (HopfInvariantPush n (fst f))) ℤGroup
  Hopfα-Iso =
    compGroupIso
      (HIPSphereCohomIso , grHom)
      (Hⁿ-Sⁿ≅ℤ (suc n))

Hopfα-Iso-α : (n : ℕ) (f : _)
            → Iso.fun (fst (Hopfα-Iso n f)) (Hopfα n f)
            ≡ 1
Hopfα-Iso-α n f =
    sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (Hⁿ-Sⁿ≅ℤ-nice-generator n))
  ∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)
  where
  hz : Iso.fun (HIPSphereCohomIso n f) (Hopfα n f) ≡ ∣ ∣_∣ ∣₂
  hz = refl

⌣-α : (n : ℕ) → (f : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → _
⌣-α n f = Hopfα n f ⌣ Hopfα n f

HopfInvariant : (n : ℕ)
             → (f : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
             → ℤ
HopfInvariant n f = Iso.fun (fst (Hopfβ-Iso n f))
  (subst (λ x → coHom x (HopfInvariantPush n (fst f)))
         (λ i → suc (suc (suc (+-suc n n i))))
         (⌣-α n f))

HopfInvariant-π' : (n : ℕ) → π' (3 +ℕ (n +ℕ n)) (S₊∙ (2 +ℕ n)) → ℤ
HopfInvariant-π' n = sRec isSetℤ (HopfInvariant n)

HopfInvariant-π : (n : ℕ) → π (3 +ℕ (n +ℕ n)) (S₊∙ (2 +ℕ n)) → ℤ
HopfInvariant-π n =  sRec isSetℤ λ x → HopfInvariant-π' n ∣ Ω→SphereMap _ x ∣₂


-- Elimination principle for the pushout defining the Hopf Invariant
HopfInvariantPushElim :
       ∀ {ℓ} n → (f : _)
    → {P : HopfInvariantPush n f → Type ℓ}
    → (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))) (P (inl tt)))
    → (e : P (inl tt))
       (g : (x : _) → P (inr x))
       (r : PathP (λ i → P (push north i)) e (g (f north)))
    → (x : _) → P x
HopfInvariantPushElim n f {P = P} hlev e g r (inl x) = e
HopfInvariantPushElim n f {P = P} hlev e g r (inr x) = g x
HopfInvariantPushElim n f {P = P} hlev e g r (push a i₁) = help a i₁
  where
  help : (a : Susp (Susp (S₊ (suc (n +ℕ n)))))
       → PathP (λ i → P (push a i)) e (g (f a))
  help =
    sphereElim _
      (sphereElim _
        (λ _ → isProp→isOfHLevelSuc (suc (suc (n +ℕ n)))
                                      (isPropIsOfHLevel _))
                  (isOfHLevelPathP' (suc (suc (suc (n +ℕ n))))
                    (subst (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))))
                           (cong P (push north))
                           hlev) _ _)) r
