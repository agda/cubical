{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.HopfInvariant.Homomorphism where

open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity
open import Cubical.Relation.Nullary
open import Cubical.ZCohomology.Gysin

open import Cubical.Functions.Embedding

open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Homotopy.HomotopyGroup

open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Cubical.Data.Sum
open import Cubical.Data.Fin
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup) hiding (Bool)
open import Cubical.Algebra.Group.ZModule

open import Cubical.HITs.Pushout.Flattening
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap ; elim3 to sElim3)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)

open import Cubical.Algebra.AbGroup

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Join

open import Cubical.Homotopy.Hopf

open import Cubical.HITs.SetQuotients renaming (_/_ to _/'_)


open import Cubical.Experiments.Brunerie
open import Cubical.HITs.Hopf

open import Cubical.HITs.Join

open import Cubical.HITs.Wedge

-- probably to be moved to Wedge

∨→∙ : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ}
   → (f g : S₊∙ n →∙ A) → ((S₊∙ n) ⋁ (S₊∙ n) , inl (ptSn _)) →∙ A
fst (∨→∙ {A = A} f g) = f ∨→ g
snd (∨→∙ {A = A} f g) = snd f

C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
C* n f g = Pushout (λ _ → tt) (fst (∨→∙ f g))

C·Π : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
C·Π n f g = Pushout (λ _ → tt) (∙Π f g .fst)

θ : ∀ {ℓ} {A : Pointed ℓ} → Susp (fst A)
  → (Susp (fst A) , north) ⋁ (Susp (fst A) , north)
θ north = inl north
θ south = inr north
θ {A = A} (merid a i₁) =
     ((λ i → inl ((merid a ∙ sym (merid (pt A))) i))
  ∙∙ push tt
  ∙∙ λ i → inr ((merid a ∙ sym (merid (pt A))) i)) i₁

-- move to path

doubleCompPath≡compPath : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
        → p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r
doubleCompPath≡compPath {x = x} {y = y} {z = z} {w = w} =
  J (λ y p → (q : y ≡ z) (r : z ≡ w) →
      (p ∙∙ q ∙∙ r) ≡ p ∙ q ∙ r)
     λ q r → lUnit (q ∙ r)


∙Π≡∨→∘θ : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
   → (x : _) → ∙Π f g .fst x ≡ (f ∨→ g) (θ {A = S₊∙ _} x)
∙Π≡∨→∘θ n f g north = sym (snd f)
∙Π≡∨→∘θ n f g south = sym (snd g)
∙Π≡∨→∘θ n f g (merid a i₁) j = main j i₁
  where
  help : cong (f ∨→ g) (cong (θ {A = S₊∙ _}) (merid a))
       ≡ (refl ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
       ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ refl) 
  help = cong-∙∙ (f ∨→ g) ((λ i → inl ((merid a ∙ sym (merid north)) i)))
                           (push tt)
                           (λ i → inr ((merid a ∙ sym (merid north)) i))
      ∙∙ doubleCompPath≡compPath _ _ _
      ∙∙ cong (cong (f ∨→ g)
              (λ i₂ → inl ((merid a ∙ (λ i₃ → merid north (~ i₃))) i₂)) ∙_)
              (sym (assoc _ _ _))
      ∙∙ assoc _ _ _
      ∙∙ cong₂ _∙_ refl (compPath≡compPath' _ _)

  main : PathP (λ i → snd f (~ i) ≡ snd g (~ i)) (λ i₁ → ∙Π f g .fst (merid a i₁))
               λ i₁ → (f ∨→ g) (θ {A = S₊∙ _} (merid a i₁))
  main = (λ i → ((λ j → snd f (~ i ∧ ~ j)) ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
                ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ λ j → snd g (~ i ∧ j)))
       ▷ sym help

private
  WedgeElim : ∀ {ℓ} (n : ℕ)
              {P : S₊∙ (3 +ℕ (n +ℕ n)) ⋁ S₊∙ (3 +ℕ (n +ℕ n)) → Type ℓ}
            → ((x : _) → isOfHLevel (3 +ℕ n) (P x))
            → P (inl north)
            → (x : _) → P x
  WedgeElim n {P = P} x s (inl x₁) =
    sphereElim _ {A = P ∘ inl}
      (λ _ → isOfHLevelPlus' {n = n} (3 +ℕ n) (x _)) s x₁
  WedgeElim n {P = P} x s (inr x₁) =
    sphereElim _ {A = P ∘ inr}
      (sphereElim _ (λ _ → isProp→isOfHLevelSuc ((suc (suc (n +ℕ n))))
        (isPropIsOfHLevel (suc (suc (suc (n +ℕ n))))))
          (subst (isOfHLevel ((3 +ℕ n) +ℕ n)) (cong P (push tt))
            (isOfHLevelPlus' {n = n} (3 +ℕ n) (x _))))
          (subst P (push tt) s) x₁
  WedgeElim n {P = P} x s (push a j) = transp (λ i → P (push tt (i ∧ j))) (~ j) s

H²C*≅ℤ : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
     → GroupIso (coHomGr (2 +ℕ n) (C* n f g)) ℤGroup
H²C*≅ℤ n f g = compGroupIso groupIso1 (Hⁿ-Sⁿ≅ℤ (suc n))
  where
  help : (coHom (2 +ℕ n) (C* n f g)) → coHom (2 +ℕ n) (S₊ (2 +ℕ n))
  help = sMap λ f → f ∘ inr


  invMapPrim : (S₊ (2 +ℕ n) → coHomK (2 +ℕ n)) → C* n f g → coHomK (2 +ℕ n)
  invMapPrim h (inl x) = h (ptSn _)
  invMapPrim h (inr x) = h x
  invMapPrim h (push a i₁) = WedgeElim n {P = λ a → h north ≡ h (fst (∨→∙ f g) a)}
                                               (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
                                               (cong h (sym (snd f))) a i₁

  invMap : coHom (2 +ℕ n) (S₊ (2 +ℕ n)) → (coHom (2 +ℕ n) (C* n f g))
  invMap = sMap invMapPrim

  ret1 : (x : coHom (2 +ℕ n) (S₊ (2 +ℕ n))) → help (invMap x) ≡ x
  ret1 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
               λ a → refl

  ret2 : (x : (coHom (2 +ℕ n) (C* n f g))) → invMap (help x) ≡ x
  ret2 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
               λ h → cong ∣_∣₂ (funExt λ { (inl x) → cong h ((λ i →  inr ((snd f) (~ i)))
                                                           ∙ sym (push (inl north)))
                                         ; (inr x) → refl
                                         ; (push a i₁) → help2 h a i₁})
    where
    help2 : (h : C* n f g → coHomK (2 +ℕ n))
          → (a : _) → PathP (λ i → invMapPrim (h ∘ inr) (push a i) ≡ h (push a i))
                  (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
                  refl
    help2 h = WedgeElim n (λ _ → isOfHLevelPathP (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
                        help4

      where
      help4 : PathP (λ i → invMapPrim (h ∘ inr) (push (inl north) i) ≡ h (push (inl north) i))
                  (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
                  refl
      help4 i j = h (hcomp (λ k → λ { (i = i1) → inr (fst f north)
                                     ; (j = i0) → inr (snd f (~ i))
                                     ; (j = i1) → push (inl north) (i ∨ ~ k)})
                           (inr (snd f (~ i ∧ ~ j))))

  groupIso1 : GroupIso ((coHomGr (2 +ℕ n) (C* n f g))) (coHomGr (2 +ℕ n) (S₊ (2 +ℕ n)))
  Iso.fun (fst groupIso1) = help
  Iso.inv (fst groupIso1) = invMap
  Iso.rightInv (fst groupIso1) = ret1
  Iso.leftInv (fst groupIso1) = ret2
  snd groupIso1 = makeIsGroupHom
    (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
           λ f g → refl)

H⁴-C·Π : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
        → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C·Π n f g))
                    ℤGroup
H⁴-C·Π n f g = compGroupIso
  (transportCohomIso (cong (3 +ℕ_) (+-suc n n))) (Hopfβ-Iso n (∙Π f g))

H²-C·Π : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
      → GroupIso (coHomGr (2 +ℕ n) (C·Π n f g))
                  ℤGroup
H²-C·Π n f g = Hopfα-Iso n (∙Π f g)


H⁴-C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
     → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
                 (DirProd ℤGroup ℤGroup)
H⁴-C* n f g =
  compGroupIso (GroupEquiv→GroupIso (invGroupEquiv fstIso))
                  (compGroupIso (transportCohomIso (cong (2 +ℕ_) (+-suc n n)))
                    (compGroupIso (Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) _)
                      (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ _) (Hⁿ-Sⁿ≅ℤ _))))
  where
  module Ms = MV _ _ _ (λ _ → tt) (fst (∨→∙ f g))
  fstIso : GroupEquiv (coHomGr ((suc (suc (n +ℕ suc n)))) (S₊∙ (3 +ℕ (n +ℕ n)) ⋁ S₊∙ (3 +ℕ (n +ℕ n))))
                      (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
  fst (fst fstIso) = Ms.d (suc (suc (n +ℕ suc n))) .fst
  snd (fst fstIso) =
    SES→isEquiv
      (GroupPath _ _ .fst (compGroupEquiv (invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl)
                          (GroupEquivDirProd
                            (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
                            (GroupIso→GroupEquiv
                              (invGroupIso
                                (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lemHopf 0 ((λ _ → north) , refl) n n (cong suc (sym (+-suc n n)) ∙ p)))))))
      (GroupPath _ _ .fst
        (compGroupEquiv ((invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl))
            ((GroupEquivDirProd
                            (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
                            (GroupIso→GroupEquiv
                              (invGroupIso (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lemHopf 0 ((λ _ → north) , refl) n (suc n) (cong (2 +ℕ_) (sym (+-suc n n)) ∙ p))))))))
      (Ms.Δ (suc (suc (n +ℕ suc n))))
      (Ms.d (suc (suc (n +ℕ suc n))))
      (Ms.i (suc (suc (suc (n +ℕ suc n)))))
      (Ms.Ker-d⊂Im-Δ _)
      (Ms.Ker-i⊂Im-d _)
  snd fstIso = Ms.d (suc (suc (n +ℕ suc n))) .snd

module _ (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) where

  C·Π' = C·Π n f g

  -- The generators of the cohomology groups of C* and C·Π

  βₗ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
  βₗ = Iso.inv (fst (H⁴-C* n f g)) (1 , 0)

  βᵣ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
  βᵣ = Iso.inv (fst (H⁴-C* n f g)) (0 , 1)

  β·Π : coHom ((2 +ℕ n) +' (2 +ℕ n)) C·Π'
  β·Π = Iso.inv (fst (H⁴-C·Π n f g)) 1

  α* : coHom (2 +ℕ n) (C* n f g)
  α* = Iso.inv (fst (H²C*≅ℤ n f g)) 1

  -- They can be difficult to work with in this form.
  -- We give them simpler forms and prove that these are equivalent
  βᵣ'-fun : C* n f g → coHomK ((4 +ℕ (n +ℕ n)))
  βᵣ'-fun (inl x) = 0ₖ _
  βᵣ'-fun (inr x) = 0ₖ _
  βᵣ'-fun (push (inl x) i₁) = 0ₖ _
  βᵣ'-fun (push (inr x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
  βᵣ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ (~ i₂) i₁

  βₗ'-fun : C* n f g → coHomK (4 +ℕ (n +ℕ n))
  βₗ'-fun (inl x) = 0ₖ _
  βₗ'-fun (inr x) = 0ₖ _
  βₗ'-fun (push (inl x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
  βₗ'-fun (push (inr x) i₁) = 0ₖ _
  βₗ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ i₂ i₁

  βₗ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
  βₗ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
                   ∣ βₗ'-fun ∣₂

  βᵣ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
  βᵣ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
                   ∣ βᵣ'-fun ∣₂

  private
    pp : (a : _) → 0ₖ (suc (suc n)) ≡ ∣ (f ∨→ g) a ∣
    pp = WedgeElim _ (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
                   (cong ∣_∣ₕ (sym (snd f)))

  pp-inr : pp (inr north) ≡ cong ∣_∣ₕ (sym (snd g))
  pp-inr = (λ j → transport (λ i →  0ₖ (2 +ℕ n) ≡ ∣ compPath-filler' (snd f) (sym (snd g)) (~ j) i ∣ₕ)
                             λ i → ∣ snd f (~ i ∨ j) ∣ₕ)
         ∙ λ j → transp (λ i → 0ₖ (2 +ℕ n) ≡ ∣ snd g (~ i ∧ ~ j) ∣ₕ) j λ i → ∣ snd g (~ i ∨ ~ j) ∣ₕ

  α*'-fun : C* n f g → coHomK (2 +ℕ n)
  α*'-fun (inl x) = 0ₖ _
  α*'-fun (inr x) = ∣ x ∣
  α*'-fun (push a i₁) = pp a i₁

  α*' : coHom (2 +ℕ n) (C* n f g)
  α*' = ∣ α*'-fun ∣₂

  -- We also need the following three maps
  jₗ : HopfInvariantPush n (fst f) → C* n f g
  jₗ (inl x) = inl x
  jₗ (inr x) = inr x
  jₗ (push a i₁) = push (inl a) i₁

  jᵣ : HopfInvariantPush n (fst g) → C* n f g
  jᵣ (inl x) = inl x
  jᵣ (inr x) = inr x
  jᵣ (push a i₁) = push (inr a) i₁

  q : C·Π' → C* n f g
  q (inl x) = inl x
  q (inr x) = inr x
  q (push a i₁) = (push (θ a) ∙ λ i → inr (∙Π≡∨→∘θ n f g a (~ i))) i₁

α*↦1 : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
        → Iso.fun (fst (H²C*≅ℤ n f g)) (α*' n f g) ≡ 1
α*↦1 n f g = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (Hⁿ-Sⁿ≅ℤ-nice-generator n))
             ∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)

α*-lem : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
        → α* n f g ≡ α*' n f g
α*-lem n f g = sym (Iso.leftInv (fst (H²C*≅ℤ n f g)) _)
             ∙∙ cong (Iso.inv (fst (H²C*≅ℤ n f g))) help
             ∙∙ Iso.leftInv (fst (H²C*≅ℤ n f g)) _
  where
  help : Iso.fun (fst (H²C*≅ℤ n f g)) (α* n f g) ≡ Iso.fun (fst (H²C*≅ℤ n f g)) (α*' n f g)
  help = (Iso.rightInv (fst (H²C*≅ℤ n f g)) (pos 1)) ∙ sym (α*↦1 n f g)

q-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (q n f g) (α* n f g) ≡ Hopfα n (∙Π f g)
q-α n f g = (λ i → coHomFun _ (q n f g) (α*-lem n f g i))
          ∙ sym (Iso.leftInv is _)
          ∙∙ cong (Iso.inv is) help
          ∙∙ Iso.leftInv is _
  where
  is = fst (Hopfα-Iso n (∙Π f g))

  help : Iso.fun is (coHomFun _ (q n f g) (α*' n f g))
       ≡ Iso.fun is (Hopfα n (∙Π f g))
  help = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (Hⁿ-Sⁿ≅ℤ-nice-generator n))
      ∙∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)
      ∙∙ sym (Hopfα-Iso-α n (∙Π f g))


βₗ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → βₗ n f g ≡ βₗ''-fun n f g
βₗ≡ n f g = cong (FF ∘ subber2)
                 (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
                                            (S₊∙ (suc (suc (suc (n +ℕ n)))))
                                (((suc (suc (n +ℕ n))))))))) help
               ∙ help2)
          ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
          ∙ cong subber3 (sym βₗ'-fun≡)
  where
  FF = MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) (suc (suc (n +ℕ suc n))) .fst
  FF' = MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) (suc (suc (suc (n +ℕ n)))) .fst

  help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (1 , 0)
       ≡ (∣ ∣_∣ ∣₂ , 0ₕ _)
  help = ΣPathP ((Hⁿ-Sⁿ≅ℤ-nice-generator _) , IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))))

  subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

  subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
                               (sym (cong (2 +ℕ_) (+-suc n n))))

  FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
  FF∘subber =
    funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
                   (MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) ((suc (suc (+-suc n n j)))) .fst
                      (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
                                            (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
                              a))))

  wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
       coHomK (suc (suc (suc (n +ℕ n)))))
  wedgeGen (inl x) = ∣ x ∣
  wedgeGen (inr x) = 0ₖ _
  wedgeGen (push a i₁) = 0ₖ _

  βₗ'-fun≡ : ∣ βₗ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
  βₗ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
                                ; (inr x) → refl
                                ; (push (inl x) i₁) → refl
                                ; (push (inr x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
                                ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ i₂) i₁})

  help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
                   (∣ ∣_∣ ∣₂ , 0ₕ _)
                   ≡ ∣ wedgeGen ∣₂
  help2 = cong ∣_∣₂ (funExt λ { (inl x) → rUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
                             ; (inr x) → refl
                             ; (push a i₁) → refl})

βᵣ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → βᵣ n f g ≡ βᵣ''-fun n f g
βᵣ≡ n f g =
    cong (FF ∘ subber2)
      (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
                                            (S₊∙ (suc (suc (suc (n +ℕ n)))))
                                (((suc (suc (n +ℕ n)))))))))
            help
          ∙ help2)
  ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
  ∙ cong (subber3) (sym βᵣ'-fun≡)
  where
  FF = MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) (suc (suc (n +ℕ suc n))) .fst
  FF' = MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) (suc (suc (suc (n +ℕ n)))) .fst

  help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (0 , 1)
       ≡ (0ₕ _ , ∣ ∣_∣ ∣₂)
  help = ΣPathP (IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) , (Hⁿ-Sⁿ≅ℤ-nice-generator _))

  subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

  subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
                               (sym (cong (2 +ℕ_) (+-suc n n))))

  FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
  FF∘subber =
    funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
                   (MV.d _ _ _ (λ _ → tt) (fst (∨→∙ f g)) ((suc (suc (+-suc n n j)))) .fst
                      (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
                                            (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
                              a))))

  wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
       coHomK (suc (suc (suc (n +ℕ n)))))
  wedgeGen (inl x) = 0ₖ _
  wedgeGen (inr x) = ∣ x ∣
  wedgeGen (push a i₁) = 0ₖ _


  help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
                   (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
                   (0ₕ _ , ∣ ∣_∣ ∣₂)
                   ≡ ∣ wedgeGen ∣₂
  help2 = cong ∣_∣₂ (funExt λ { (inl x) → refl
                             ; (inr x) → lUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
                             ; (push a i₁) → refl})

  βᵣ'-fun≡ : ∣ βᵣ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
  βᵣ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
                                ; (inr x) → refl
                                ; (push (inl x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
                                ; (push (inr x) i₁) → refl
                                ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ ~ i₂) i₁})

q-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (q n f g) (βₗ n f g)
    ≡ β·Π n f g
q-βₗ n f g = cong (coHomFun _ (q n f g)) (βₗ≡ n f g)
           ∙ transportLem
           ∙ cong (subst (λ m → coHom m (C·Π' n f g))
                  (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
                        (sym (Iso.leftInv (fst (Hopfβ-Iso n (∙Π f g))) (Hopfβ n (∙Π f g)))
                        ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (∙Π f g))))) (Hopfβ↦1 n (∙Π f g)))
  where
  transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
      (βₗ''-fun n f g)
     ≡ subst (λ m → coHom m (C·Π' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
             (Hopfβ n (∙Π f g))
  transportLem =
      natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
    ∙ cong (subst (λ m → coHom m (C·Π' n f g))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
        (cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → loll a i₁}))
    where
    open import Cubical.Foundations.Path
    loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
      PathP
      (λ i₁ →
         βₗ'-fun n f g ((push (θ x) ∙ λ i → inr (∙Π≡∨→∘θ n f g x (~ i))) i₁) ≡
         MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
         (λ _ → tt) (fst (∙Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
      (λ _ → βₗ'-fun n f g (q n f g (inl tt)))
      (λ _ → βₗ'-fun n f g (q n f g (inr (∙Π f g .fst x))))
    loll x =
      flipSquare (cong-∙ (βₗ'-fun n f g) (push (θ x)) (λ i → inr (∙Π≡∨→∘θ n f g x (~ i)))
              ∙∙ sym (rUnit _)
              ∙∙ lem₁ x)

      where
      lem₁ : (x : _) → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
      lem₁ north = refl
      lem₁ south = sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
      lem₁ (merid a j) k = lala k j
        where
        lala : PathP (λ k → Kn→ΩKn+1 _ ∣ north ∣ₕ ≡ (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
                     (λ j → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
                     (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
        lala = (cong-∙∙ (cong (βₗ'-fun n f g) ∘ push)
                        ((λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
                        (push tt)
                        ((λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
                        ∙ sym (compPath≡compPath' _ _)
                        ∙ (λ _ → (λ j → Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∣ (merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) j ∣ₕ)
                               ∙ Kn→ΩKn+10ₖ _)
                        ∙ cong (_∙ Kn→ΩKn+10ₖ _) (cong-∙ ((Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ))
                               (merid a) (sym (merid north)))
                        ∙ sym (assoc _ _ _)
                        ∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) ∙_)
                               (sym (symDistr (sym ((Kn→ΩKn+10ₖ _))) (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))))))
                        ◁ λ i j → compPath-filler (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
                                                    (sym (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))))
                                                                                     (cong ∣_∣ₕ (merid north))))
                                                    (~ i) j

q-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (q n f g) (βᵣ n f g)
    ≡ β·Π n f g
q-βᵣ n f g = cong (coHomFun _ (q n f g)) (βᵣ≡ n f g)
           ∙ transportLem
           ∙ cong (subst (λ m → coHom m (C·Π' n f g))
                  (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
                        (sym (Iso.leftInv (fst (Hopfβ-Iso n (∙Π f g))) (Hopfβ n (∙Π f g)))
                        ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (∙Π f g))))) (Hopfβ↦1 n (∙Π f g)))
  where
  transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
      (βᵣ''-fun n f g)
     ≡ subst (λ m → coHom m (C·Π' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
             (Hopfβ n (∙Π f g))
  transportLem =
      natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
    ∙ cong (subst (λ m → coHom m (C·Π' n f g))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
        (cong ∣_∣₂ (funExt λ { (inl x) → refl
                            ; (inr x) → refl
                            ; (push a i₁) → loll a i₁}))
    where
    open import Cubical.Foundations.Path
    loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
      PathP
      (λ i₁ →
         βᵣ'-fun n f g ((push (θ x) ∙ λ i → inr (∙Π≡∨→∘θ n f g x (~ i))) i₁) ≡
         MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
         (λ _ → tt) (fst (∙Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
      (λ _ → βᵣ'-fun n f g (q n f g (inl tt)))
      (λ _ → βᵣ'-fun n f g (q n f g (inr (∙Π f g .fst x))))
    loll x = flipSquare (cong-∙ (βᵣ'-fun n f g) (push (θ x)) (λ i → inr (∙Π≡∨→∘θ n f g x (~ i)))
                     ∙∙ sym (rUnit _)
                     ∙∙ lem₁ x)
      where
      lem₁ : (x : _) → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
      lem₁ north = sym (Kn→ΩKn+10ₖ _)
      lem₁ south = cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
      lem₁ (merid a j) k = lala k j -- lala k j
        where
        lala : PathP (λ k → (Kn→ΩKn+10ₖ _) (~ k) ≡ (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
                     (λ j → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
                     (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
        lala = (cong-∙∙ (cong (βᵣ'-fun n f g) ∘ push)
                        (λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
                        (push tt)
                        (λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
             ∙∙ (cong (sym (Kn→ΩKn+10ₖ _) ∙_) (cong-∙ (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) (sym (merid (ptSn _)))))
             ∙∙ sym (doubleCompPath≡compPath _ _ _))
             ◁ symP (doubleCompPath-filler
                      (sym (Kn→ΩKn+10ₖ _))
                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (sym (merid north))))
open import Cubical.Foundations.Path
jₗ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jₗ n f g) (α* n f g)
    ≡ Hopfα n f
jₗ-α n f g =
    cong (coHomFun _ (jₗ n f g)) (α*-lem n f g)
  ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst f)
                      (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
                        (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
                      refl
                      (λ _ → refl)
                      λ j → refl))

jₗ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jₗ n f g) (βₗ n f g)
    ≡ subst (λ m → coHom m (HopfInvariantPush n (fst f)))
            (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
            (Hopfβ n f)
jₗ-βₗ n f g =
     cong (coHomFun _ (jₗ n f g)) (βₗ≡ n f g)
  ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
  ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
        (cong ∣_∣₂
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a i₁) → refl}))

jₗ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jₗ n f g) (βᵣ n f g)
    ≡ 0ₕ _
jₗ-βᵣ n f g =
  cong (coHomFun _ (jₗ n f g)) (βᵣ≡ n f g)
  ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
  ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
      cool
  where
  cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jₗ n f g)
      ∣ βᵣ'-fun n f g ∣₂ ≡ 0ₕ _
  cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})

jᵣ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jᵣ n f g) (α* n f g)
    ≡ Hopfα n g
jᵣ-α n f g = cong (coHomFun _ (jᵣ n f g)) (α*-lem n f g)
  ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst g)
                      (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
                        (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
                      refl
                      (λ _ → refl)
                      (flipSquare (pp-inr n f g))))

jᵣ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jᵣ n f g) (βₗ n f g) ≡ 0ₕ _
jᵣ-βₗ n f g =
  cong (coHomFun _ (jᵣ n f g)) (βₗ≡ n f g)
  ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
  ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
      cool
  where
  cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jᵣ n f g)
      ∣ βₗ'-fun n f g ∣₂ ≡ 0ₕ _
  cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})


jᵣ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → coHomFun _ (jᵣ n f g) (βᵣ n f g)
    ≡ subst (λ m → coHom m (HopfInvariantPush n (fst g)))
            (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
            (Hopfβ n g)
jᵣ-βᵣ n f g =
  cong (coHomFun _ (jᵣ n f g)) (βᵣ≡ n f g)
  ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
  ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst g)))
      (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
        (cong ∣_∣₂
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a i₁) → refl}))

gen₂ℤ×ℤ : gen₂-by (DirProd ℤGroup ℤGroup) (1 , 0) (0 , 1)
fst (gen₂ℤ×ℤ (x , y)) = x , y
snd (gen₂ℤ×ℤ (x , y)) =
  ΣPathP ((cong₂ _+_ ((·Comm 1 x) ∙ cong fst (sym (distrLem 1 0 x))) ((·Comm 0 y) ∙ cong fst (sym (distrLem 0 1 y))))
        , +Comm y 0 ∙ cong₂ _+_ (·Comm 0 x ∙ cong snd (sym (distrLem 1 0 x))) (·Comm 1 y ∙ cong snd (sym (distrLem 0 1 y))))
  where
  ℤ×ℤ = DirProd ℤGroup ℤGroup
  _+''_ = GroupStr._·_ (snd ℤ×ℤ)

  ll3 : (x : ℤ) → - x ≡ 0 - x
  ll3 (pos zero) = refl
  ll3 (pos (suc zero)) = refl
  ll3 (pos (suc (suc n))) =
    cong predℤ (ll3 (pos (suc n)))
  ll3 (negsuc zero) = refl
  ll3 (negsuc (suc n)) = cong sucℤ (ll3 (negsuc n))

  distrLem : (x y : ℤ) (z : ℤ)
         → Path (ℤ × ℤ) (z ℤ[ ℤ×ℤ ]· (x , y)) (z · x , z · y)
  distrLem x y (pos zero) = refl
  distrLem x y (pos (suc n)) =
    (cong ((x , y) +''_) (distrLem x y (pos n)))
  distrLem x y (negsuc zero) = ΣPathP (sym (ll3 x) , sym (ll3 y))
  distrLem x y (negsuc (suc n)) =
    cong₂ _+''_ (ΣPathP (sym (ll3 x) , sym (ll3 y)))
                (distrLem x y (negsuc n))
  
genH²ⁿC* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
         → gen₂-by (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
                    (βₗ n f g)
                    (βᵣ n f g)
genH²ⁿC* n f g =
  Iso-pres-gen₂ (DirProd ℤGroup ℤGroup)
    (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
    (1 , 0)
    (0 , 1)
    gen₂ℤ×ℤ
    (invGroupIso (H⁴-C* n f g))

private

  H⁴C* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Group _
  H⁴C* n f g = coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)

  X : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
      → ℤ
  X n f g = (genH²ⁿC* n f g) (α* n f g ⌣ α* n f g) .fst .fst
  Y : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
      → ℤ
  Y n  f g = (genH²ⁿC* n f g) (α* n f g ⌣ α* n f g) .fst .snd

  α*≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
      → α* n f g ⌣ α* n f g ≡ ((X n f g) ℤ[ H⁴C* n f g ]· βₗ n f g)
                            +ₕ ((Y n f g) ℤ[ H⁴C* n f g ]· βᵣ n f g)
  α*≡ n f g = (genH²ⁿC* n f g) (α* n f g ⌣ α* n f g) .snd


eq₁ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → (Hopfα n (∙Π f g)) ⌣ (Hopfα n (∙Π f g))
    ≡ ((X n f g + Y n f g) ℤ[ coHomGr _ _ ]· (β·Π n f g))
eq₁ n f g =
    cong (λ x → x ⌣ x) (sym (q-α n f g) ∙ cong (coHomFun (suc (suc n)) (q n f g)) (α*-lem n f g))
  ∙ cong ((coHomFun _) (q _ f g)) (cong (λ x → x ⌣ x) (sym (α*-lem n f g))
                       ∙ α*≡ n f g)
  ∙ IsGroupHom.pres· (coHomMorph _ (q n f g) .snd) _ _
  ∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (q n f g)) (βₗ n f g) (X n f g)
                       ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
                              (q-βₗ n f g))
               (homPresℤ· (coHomMorph _ (q n f g)) (βᵣ n f g) (Y n f g)
                       ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
                              (q-βᵣ n f g))
  ∙ sym (distrℤ· (coHomGr _ _) (β·Π n f g) (X n f g) (Y n f g))

coHomFun⌣ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
          → (n : ℕ) (x y : coHom n B)
          → coHomFun _ f (x ⌣ y) ≡ coHomFun _ f x ⌣ coHomFun _ f y
coHomFun⌣ f n = sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl

eq₂ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → Hopfα n f ⌣ Hopfα n f
    ≡ (X n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
            (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
            (Hopfβ n f))
eq₂ n f g =
     cong (λ x → x ⌣ x) (sym (jₗ-α n f g))
  ∙∙ sym (coHomFun⌣ (jₗ n f g) _ _ _)
  ∙∙ cong (coHomFun _ (jₗ n f g)) (α*≡ n f g)
  ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jₗ n f g))) _ _
  ∙∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (jₗ n f g)) (βₗ n f g) (X n f g))
                (homPresℤ· (coHomMorph _ (jₗ n f g)) (βᵣ n f g) (Y n f g)
                          ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
                                 (jₗ-βᵣ n f g))
  ∙∙ cong₂ _+ₕ_ refl (rUnitℤ· (coHomGr _ _) (Y n f g))
  ∙∙ (rUnitₕ _ _
   ∙ cong (X n f g ℤ[ coHomGr _ _ ]·_) (jₗ-βₗ n f g))

eq₃ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → Hopfα n g ⌣ Hopfα n g
    ≡ (Y n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
            (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
            (Hopfβ n g))
eq₃ n f g =
     cong (λ x → x ⌣ x) (sym (jᵣ-α n f g))
  ∙∙ sym (coHomFun⌣ (jᵣ n f g) _ _ _)
  ∙∙ cong (coHomFun _ (jᵣ n f g)) (α*≡ n f g)
  ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jᵣ n f g))) _ _
  ∙∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (jᵣ n f g)) (βₗ n f g) (X n f g)
                          ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
                                 (jᵣ-βₗ n f g))
                (homPresℤ· (coHomMorph _ (jᵣ n f g)) (βᵣ n f g) (Y n f g))
  ∙∙ cong₂ _+ₕ_ (rUnitℤ· (coHomGr _ _) (X n f g)) refl
  ∙∙ ((lUnitₕ _ _) ∙ cong (Y n f g ℤ[ coHomGr _ _ ]·_) (jᵣ-βᵣ n f g))

eq₂-eq₂ : (n : ℕ) (f g : S₊∙ (suc (suc (suc (n +ℕ n)))) →∙ S₊∙ (suc (suc n)))
        → HopfInvariant n (∙Π f g) ≡ HopfInvariant n f + HopfInvariant n g
eq₂-eq₂ n f g =
      mainL
   ∙ sym (cong₂ _+_ (help n f g) (helpg n f g))
  where
  transpLem : ∀ {ℓ} {G : ℕ → Group ℓ}
             → (n m : ℕ)
             → (x : ℤ)
             → (p : m ≡ n)
             → (g : fst (G n))
             → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g) ≡ (x ℤ[ G n ]· g)
  transpLem {G = G} n m x =
    J (λ n p → (g : fst (G n)) → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g)
                                ≡ (x ℤ[ G n ]· g))
      λ g → transportRefl _ ∙ cong (x ℤ[ G m ]·_) (transportRefl _)

  mainL : HopfInvariant n (∙Π f g) ≡ X n f g + Y n f g
  mainL = cong (Iso.fun (fst (Hopfβ-Iso n (∙Π f g))))
               (cong (subst (λ x → coHom x (HopfInvariantPush n (fst (∙Π f g))))
                            λ i₁ → suc (suc (suc (+-suc n n i₁))))
                     (eq₁ n f g))
       ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n (∙Π f g))))
               (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst (∙Π f g)))} _ _
                          (X n f g + Y n f g) (λ i₁ → suc (suc (suc (+-suc n n i₁))))
                          (Iso.inv (fst (Hopfβ-Iso n (∙Π f g))) 1))
       ∙∙ homPresℤ· (_ , snd (Hopfβ-Iso n (∙Π f g))) (Iso.inv (fst (Hopfβ-Iso n (∙Π f g))) 1)
                   (X n f g + Y n f g) 
       ∙∙ cong ((X n f g + Y n f g) ℤ[ ℤ , ℤGroup .snd ]·_)
               (Iso.rightInv ((fst (Hopfβ-Iso n (∙Π f g)))) 1)
       ∙∙ rUnitℤ·ℤ (X n f g + Y n f g)


  help : (n : ℕ) (f g : _) → HopfInvariant n f ≡ X n f g
  help n f g = cong (Iso.fun (fst (Hopfβ-Iso n f)))
              (cong (subst (λ x → coHom x (HopfInvariantPush n (fst f)))
                    (λ i₁ → suc (suc (suc (+-suc n n i₁))))) (eq₂ n f g))
            ∙ cong (Iso.fun (fst (Hopfβ-Iso n f)))
                   (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst f))} _ _
                              (X n f g)
                              ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
                              (Hopfβ n f))
            ∙ homPresℤ· (_ , snd (Hopfβ-Iso n f)) (Hopfβ n f) (X n f g)
            ∙ cong (X n f g ℤ[ ℤ , ℤGroup .snd ]·_) (Hopfβ↦1 n f)
            ∙ rUnitℤ·ℤ (X n f g)

  helpg : (n : ℕ) (f g : _) → HopfInvariant n g ≡ Y n f g
  helpg n f g =
       cong (Iso.fun (fst (Hopfβ-Iso n g)))
            (cong (subst (λ x → coHom x (HopfInvariantPush n (fst g)))
                    (λ i₁ → suc (suc (suc (+-suc n n i₁)))))
                      (eq₃ n f g))
    ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n g)))
                   (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst g))} _ _
                              (Y n f g)
                              ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
                              (Hopfβ n g))
    ∙∙ homPresℤ· (_ , snd (Hopfβ-Iso n g)) (Hopfβ n g) (Y n f g)
    ∙∙ cong (Y n f g ℤ[ ℤ , ℤGroup .snd ]·_) (Hopfβ↦1 n g)
    ∙∙ rUnitℤ·ℤ (Y n f g)


-- GroupHom-HopfInvariant-π' : (n : ℕ) → GroupHom (π'Gr (suc (suc (n +ℕ n))) (S₊∙ (suc (suc n)))) ℤGroup 
-- GroupHom-HopfInvariant-π' n = HopfInvariant-π' n , makeIsGroupHom {!eq₂-eq₂ n!}
