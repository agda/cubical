{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contains a proof that the generator of Π₃S² has
hopf invariant ±1.
-}
module Cubical.Homotopy.HopfInvariant.HopfMap where

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


HopfMap : S₊∙ 3 →∙ S₊∙ 2
fst HopfMap x = JoinS¹S¹→TotalHopf (Iso.inv (IsoSphereJoin 1 1) x) .fst
snd HopfMap = refl

-- We use the Hopf fibration in order to connect it to the Gysin Sequence
module hopfS¹ = hopfBase S1-AssocHSpace (sphereElim2 _ (λ _ _ → squash) ∣ refl ∣)
S¹Hopf = hopfS¹.Hopf
E* = hopfS¹.totalSpaceMegaPush
IsoE*join = hopfS¹.IsoJoin₁
IsoTotalHopf' = hopfS¹.joinIso₁
CP² = hopfS¹.megaPush
fibr = hopfS¹.P

TotalHopf' : Type _
TotalHopf' = Σ (S₊ 2) S¹Hopf

IsoJoins : (join S¹ (join S¹ S¹)) ≡ join S¹ (S₊ 3)
IsoJoins = cong (join S¹) (isoToPath (IsoSphereJoin 1 1))

-- CP² is 1-connected
conCP² : (x y : CP²) → ∥ x ≡ y ∥₂
conCP² x y = sRec2 squash₂ (λ p q → ∣ p ∙ sym q ∣₂) (conCP²' x) (conCP²' y)
  where
  conCP²' : (x : CP²) → ∥ x ≡ inl tt ∥₂
  conCP²' (inl x) = ∣ refl ∣₂
  conCP²' (inr x) = sphereElim 1 {A = λ x → ∥ inr x ≡ inl tt ∥₂}
                                 (λ _ → squash₂) ∣ sym (push (inl base)) ∣₂ x
  conCP²' (push a i₁) = main a i₁
    where
    indLem : ∀ {ℓ} {A : hopfS¹.TotalSpaceHopf' → Type ℓ} → ((a : _) → isProp (A a))
        → A (inl base)
        → ((a : hopfS¹.TotalSpaceHopf') → A a) 
    indLem {A = A} p b =
      PushoutToProp p (sphereElim 0 (λ _ → p _) b)
                      (sphereElim 0 (λ _ → p _) (subst A (push (base , base)) b))

    main : (a : hopfS¹.TotalSpaceHopf')
         → PathP (λ i → ∥ Path CP² (push a i) (inl tt) ∥₂)
                  (conCP²' (inl tt)) (conCP²' (inr (hopfS¹.induced a)))
    main = indLem (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
                   λ j → ∣ (λ i → push (inl base) (~ i ∧ j)) ∣₂

module GysinS² = Gysin (CP² , inl tt) fibr conCP² 2 idIso refl

E'S⁴Iso : Iso GysinS².E' (S₊ 5)
E'S⁴Iso =
  compIso IsoE*join
    (compIso (Iso→joinIso idIso (IsoSphereJoin 1 1))
             (IsoSphereJoin 1 3))

isContrH³E : isContr (coHom 3 (GysinS².E'))
isContrH³E =
  subst isContr (sym (isoToPath
                      (fst (Hⁿ-Sᵐ≅0 2 4
                      λ p → snotz (sym (cong (predℕ ∘ predℕ) p)))))
               ∙ cong (coHom 3) (sym (isoToPath E'S⁴Iso)))
        isContrUnit

isContrH⁴E : isContr (coHom 4 (GysinS².E'))
isContrH⁴E =
  subst isContr (sym (isoToPath
                     (fst (Hⁿ-Sᵐ≅0 3 4
                       λ p → snotz (sym (cong (predℕ ∘ predℕ ∘ predℕ) p)))))
               ∙ cong (coHom 4) (sym (isoToPath E'S⁴Iso)))
        isContrUnit

-- We will need a bunch of elimination principles
joinS¹S¹→Groupoid : ∀ {ℓ} (P : join S¹ S¹ → Type ℓ)
            → ((x : _) → isGroupoid (P x))
            → P (inl base)
            → (x : _) → P x
joinS¹S¹→Groupoid P grp b =
  transport (λ i → (x : (isoToPath (invIso (IsoSphereJoin 1 1))) i)
         → P (transp (λ j → isoToPath (invIso (IsoSphereJoin 1 1)) (i ∨ j)) i x ))
         (sphereElim _ (λ _ → grp _) b)

TotalHopf→Gpd : ∀ {ℓ} (P : hopfS¹.TotalSpaceHopf' → Type ℓ)
            → ((x : _) → isGroupoid (P x))
            → P (inl base)
            → (x : _) → P x
TotalHopf→Gpd P grp b =
  transport (λ i → (x : sym (isoToPath IsoTotalHopf') i)
                 → P (transp (λ j → isoToPath IsoTotalHopf' (~ i ∧ ~ j)) i x))
    (joinS¹S¹→Groupoid _ (λ _ → grp _) b)

TotalHopf→Gpd' : ∀ {ℓ} (P : Σ (S₊ 2) hopfS¹.Hopf → Type ℓ)
            → ((x : _) → isGroupoid (P x))
            → P (north , base)
            → (x : _) → P x
TotalHopf→Gpd' P grp b =
  transport (λ i → (x : ua (_ , hopfS¹.isEquivTotalSpaceHopf'→TotalSpace) i)
          → P (transp (λ j → ua (_ , hopfS¹.isEquivTotalSpaceHopf'→TotalSpace) (i ∨ j)) i x))
          (TotalHopf→Gpd _ (λ _ → grp _) b)

CP²→Groupoid : ∀ {ℓ} {P : CP² → Type ℓ}
               → ((x : _) → is2Groupoid (P x))
               → (b : P (inl tt))
               → (s2 : ((x : _) → P (inr x)))
               → PathP (λ i → P (push (inl base) i)) b (s2 north)
               → (x : _) → P x
CP²→Groupoid {P = P} grp b s2 pp (inl x) = b
CP²→Groupoid {P = P} grp b s2 pp (inr x) = s2 x
CP²→Groupoid {P = P} grp b s2 pp (push a i₁) = lem a i₁
  where
  lem : (a : hopfS¹.TotalSpaceHopf') → PathP (λ i → P (push a i)) b (s2 _) 
  lem = TotalHopf→Gpd _  (λ _ → isOfHLevelPathP' 3 (grp _) _ _) pp

-- The function inducing the iso H²(S²) ≅ H²(CP²)
H²S²→H²CP²-raw : (S₊ 2 → coHomK 2) → (CP² → coHomK 2)
H²S²→H²CP²-raw f (inl x) = 0ₖ _
H²S²→H²CP²-raw f (inr x) = f x -ₖ f north
H²S²→H²CP²-raw f (push a i) =
  TotalHopf→Gpd (λ x → 0ₖ 2 ≡ f (hopfS¹.TotalSpaceHopf'→TotalSpace x .fst) -ₖ f north)
                                         (λ _ → isOfHLevelTrunc 4 _ _)
                                         (sym (rCancelₖ 2 (f north)))
                                         a i

H²S²→H²CP² : coHomGr 2 (S₊ 2) .fst → coHomGr 2 CP² .fst
H²S²→H²CP² = sMap H²S²→H²CP²-raw

cancel-H²S²→H²CP² : (f : CP² → coHomK 2) → ∥ H²S²→H²CP²-raw (f ∘ inr) ≡ f ∥
cancel-H²S²→H²CP² f =
  pRec squash
    (λ p → pRec squash
                (λ f → ∣ funExt f ∣)
                (cancelLem p))
    (connLem (f (inl tt)))
  where
  connLem : (x : coHomK 2) →  ∥ x ≡ 0ₖ 2 ∥
  connLem = coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash) ∣ refl ∣ 

  cancelLem : (p : f (inl tt) ≡ 0ₖ 2) → ∥ ((x : CP²) → H²S²→H²CP²-raw (f ∘ inr) x ≡ f x) ∥
  cancelLem p = trRec squash (λ pp → 
    ∣ CP²→Groupoid (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
                 (sym p)
                 (λ x → (λ i → f (inr x) -ₖ f (push (inl base) (~ i)))
                       ∙∙ (λ i → f (inr x) -ₖ p i)
                       ∙∙ rUnitₖ 2 (f (inr x))) pp ∣)
                help
    where
    help : hLevelTrunc 1 (PathP ((λ i₁ → H²S²→H²CP²-raw (f ∘ inr) (push (inl base) i₁) ≡ f (push (inl base) i₁)))
              (sym p)
              (((λ i₁ → f (inr north) -ₖ f (push (inl base) (~ i₁))) ∙∙
                (λ i₁ → f (inr north) -ₖ p i₁) ∙∙ rUnitₖ 2 (f (inr north)))))
    help = isConnectedPathP 1 (isConnectedPath 2 (isConnectedKn 1) _ _) _ _ .fst

H²CP²≅H²S² : GroupIso (coHomGr 2 CP²) (coHomGr 2 (S₊ 2))
Iso.fun (fst H²CP²≅H²S²) = sMap (_∘ inr)
Iso.inv (fst H²CP²≅H²S²) = H²S²→H²CP²
Iso.rightInv (fst H²CP²≅H²S²) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f → trRec {B = Iso.fun (fst H²CP²≅H²S²) (Iso.inv (fst H²CP²≅H²S²) ∣ f ∣₂) ≡ ∣ f ∣₂}
      (isOfHLevelPath 2 squash₂ _ _)
      (λ p → cong ∣_∣₂ (funExt λ x → cong (λ y → (f x) -ₖ y) p ∙ rUnitₖ 2 (f x)))
      (Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedKn 1) ∣ f north ∣ ∣ 0ₖ 2 ∣))
Iso.leftInv (fst H²CP²≅H²S²) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    λ f → pRec (squash₂ _ _) (cong ∣_∣₂) (cancel-H²S²→H²CP² f)
snd H²CP²≅H²S² =
  makeIsGroupHom
    (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ f g → refl)

H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) ℤGroup
H²CP²≅ℤ = compGroupIso H²CP²≅H²S² (Hⁿ-Sⁿ≅ℤ 1)

-- ⌣ gives a groupEquiv H²(CP²) ≃ H⁴(CP²)
⌣Equiv : GroupEquiv (coHomGr 2 CP²) (coHomGr 4 CP²)
fst (fst ⌣Equiv) = GysinS².⌣-hom 2 .fst
snd (fst ⌣Equiv) = subst isEquiv (cong fst (GysinS².ϕ∘j≡ 2)) eq'
  where
  eq' : isEquiv (GysinS².ϕ∘j 2 .fst)
  eq' =
    SES→isEquiv
      (GroupPath _ _ .fst (invGroupEquiv
        (isContr→≃Unit isContrH³E
        , makeIsGroupHom λ _ _ → refl)))
      (GroupPath _ _ .fst (invGroupEquiv
        (isContr→≃Unit isContrH⁴E
        , makeIsGroupHom λ _ _ → refl)))
      (GysinS².susp∘ϕ 1)
      (GysinS².ϕ∘j 2)
      (GysinS².p-hom 4)
      (GysinS².Ker-ϕ∘j⊂Im-Susp∘ϕ _)
      (GysinS².Ker-p⊂Im-ϕ∘j _)
snd ⌣Equiv = GysinS².⌣-hom 2 .snd

-- The generator of H²(CP²)
genCP² : coHom 2 CP²
genCP² = ∣ CP²→Groupoid (λ _ → isOfHLevelTrunc 4)
                      (0ₖ _)
                      ∣_∣
                      refl ∣₂

inrInjective : (f g : CP² → coHomK 2) → ∥ f ∘ inr ≡ g ∘ inr ∥ → Path (coHom 2 CP²) ∣ f ∣₂ ∣ g ∣₂
inrInjective f g = pRec (squash₂ _ _)
  (λ p → pRec (squash₂ _ _) (λ id → trRec (squash₂ _ _)
               (λ pp → cong ∣_∣₂
                 (funExt (CP²→Groupoid (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
                         id
                         (funExt⁻ p)
                         (compPathR→PathP pp))))
                   (conn2 (f (inl tt)) (g (inl tt)) id
                     (cong f (push (inl base)) ∙ (funExt⁻ p north) ∙ cong g (sym (push (inl base))))))
               (conn (f (inl tt)) (g (inl tt))))

  where
  conn : (x y : coHomK 2) → ∥ x ≡ y ∥
  conn = coHomK-elim _ (λ _ → isSetΠ λ _ → isOfHLevelSuc 1 squash)
           (coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash) ∣ refl ∣)

  conn2 : (x y : coHomK 2) (p q : x ≡ y) → hLevelTrunc 1 (p ≡ q)
  conn2 x y = λ p q → Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedPath _ (isConnectedKn 1) x y) ∣ p ∣ ∣ q ∣)

-- A couple of basic lemma concerning the hSpace structure on S¹
private
  rUnit* : (x : S¹) → x * base ≡ x
  rUnit* base = refl
  rUnit* (loop i₁) = refl

  merid*-lem : (a x : S¹) → Path (Path (coHomK 2) _ _) (cong ∣_∣ₕ (merid (a * x) ∙ sym (merid base)))
                                                    ((cong ∣_∣ₕ (merid a ∙ sym (merid base))) ∙ (cong ∣_∣ₕ (merid x ∙ sym (merid base))))
  merid*-lem = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
             (λ x → lUnit _ ∙ cong (_∙ cong ∣_∣ₕ (merid x ∙ sym (merid base))) (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
             (λ x → (λ i → cong ∣_∣ₕ (merid (rUnit* x i) ∙ sym (merid base)))
                 ∙∙ rUnit _
                 ∙∙ cong (cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙_)
                         (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
             (sym (l (cong ∣_∣ₕ (merid base ∙ sym (merid base)))
                  (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))))
    where
    l : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : refl ≡ p)
      → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P
    l p = J (λ p P → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P) refl

  lemmie : (x : S¹) → ptSn 1 ≡ x * (invLooper x)
  lemmie base = refl
  lemmie (loop i) j =
    hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (j = i0) → base})
          base


  meridInvLooperLem : (x : S¹) → Path (Path (coHomK 2) _ _)
                           (cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base)))
                           (cong ∣_∣ₕ (sym (merid x ∙ sym (merid base))))
  meridInvLooperLem x = (lUnit _
         ∙∙ cong (_∙ cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base)))
                 (sym (lCancel (cong ∣_∣ₕ (merid x ∙ sym (merid base))))) ∙∙ sym (assoc _ _ _))
         ∙∙ cong (sym (cong ∣_∣ₕ (merid x ∙ sym (merid base))) ∙_) lem
         ∙∙ (assoc _ _ _
         ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (merid x ∙ sym (merid base)))))
                 (lCancel (cong ∣_∣ₕ (merid x ∙ sym (merid base))))
         ∙∙ sym (lUnit _))
    where
    lem : cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙ cong ∣_∣ₕ (merid (invLooper x) ∙ sym (merid base))
       ≡ cong ∣_∣ₕ (merid x ∙ sym (merid base)) ∙ cong ∣_∣ₕ (sym (merid x ∙ sym (merid base)))
    lem = sym (merid*-lem x (invLooper x))
       ∙ ((λ i → cong ∣_∣ₕ (merid (lemmie x (~ i)) ∙ sym (merid base)))
       ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

  comm·S¹ : (a x : S¹) → a * x ≡ x * a
  comm·S¹ = wedgeconFun _ _ (λ _ _ → isGroupoidS¹ _ _)
           (sym ∘ rUnit*)
           rUnit*
           refl

  invLooperLem₁ : (a x : S¹) → (invEq (hopfS¹.μ-eq a) x) * a ≡ (invLooper a * x) * a
  invLooperLem₁ a x =
       secEq (hopfS¹.μ-eq a) x
    ∙∙ cong (_* x) (lemmie a)
    ∙∙ assocHSpace.μ-assoc S1-AssocHSpace a (invLooper a) x
     ∙ comm·S¹ _ _

  invLooperLem₂ : (a x : S¹) → invEq (hopfS¹.μ-eq a) x ≡ invLooper a * x
  invLooperLem₂ a x = sym (retEq (hopfS¹.μ-eq a) (invEq (hopfS¹.μ-eq a) x))
          ∙∙ cong (invEq (hopfS¹.μ-eq a)) (invLooperLem₁ a x)
          ∙∙ retEq (hopfS¹.μ-eq a) (invLooper a * x)

  rotLoop² : (a : S¹) → Path (a ≡ a) (λ i → rotLoop (rotLoop a i) (~ i)) refl
  rotLoop² =
    sphereElim 0 (λ _ → isGroupoidS¹ _ _ _ _)
      λ i j → hcomp (λ {k → λ { (i = i1) → base
                                ; (j = i0) → base
                                ; (j = i1) → base}})
                    base


-- We prove that the generator of CP² given by Gysin is the same one
-- as genCP², which is much easier to work with
Gysin-e≡genCP² : GysinS².e ≡ genCP²
Gysin-e≡genCP² = inrInjective _ _ ∣ funExt (λ x → funExt⁻ (cong fst (main x)) south) ∣
  where
  mainId : (x : Σ (S₊ 2) hopfS¹.Hopf) → Path (hLevelTrunc 4 _) ∣ fst x ∣ ∣ north ∣
  mainId = uncurry λ { north → λ y → cong ∣_∣ₕ (merid base ∙ sym (merid y))
                     ; south → λ y → cong ∣_∣ₕ (sym (merid y))
                     ; (merid a i) → main a i}
    where
    main : (a : S¹) → PathP (λ i → (y : hopfS¹.Hopf (merid a i))
                    → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a i ∣ ∣ north ∣)
                            (λ y → cong ∣_∣ₕ (merid base ∙ sym (merid y)))
                            λ y → cong ∣_∣ₕ (sym (merid y))
    main a =
      toPathP
        (funExt λ x →
          cong (transport (λ i₁ → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a i₁ ∣ ∣ north ∣))
               ((λ i → (λ z → cong ∣_∣ₕ
                         (merid base ∙ sym (merid (transport (λ j → uaInvEquiv (hopfS¹.μ-eq a) (~ i) j) x))) z))
               ∙ λ i → cong ∣_∣ₕ (merid base
                      ∙ sym (merid (transportRefl (invEq (hopfS¹.μ-eq a) x) i))))
      ∙∙ (λ i → transp (λ i₁ → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a (i₁ ∨ i) ∣ ∣ north ∣) i
                        (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                          (cong ∣_∣ₕ (merid base ∙ sym (merid (invLooperLem₂ a x i)))) i))
      ∙∙ cong ((cong ∣_∣ₕ) (sym (merid a)) ∙_)
              (cong (cong ∣_∣ₕ) (cong sym (symDistr (merid base) (sym (merid (invLooper a * x)))))
                              ∙ cong sym (merid*-lem (invLooper a) x)
                              ∙ symDistr ((cong ∣_∣ₕ) (merid (invLooper a) ∙ sym (merid base)))
                                          ((cong ∣_∣ₕ) (merid x ∙ sym (merid base)))
                              ∙ isCommΩK 2 (sym (λ i₁ → ∣ (merid x ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
                                           (sym (λ i₁ → ∣ (merid (invLooper a) ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
                              ∙ cong₂ _∙_ (cong sym (meridInvLooperLem a)
                                            ∙ cong-∙ ∣_∣ₕ (merid a) (sym (merid base)))
                                          (cong (cong ∣_∣ₕ) (symDistr (merid x) (sym (merid base)))
                                            ∙ cong-∙ ∣_∣ₕ (merid base) (sym (merid x))))
      ∙∙ (λ j → (λ i₁ → ∣ merid a (~ i₁ ∨ j) ∣) ∙ ((λ i₁ → ∣ merid a (i₁ ∨ j) ∣)
                 ∙ (λ i₁ → ∣ merid base (~ i₁ ∨ j) ∣)) ∙ (λ i₁ → ∣ merid base (i₁ ∨ j) ∣)
                 ∙ (λ i₁ → ∣ merid x (~ i₁) ∣ₕ))
      ∙∙ sym (lUnit _)
      ∙∙ sym (assoc _ _ _)
      ∙∙ (sym (lUnit _) ∙ sym (lUnit _) ∙ sym (lUnit _)))

  gen' : (x : S₊ 2) → preThom.Q (CP² , inl tt) fibr (inr x) →∙ coHomK-ptd 2
  fst (gen' x) north = ∣ north ∣
  fst (gen' x) south = ∣ x ∣
  fst (gen' x) (merid a i₁) = mainId (x , a) (~ i₁)
  snd (gen' x) = refl

  gen'Id : GysinS².c (inr north) .fst ≡ gen' north .fst
  gen'Id = cong fst (GysinS².cEq (inr north) ∣ push (inl base) ∣₂)
           ∙ (funExt l)
    where
    l : (qb : _) →
         ∣ (subst (fst ∘ preThom.Q (CP² , inl tt) fibr) (sym (push (inl base))) qb) ∣
      ≡ gen' north .fst qb
    l north = refl
    l south = cong ∣_∣ₕ (sym (merid base))
    l (merid a i) j =
      hcomp (λ k → λ { (i = i0) → ∣ merid a (~ k ∧ j) ∣
                      ; (i  = i1) → ∣ merid base (~ j) ∣
                      ; (j = i0) → ∣ transportRefl (merid a i) (~ k) ∣
                      ; (j = i1) → ∣ compPath-filler (merid base) (sym (merid a)) k (~ i) ∣ₕ})
            (hcomp (λ k → λ { (i = i0) → ∣ merid a (j ∨ ~ k) ∣
                             ; (i  = i1) → ∣ merid base (~ j ∨ ~ k) ∣
                             ; (j = i0) → ∣ merid a (~ k ∨ i) ∣
                             ; (j = i1) → ∣ merid base (~ i ∨ ~ k) ∣ₕ})
                          ∣ south ∣)

  setHelp : (x : S₊ 2) → isSet (preThom.Q (CP² , inl tt) fibr (inr x) →∙ coHomK-ptd 2)
  setHelp = sphereElim _ (λ _ → isProp→isOfHLevelSuc 1 (isPropIsOfHLevel 2))
                            (isOfHLevel↑∙' 0 1)

  main : (x : S₊ 2) →  (GysinS².c (inr x) ≡ gen' x)
  main = sphereElim _ (λ x → isOfHLevelPath 2 (setHelp x) _ _)
         (→∙Homogeneous≡ (isHomogeneousKn _) gen'Id)

isGenerator≃ℤ : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Type ℓ
isGenerator≃ℤ G g =
  Σ[ e ∈ GroupIso G ℤGroup ] abs (Iso.fun (fst e) g) ≡ 1

isGenerator≃ℤ-e : isGenerator≃ℤ (coHomGr 2 CP²) GysinS².e
isGenerator≃ℤ-e =
  subst (isGenerator≃ℤ (coHomGr 2 CP²)) (sym Gysin-e≡genCP²)
    (H²CP²≅ℤ , refl)

-- Alternative definition of the hopfMap
HopfMap' : S₊ 3 → S₊ 2
HopfMap' x =
  hopfS¹.TotalSpaceHopf'→TotalSpace
    (Iso.inv IsoTotalHopf'
      (Iso.inv (IsoSphereJoin 1 1) x)) .fst

hopfMap≡HopfMap' : HopfMap ≡ (HopfMap' , refl)
hopfMap≡HopfMap' =
  ΣPathP ((funExt (λ x → cong (λ x → JoinS¹S¹→TotalHopf x .fst)
                               (sym (Iso.rightInv IsoTotalHopf' (Iso.inv (IsoSphereJoin 1 1) x)))
                        ∙ sym (lem (Iso.inv IsoTotalHopf' (Iso.inv (IsoSphereJoin 1 1) x)))))
         , flipSquare (sym (rUnit refl) ◁ λ _ _ → north))
  where
  lem : (x : _) → hopfS¹.TotalSpaceHopf'→TotalSpace x .fst
               ≡ JoinS¹S¹→TotalHopf (Iso.fun IsoTotalHopf' x) .fst
  lem (inl x) = refl
  lem (inr x) = refl
  lem (push (base , snd₁) i) = refl
  lem (push (loop i₁ , a) i) k = merid (rotLoop² a (~ k) i₁) i

CP²' : Type _
CP²' = Pushout {A = S₊ 3} (λ _ → tt) HopfMap'

PushoutReplaceBase :
  ∀ {ℓ ℓ' ℓ''} {A B : Type ℓ} {C : Type ℓ'} {D : Type ℓ''} {f : A → C} {g : A → D}
    (e : B ≃ A) → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g
PushoutReplaceBase {f = f} {g = g} =
  EquivJ (λ _ e → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g) refl

CP2≡CP²' : CP²' ≡ CP²
CP2≡CP²' =
  PushoutReplaceBase
    (isoToEquiv (compIso (invIso (IsoSphereJoin 1 1)) (invIso IsoTotalHopf')))

-- packaging everything up:
⌣equiv→pres1 : ∀ {ℓ} {G H : Type ℓ} → (G ≡ H) → (g₁ : coHom 2 G) (h₁ : coHom 2 H)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ] abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 H) ℤGroup ] abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 H) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1
⌣equiv→pres1 {G = G} = J (λ H _ → (g₁ : coHom 2 G) (h₁ : coHom 2 H)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ] abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 H) ℤGroup ] abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 H) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1)
              help
  where
  help : (g₁ h₁ : coHom 2 G)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ] abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ] abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 G) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1
  help g h (ϕ , idg) (ψ , idh) ⌣eq ξ =
    ⊎→abs _ _
      (allisoPresGen _
        (compGroupEquiv main4 (compGroupEquiv (invGroupEquiv main4) ψ))
        h (abs→⊎ _ _ (cong abs (cong (fst (fst ψ)) (retEq (fst main4) h)) ∙ idh)) (compGroupEquiv main4 ξ))
    where
    k1 : ((fst (fst ψ) h) ≡ 1) ⊎ (fst (fst ψ) h ≡ -1)
      → abs (fst (fst ϕ) h) ≡ 1
    k1 p = ⊎→abs _ _ (allisoPresGen _ ψ h p ϕ)

    help2 : ((fst (fst ϕ) h) ≡ 1) ⊎ (fst (fst ϕ) h ≡ -1)
          → ((fst (fst ϕ) g) ≡ 1) ⊎ (fst (fst ϕ) g ≡ -1)
          → (h ≡ g) ⊎ (h ≡ (-ₕ g))
    help2 (inl x) (inl x₁) =
      inl (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) (x ∙ sym x₁)
        ∙∙ retEq (fst ϕ) g)
    help2 (inl x) (inr x₁) =
      inr (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) x
         ∙ IsGroupHom.presinv (snd (invGroupEquiv ϕ)) (negsuc zero)
         ∙∙ cong (-ₕ_) (cong (invEq (fst ϕ)) (sym x₁) ∙ (retEq (fst ϕ) g)))
    help2 (inr x) (inl x₁) =
      inr (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) x
        ∙∙ (IsGroupHom.presinv (snd (invGroupEquiv ϕ)) 1
          ∙ cong (-ₕ_) (cong (invEq (fst ϕ)) (sym x₁) ∙ (retEq (fst ϕ) g))))
    help2 (inr x) (inr x₁) =
      inl (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) (x ∙ sym x₁)
        ∙∙ retEq (fst ϕ) g)

    -ₕeq : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → Iso (coHom n A) (coHom n A)
    Iso.fun (-ₕeq n) = -ₕ_
    Iso.inv (-ₕeq n) = -ₕ_
    Iso.rightInv (-ₕeq n) =
      sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ f → cong ∣_∣₂ (funExt λ x → -ₖ^2 (f x))
    Iso.leftInv (-ₕeq n) =
      sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ f → cong ∣_∣₂ (funExt λ x → -ₖ^2 (f x))

    theEq : coHom 2 G ≃ coHom 4 G
    theEq = compEquiv (_ , ⌣eq) (isoToEquiv (-ₕeq 4))

    main3 : (h ≡ g) ⊎ (h ≡ (-ₕ g)) → isEquiv {A = coHom 2 G} (_⌣ h)
    main3 (inl x) = subst isEquiv (λ i → _⌣ (x (~ i))) ⌣eq
    main3 (inr x) =
      subst isEquiv (funExt (λ x → -ₕDistᵣ 2 2 x g) ∙ (λ i → _⌣ (x (~ i))))
            (theEq .snd)

    main4 : GroupEquiv (coHomGr 2 G) (coHomGr 4 G)
    fst main4 = _ , (main3 (help2 (abs→⊎ _ _ (k1 (abs→⊎ _ _ idh))) (abs→⊎ _ _ idg)))
    snd main4 =
      makeIsGroupHom λ g1 g2 → rightDistr-⌣ _ _ g1 g2 h

-- The hopf invariant is ±1 for both definitions of the hopf map
HopfInvariant-HopfMap' : abs (HopfInvariant zero (HopfMap' , λ _ → HopfMap' (snd (S₊∙ 3))))
                       ≡ suc zero
HopfInvariant-HopfMap' =
  cong abs (cong (Iso.fun (fst (Hopfβ-Iso zero (HopfMap' , refl))))
           (transportRefl (⌣-α 0 (HopfMap' , refl))))
            ∙ ⌣equiv→pres1 (sym CP2≡CP²') GysinS².e (Hopfα zero (HopfMap' , refl))
           (l isGenerator≃ℤ-e)
           (GroupIso→GroupEquiv (Hopfα-Iso 0 (HopfMap' , refl)) , refl)
           (snd (fst ⌣Equiv))
           (GroupIso→GroupEquiv (Hopfβ-Iso zero (HopfMap' , refl)))
  where
  l : Σ[ ϕ ∈ GroupIso (coHomGr 2 CP²) ℤGroup ]
       (abs (Iso.fun (fst ϕ) GysinS².e) ≡ 1)
      → Σ[ ϕ ∈ GroupEquiv (coHomGr 2 CP²) ℤGroup ]
          (abs (fst (fst ϕ) GysinS².e) ≡ 1)
  l p = (GroupIso→GroupEquiv (fst p)) , (snd p)

HopfInvariant-HopfMap : abs (HopfInvariant zero HopfMap) ≡ suc zero
HopfInvariant-HopfMap = cong abs (cong (HopfInvariant zero) hopfMap≡HopfMap')
                      ∙ HopfInvariant-HopfMap'



HopfInvariantPushElim : ∀ {ℓ} n → (f : _) → {P : HopfInvariantPush n f → Type ℓ}
                        → (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))) (P (inl tt)))
                        →  (e : P (inl tt))
                          (g : (x : _) → P (inr x))
                          (r : PathP (λ i → P (push north i)) e (g (f north)))
                          → (x : _) → P x
HopfInvariantPushElim n f {P = P} hlev e g r (inl x) = e
HopfInvariantPushElim n f {P = P} hlev e g r (inr x) = g x
HopfInvariantPushElim n f {P = P} hlev e g r (push a i₁) = help a i₁
  where
  help : (a : Susp (Susp (S₊ (suc (n +ℕ n))))) → PathP (λ i → P (push a i)) e (g (f a))
  help = sphereElim _ (sphereElim _ (λ _ → isProp→isOfHLevelSuc ((suc (suc (n +ℕ n)))) (isPropIsOfHLevel _))
                      (isOfHLevelPathP' (suc (suc (suc (n +ℕ n))))
                        (subst (isOfHLevel (suc (suc (suc (suc (n +ℕ n))))))
                               (cong P (push north))
                               hlev) _ _)) r


-- open import Cubical.HITs.Wedge
-- _∨→_ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--       → (f : A →∙ C) (g : B →∙ C)
--       → A ⋁ B → fst C
-- (f ∨→ g) (inl x) = fst f x
-- (f ∨→ g) (inr x) = fst g x
-- (f ∨→ g) (push a i₁) = (snd f ∙ sym (snd g)) i₁


-- add2 : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} → (f g : S₊∙ n →∙ A) → ((S₊∙ n) ⋁ (S₊∙ n) , inl (ptSn _)) →∙ A
-- fst (add2 {A = A} f g) = f ∨→ g
-- snd (add2 {A = A} f g) = snd f

-- C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
-- C* n f g = Pushout (λ _ → tt) (fst (add2 f g))

-- θ : ∀ {ℓ} {A : Pointed ℓ} → Susp (fst A) → (Susp (fst A) , north) ⋁ (Susp (fst A) , north)
-- θ north = inl north
-- θ south = inr north
-- θ {A = A} (merid a i₁) =
--      ((λ i → inl ((merid a ∙ sym (merid (pt A))) i))
--   ∙∙ push tt
--   ∙∙ λ i → inr ((merid a ∙ sym (merid (pt A))) i)) i₁


-- help3 : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
--         → p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r
-- help3 {x = x} {y = y} {z = z} {w = w} =
--   J (λ y p → (q : y ≡ z) (r : z ≡ w) →
--       (p ∙∙ q ∙∙ r) ≡ p ∙ q ∙ r)
--      λ q r → lUnit (q ∙ r)

-- +≡ : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--    → (x : _) → ∙Π f g .fst x ≡ (f ∨→ g) (θ {A = S₊∙ _} x)
-- +≡ n f g north = sym (snd f)
-- +≡ n f g south = sym (snd g)
-- +≡ n f g (merid a i₁) j = main j i₁
--   where

--   help : cong (f ∨→ g) (cong (θ {A = S₊∙ _}) (merid a))
--        ≡ (refl ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
--        ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ refl) 
--   help = cong-∙∙ (f ∨→ g) ((λ i → inl ((merid a ∙ sym (merid north)) i)))
--                            (push tt)
--                            (λ i → inr ((merid a ∙ sym (merid north)) i))
--       ∙∙ help3 _ _ _
--       ∙∙ cong (cong (f ∨→ g)
--               (λ i₂ → inl ((merid a ∙ (λ i₃ → merid north (~ i₃))) i₂)) ∙_)
--               (sym (assoc _ _ _))
--       ∙∙ assoc _ _ _
--       ∙∙ cong₂ _∙_ refl (compPath≡compPath' _ _)

--   main : PathP (λ i → snd f (~ i) ≡ snd g (~ i)) (λ i₁ → ∙Π f g .fst (merid a i₁))
--                λ i₁ → (f ∨→ g) (θ {A = S₊∙ _} (merid a i₁))
--   main = (λ i → ((λ j → snd f (~ i ∧ ~ j)) ∙∙ cong (fst f) (merid a ∙ sym (merid north)) ∙∙ snd f)
--                 ∙ (sym (snd g) ∙∙ cong (fst g) (merid a ∙ sym (merid north)) ∙∙ λ j → snd g (~ i ∧ j)))
--        ▷ sym help

-- +≡' : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--        → ∙Π f g ≡ ((f ∨→ g) ∘ (θ {A = S₊∙ _}) , snd f)
-- +≡' n f g = ΣPathP ((funExt (+≡ n f g)) , (λ j i → snd f (i ∨ ~ j)))

-- WedgeElim : (n : ℕ) → ∀ {ℓ} {P : S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) → Type ℓ}
--           → ((x : _) → isOfHLevel (3 +ℕ n) (P x))
--           → P (inl north)
--           → (x : _) → P x
-- WedgeElim n {P = P} x s (inl x₁) =
--   sphereElim _ {A = P ∘ inl}
--     (λ _ → isOfHLevelPlus' {n = n} (3 +ℕ n) (x _)) s x₁
-- WedgeElim n {P = P} x s (inr x₁) =
--   sphereElim _ {A = P ∘ inr}
--     (sphereElim _ (λ _ → isProp→isOfHLevelSuc ((suc (suc (n +ℕ n))))
--       (isPropIsOfHLevel (suc (suc (suc (n +ℕ n))))))
--         (subst (isOfHLevel ((3 +ℕ n) +ℕ n)) (cong P (push tt))
--           (isOfHLevelPlus' {n = n} (3 +ℕ n) (x _))))
--         (subst P (push tt) s) x₁
-- WedgeElim n {P = P} x s (push a j) = transp (λ i → P (push tt (i ∧ j))) (~ j) s


-- H²-C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--      → GroupIso (coHomGr (2 +ℕ n) (C* n f g)) ℤGroup
-- H²-C* n f g = compGroupIso groupIso1 (Hⁿ-Sⁿ≅ℤ (suc n))
--   where
--   help : (coHom (2 +ℕ n) (C* n f g)) → coHom (2 +ℕ n) (S₊ (2 +ℕ n))
--   help = sMap λ f → f ∘ inr


--   invMapPrim : (S₊ (2 +ℕ n) → coHomK (2 +ℕ n)) → C* n f g → coHomK (2 +ℕ n)
--   invMapPrim h (inl x) = h (ptSn _)
--   invMapPrim h (inr x) = h x
--   invMapPrim h (push a i₁) = WedgeElim n {P = λ a → h north ≡ h (fst (add2 f g) a)}
--                                                (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
--                                                (cong h (sym (snd f))) a i₁

--   invMap : coHom (2 +ℕ n) (S₊ (2 +ℕ n)) → (coHom (2 +ℕ n) (C* n f g))
--   invMap = sMap invMapPrim

--   ret1 : (x : coHom (2 +ℕ n) (S₊ (2 +ℕ n))) → help (invMap x) ≡ x
--   ret1 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
--                λ a → refl

--   ret2 : (x : (coHom (2 +ℕ n) (C* n f g))) → invMap (help x) ≡ x
--   ret2 = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
--                λ h → cong ∣_∣₂ (funExt λ { (inl x) → cong h ((λ i →  inr ((snd f) (~ i)))
--                                                            ∙ sym (push (inl north)))
--                                          ; (inr x) → refl
--                                          ; (push a i₁) → help2 h a i₁})
--     where
--     help2 : (h : C* n f g → coHomK (2 +ℕ n))
--           → (a : _) → PathP (λ i → invMapPrim (h ∘ inr) (push a i) ≡ h (push a i))
--                   (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
--                   refl
--     help2 h = WedgeElim n (λ _ → isOfHLevelPathP (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
--                         help4

--       where
--       help4 : PathP (λ i → invMapPrim (h ∘ inr) (push (inl north) i) ≡ h (push (inl north) i))
--                   (cong h ((λ i →  inr ((snd f) (~ i))) ∙ sym (push (inl north))))
--                   refl
--       help4 i j = h (hcomp (λ k → λ { (i = i1) → inr (fst f north)
--                                      ; (j = i0) → inr (snd f (~ i))
--                                      ; (j = i1) → push (inl north) (i ∨ ~ k)})
--                            (inr (snd f (~ i ∧ ~ j))))

--   groupIso1 : GroupIso ((coHomGr (2 +ℕ n) (C* n f g))) (coHomGr (2 +ℕ n) (S₊ (2 +ℕ n)))
--   Iso.fun (fst groupIso1) = help
--   Iso.inv (fst groupIso1) = invMap
--   Iso.rightInv (fst groupIso1) = ret1
--   Iso.leftInv (fst groupIso1) = ret2
--   snd groupIso1 = makeIsGroupHom
--     (sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
--            λ f g → refl)


-- C+ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Type _
-- C+ n f g = Pushout (λ _ → tt) (∙Π f g .fst)

-- H⁴-C∨ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--         → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C+ n f g))
--                     ℤGroup
-- H⁴-C∨ n f g = compGroupIso
--   (transportCohomIso (cong (3 +ℕ_) (+-suc n n))) (Hopfβ-Iso n (∙Π f g))

-- lol : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) (x : ℤ)
--          → Iso.inv (fst (H⁴-C∨ n f g)) x
--          ≡ subst (λ m → coHom m (C+ n f g)) (sym (cong (3 +ℕ_) (+-suc n n))) (Iso.inv (fst (Hopfβ-Iso n (∙Π f g))) x)
-- lol n f g = λ _ → refl

-- H²-C∨ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--       → GroupIso (coHomGr (2 +ℕ n) (C+ n f g))
--                   ℤGroup
-- H²-C∨ n f g = Hopfα-Iso n (∙Π f g)


-- H⁴-C* : ∀ n → (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--      → GroupIso (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
--                  (DirProd ℤGroup ℤGroup)
-- H⁴-C* n f g = compGroupIso (GroupEquiv→GroupIso (invGroupEquiv fstIso))
--                            (compGroupIso (transportCohomIso (cong (2 +ℕ_) (+-suc n n)))
--                              (compGroupIso (Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) _)
--                                (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ _) (Hⁿ-Sⁿ≅ℤ _))))
--   where
--   module Ms = MV _ _ _ (λ _ → tt) (fst (add2 f g))
--   fstIso : GroupEquiv (coHomGr ((suc (suc (n +ℕ suc n)))) (S₊∙ (3 +ℕ (n +ℕ n)) ⋁ S₊∙ (3 +ℕ (n +ℕ n))))
--                       (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
--   fst (fst fstIso) = Ms.d (suc (suc (n +ℕ suc n))) .fst
--   snd (fst fstIso) =
--     SES→isEquiv
--       (GroupPath _ _ .fst (compGroupEquiv (invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl)
--                           (GroupEquivDirProd
--                             (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
--                             (GroupIso→GroupEquiv
--                               (invGroupIso
--                                 (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lemHopf 0 ((λ _ → north) , refl) n n (cong suc (sym (+-suc n n)) ∙ p)))))))
--       (GroupPath _ _ .fst
--         (compGroupEquiv ((invEquiv (isContr→≃Unit ((tt , tt) , (λ _ → refl))) , makeIsGroupHom λ _ _ → refl))
--             ((GroupEquivDirProd
--                             (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Unit≅0 _)))
--                             (GroupIso→GroupEquiv
--                               (invGroupIso (Hⁿ-Sᵐ≅0 _ _ λ p → ¬lemHopf 0 ((λ _ → north) , refl) n (suc n) (cong (2 +ℕ_) (sym (+-suc n n)) ∙ p))))))))
--       (Ms.Δ (suc (suc (n +ℕ suc n))))
--       (Ms.d (suc (suc (n +ℕ suc n))))
--       (Ms.i (suc (suc (suc (n +ℕ suc n)))))
--       (Ms.Ker-d⊂Im-Δ _)
--       (Ms.Ker-i⊂Im-d _)
--   snd fstIso = Ms.d (suc (suc (n +ℕ suc n))) .snd

-- Hopfie : {n : ℕ} → ∥ S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n) ∥₂ → ℤ
-- Hopfie = sRec isSetℤ (HopfInvariant _)

-- subber : (n : ℕ) (f : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → _
-- subber n f = subst (λ x → coHom x (HopfInvariantPush n (fst f)))
--                    (λ i → suc (suc (suc (+-suc n n i)))) 

-- module _ (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) where

--   C+' = C+ n f g

--   βₗ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
--   βₗ = Iso.inv (fst (H⁴-C* n f g)) (1 , 0)

--   βᵣ : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
--   βᵣ = Iso.inv (fst (H⁴-C* n f g)) (0 , 1)

--   βᵣ'-fun : C* n f g → coHomK ((4 +ℕ (n +ℕ n)))
--   βᵣ'-fun (inl x) = 0ₖ _
--   βᵣ'-fun (inr x) = 0ₖ _
--   βᵣ'-fun (push (inl x) i₁) = 0ₖ _
--   βᵣ'-fun (push (inr x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
--   βᵣ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ (~ i₂) i₁


--   βₗ'-fun : C* n f g → coHomK (4 +ℕ (n +ℕ n))
--   βₗ'-fun (inl x) = 0ₖ _
--   βₗ'-fun (inr x) = 0ₖ _
--   βₗ'-fun (push (inl x) i₁) = Kn→ΩKn+1 _ ∣ x ∣ i₁
--   βₗ'-fun (push (inr x) i₁) = 0ₖ _
--   βₗ'-fun (push (push a i₂) i₁) = Kn→ΩKn+10ₖ _ i₂ i₁

--   βₗ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
--   βₗ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))) ∣ βₗ'-fun ∣₂

--   βᵣ''-fun : coHom ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)
--   βᵣ''-fun = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))) ∣ βᵣ'-fun ∣₂

--   α∨ : coHom (2 +ℕ n) (C* n f g)
--   α∨ = Iso.inv (fst (H²-C* n f g)) 1

--   private
--     pp : (a : _) → 0ₖ (suc (suc n)) ≡ ∣ (f ∨→ g) a ∣
--     pp = WedgeElim _ (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
--                    (cong ∣_∣ₕ (sym (snd f)))

--   pp-inr : pp (inr north) ≡ cong ∣_∣ₕ (sym (snd g))
--   pp-inr = (λ j → transport (λ i →  0ₖ (2 +ℕ n) ≡ ∣ compPath-filler' (snd f) (sym (snd g)) (~ j) i ∣ₕ)
--                              λ i → ∣ snd f (~ i ∨ j) ∣ₕ)
--          ∙ λ j → transp (λ i → 0ₖ (2 +ℕ n) ≡ ∣ snd g (~ i ∧ ~ j) ∣ₕ) j λ i → ∣ snd g (~ i ∨ ~ j) ∣ₕ

--   α∨'-fun : C* n f g → coHomK (2 +ℕ n)
--   α∨'-fun (inl x) = 0ₖ _
--   α∨'-fun (inr x) = ∣ x ∣
--   α∨'-fun (push a i₁) = pp a i₁

--   α∨' : coHom (2 +ℕ n) (C* n f g)
--   α∨' = ∣ α∨'-fun ∣₂


--   β+ : coHom ((2 +ℕ n) +' (2 +ℕ n)) C+'
--   β+ = Iso.inv (fst (H⁴-C∨ n f g)) 1

--   q : C+' → C* n f g
--   q (inl x) = inl x
--   q (inr x) = inr x
--   q (push a i₁) = (push (θ a) ∙ λ i → inr (+≡ n f g a (~ i))) i₁

--   jₗ : HopfInvariantPush n (fst f) → C* n f g
--   jₗ (inl x) = inl x
--   jₗ (inr x) = inr x
--   jₗ (push a i₁) = push (inl a) i₁

--   jᵣ : HopfInvariantPush n (fst g) → C* n f g
--   jᵣ (inl x) = inl x
--   jᵣ (inr x) = inr x
--   jᵣ (push a i₁) = push (inr a) i₁

-- α-∨→1 : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--         → Iso.fun (fst (H²-C* n f g)) (α∨' n f g) ≡ 1
-- α-∨→1 n f g = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (Hⁿ-Sⁿ≅ℤ-nice-generator n))
--              ∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)

-- α-∨-lem : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--         → α∨ n f g ≡ α∨' n f g
-- α-∨-lem n f g = sym (Iso.leftInv (fst (H²-C* n f g)) _)
--              ∙∙ cong (Iso.inv (fst (H²-C* n f g))) help
--              ∙∙ Iso.leftInv (fst (H²-C* n f g)) _
--   where
--   help : Iso.fun (fst (H²-C* n f g)) (α∨ n f g) ≡ Iso.fun (fst (H²-C* n f g)) (α∨' n f g)
--   help = (Iso.rightInv (fst (H²-C* n f g)) (pos 1)) ∙ sym (α-∨→1 n f g)

-- q-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (q n f g) (α∨ n f g) ≡ Hopfα n (∙Π f g)
-- q-α n f g = (λ i → coHomFun _ (q n f g) (α-∨-lem n f g i))
--           ∙ sym (Iso.leftInv is _)
--           ∙∙ cong (Iso.inv is) help
--           ∙∙ Iso.leftInv is _
--   where
--   is = fst (Hopfα-Iso n (∙Π f g))

--   help : Iso.fun is (coHomFun _ (q n f g) (α∨' n f g))
--        ≡ Iso.fun is (Hopfα n (∙Π f g))
--   help = sym (cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ (suc n)))) (Hⁿ-Sⁿ≅ℤ-nice-generator n))
--       ∙∙ Iso.rightInv (fst (Hⁿ-Sⁿ≅ℤ (suc n))) (pos 1)
--       ∙∙ sym (Hopfα-Iso-α n (∙Π f g))


-- βₗ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → βₗ n f g ≡ βₗ''-fun n f g
-- βₗ≡ n f g = cong (FF ∘ subber2)
--                  (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
--                                             (S₊∙ (suc (suc (suc (n +ℕ n)))))
--                                 (((suc (suc (n +ℕ n))))))))) help
--                ∙ help2)
--           ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
--           ∙ cong subber3 (sym βₗ'-fun≡)
--   where
--   FF = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (n +ℕ suc n))) .fst
--   FF' = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (suc (n +ℕ n)))) .fst

--   help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (1 , 0)
--        ≡ (∣ ∣_∣ ∣₂ , 0ₕ _)
--   help = ΣPathP ((Hⁿ-Sⁿ≅ℤ-nice-generator _) , IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))))

--   subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

--   subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
--                                (sym (cong (2 +ℕ_) (+-suc n n))))

--   FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
--   FF∘subber =
--     funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
--                    (MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) ((suc (suc (+-suc n n j)))) .fst
--                       (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
--                                             (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
--                               a))))

--   wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
--        coHomK (suc (suc (suc (n +ℕ n)))))
--   wedgeGen (inl x) = ∣ x ∣
--   wedgeGen (inr x) = 0ₖ _
--   wedgeGen (push a i₁) = 0ₖ _

--   βₗ'-fun≡ : ∣ βₗ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
--   βₗ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
--                                 ; (inr x) → refl
--                                 ; (push (inl x) i₁) → refl
--                                 ; (push (inr x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
--                                 ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ i₂) i₁})

--   help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
--                    (∣ ∣_∣ ∣₂ , 0ₕ _)
--                    ≡ ∣ wedgeGen ∣₂
--   help2 = cong ∣_∣₂ (funExt λ { (inl x) → rUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
--                              ; (inr x) → refl
--                              ; (push a i₁) → refl})

-- βᵣ≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → βᵣ n f g ≡ βᵣ''-fun n f g
-- βᵣ≡ n f g =
--     cong (FF ∘ subber2)
--       (cong (Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n)))))
--                                             (S₊∙ (suc (suc (suc (n +ℕ n)))))
--                                 (((suc (suc (n +ℕ n)))))))))
--             help
--           ∙ help2)
--   ∙ funExt⁻ FF∘subber ∣ wedgeGen ∣₂
--   ∙ cong (subber3) (sym βᵣ'-fun≡)
--   where
--   FF = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (n +ℕ suc n))) .fst
--   FF' = MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) (suc (suc (suc (n +ℕ n)))) .fst

--   help : Iso.inv (fst (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))) (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) (0 , 1)
--        ≡ (0ₕ _ , ∣ ∣_∣ ∣₂)
--   help = ΣPathP (IsGroupHom.pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc (suc (n +ℕ n)))))) , (Hⁿ-Sⁿ≅ℤ-nice-generator _))

--   subber3 = subst (λ m → coHom m (C* n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))

--   subber2 = (subst (λ m → coHom m (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n))))))
--                                (sym (cong (2 +ℕ_) (+-suc n n))))

--   FF∘subber : FF ∘ subber2 ≡ subber3 ∘ FF'
--   FF∘subber =
--     funExt (λ a → (λ j → transp (λ i → coHom ((suc ∘ suc ∘ suc) (+-suc n n (~ i ∧ j))) (C* n f g)) (~ j)
--                    (MV.d _ _ _ (λ _ → tt) (fst (add2 f g)) ((suc (suc (+-suc n n j)))) .fst
--                       (transp (λ i → coHom (2 +ℕ (+-suc n n (j ∨ ~ i)))
--                                             (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))))) j
--                               a))))

--   wedgeGen : (S₊∙ (suc (suc (suc (n +ℕ n)))) ⋁ S₊∙ (suc (suc (suc (n +ℕ n)))) →
--        coHomK (suc (suc (suc (n +ℕ n)))))
--   wedgeGen (inl x) = 0ₖ _
--   wedgeGen (inr x) = ∣ x ∣
--   wedgeGen (push a i₁) = 0ₖ _


--   help2 : Iso.inv (fst ((Hⁿ-⋁ (S₊∙ (suc (suc (suc (n +ℕ n))))) (S₊∙ (suc (suc (suc (n +ℕ n))))) (((suc (suc (n +ℕ n))))))))
--                    (0ₕ _ , ∣ ∣_∣ ∣₂)
--                    ≡ ∣ wedgeGen ∣₂
--   help2 = cong ∣_∣₂ (funExt λ { (inl x) → refl
--                              ; (inr x) → lUnitₖ (suc (suc (suc (n +ℕ n)))) ∣ x ∣
--                              ; (push a i₁) → refl})

--   βᵣ'-fun≡ : ∣ βᵣ'-fun n f g ∣₂ ≡ FF' ∣ wedgeGen ∣₂
--   βᵣ'-fun≡ = cong ∣_∣₂ (funExt λ { (inl x) → refl
--                                 ; (inr x) → refl
--                                 ; (push (inl x) i₁) j → Kn→ΩKn+10ₖ _ (~ j) i₁
--                                 ; (push (inr x) i₁) → refl
--                                 ; (push (push a i₂) i₁) j → Kn→ΩKn+10ₖ _ (~ j ∧ ~ i₂) i₁})

-- q-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (q n f g) (βₗ n f g)
--     ≡ β+ n f g
-- q-βₗ n f g = cong (coHomFun _ (q n f g)) (βₗ≡ n f g)
--            ∙ transportLem
--            ∙ cong (subst (λ m → coHom m (C+' n f g))
--                   (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--                         (sym (Iso.leftInv (fst (Hopfβ-Iso n (∙Π f g))) (Hopfβ n (∙Π f g)))
--                         ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (∙Π f g))))) (Hopfβ↦1 n (∙Π f g)))
--   where
--   transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
--       (βₗ''-fun n f g)
--      ≡ subst (λ m → coHom m (C+' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--              (Hopfβ n (∙Π f g))
--   transportLem =
--       natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--     ∙ cong (subst (λ m → coHom m (C+' n f g))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--         (cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → loll a i₁}))
--     where
--     open import Cubical.Foundations.Path
--     loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
--       PathP
--       (λ i₁ →
--          βₗ'-fun n f g ((push (θ x) ∙ λ i → inr (+≡ n f g x (~ i))) i₁) ≡
--          MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
--          (λ _ → tt) (fst (∙Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
--       (λ _ → βₗ'-fun n f g (q n f g (inl tt)))
--       (λ _ → βₗ'-fun n f g (q n f g (inr (∙Π f g .fst x))))
--     loll x =
--       flipSquare (cong-∙ (βₗ'-fun n f g) (push (θ x)) (λ i → inr (+≡ n f g x (~ i)))
--               ∙∙ sym (rUnit _)
--               ∙∙ lem₁ x)

--       where
--       lem₁ : (x : _) → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
--       lem₁ north = refl
--       lem₁ south = sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
--       lem₁ (merid a j) k = lala k j
--         where
--         lala : PathP (λ k → Kn→ΩKn+1 _ ∣ north ∣ₕ ≡ (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
--                      (λ j → cong (βₗ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
--                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
--         lala = (cong-∙∙ (cong (βₗ'-fun n f g) ∘ push)
--                         ((λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
--                         (push tt)
--                         ((λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁)))
--                         ∙ sym (compPath≡compPath' _ _)
--                         ∙ (λ _ → (λ j → Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∣ (merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) j ∣ₕ)
--                                ∙ Kn→ΩKn+10ₖ _)
--                         ∙ cong (_∙ Kn→ΩKn+10ₖ _) (cong-∙ ((Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ))
--                                (merid a) (sym (merid north)))
--                         ∙ sym (assoc _ _ _)
--                         ∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) ∙_)
--                                (sym (symDistr (sym ((Kn→ΩKn+10ₖ _))) (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))))))
--                         ◁ λ i j → compPath-filler (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
--                                                     (sym (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))))
--                                                                                      (cong ∣_∣ₕ (merid north))))
--                                                     (~ i) j

-- q-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (q n f g) (βᵣ n f g)
--     ≡ β+ n f g
-- q-βᵣ n f g = cong (coHomFun _ (q n f g)) (βᵣ≡ n f g)
--            ∙ transportLem
--            ∙ cong (subst (λ m → coHom m (C+' n f g))
--                   (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--                         (sym (Iso.leftInv (fst (Hopfβ-Iso n (∙Π f g))) (Hopfβ n (∙Π f g)))
--                         ∙ cong (Iso.inv ((fst (Hopfβ-Iso n (∙Π f g))))) (Hopfβ↦1 n (∙Π f g)))
--   where
--   transportLem : coHomFun (suc (suc (suc (n +ℕ suc n)))) (q n f g)
--       (βᵣ''-fun n f g)
--      ≡ subst (λ m → coHom m (C+' n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--              (Hopfβ n (∙Π f g))
--   transportLem =
--       natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (q n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--     ∙ cong (subst (λ m → coHom m (C+' n f g))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--         (cong ∣_∣₂ (funExt λ { (inl x) → refl
--                             ; (inr x) → refl
--                             ; (push a i₁) → loll a i₁}))
--     where
--     open import Cubical.Foundations.Path
--     loll : (x : fst (S₊∙ (3 +ℕ (n +ℕ n)))) →
--       PathP
--       (λ i₁ →
--          βᵣ'-fun n f g ((push (θ x) ∙ λ i → inr (+≡ n f g x (~ i))) i₁) ≡
--          MV.d-pre Unit (fst (S₊∙ (2 +ℕ n))) (fst (S₊∙ (3 +ℕ n +ℕ n)))
--          (λ _ → tt) (fst (∙Π f g)) (3 +ℕ n +ℕ n) ∣_∣ (push x i₁))
--       (λ _ → βᵣ'-fun n f g (q n f g (inl tt)))
--       (λ _ → βᵣ'-fun n f g (q n f g (inr (∙Π f g .fst x))))
--     loll x = flipSquare (cong-∙ (βᵣ'-fun n f g) (push (θ x)) (λ i → inr (+≡ n f g x (~ i)))
--                      ∙∙ sym (rUnit _)
--                      ∙∙ lem₁ x)
--       where
--       lem₁ : (x : _) → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} x)) ≡ Kn→ΩKn+1 _ ∣ x ∣
--       lem₁ north = sym (Kn→ΩKn+10ₖ _)
--       lem₁ south = cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))
--       lem₁ (merid a j) k = lala k j -- lala k j
--         where
--         lala : PathP (λ k → (Kn→ΩKn+10ₖ _) (~ k) ≡ (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n))))) (cong ∣_∣ₕ (merid north))) k)
--                      (λ j → cong (βᵣ'-fun n f g) (push (θ {A = S₊∙ _} (merid a j))))
--                      (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
--         lala = (cong-∙∙ (cong (βᵣ'-fun n f g) ∘ push)
--                         (λ i₁ → inl ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
--                         (push tt)
--                         (λ i₁ → inr ((merid a ∙ (sym (merid (pt (S₊∙ (suc (suc (n +ℕ n)))))))) i₁))
--              ∙∙ (cong (sym (Kn→ΩKn+10ₖ _) ∙_) (cong-∙ (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a) (sym (merid (ptSn _)))))
--              ∙∙ sym (help3 _ _ _))
--              ◁ symP (doubleCompPath-filler
--                       (sym (Kn→ΩKn+10ₖ _))
--                       (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (merid a))
--                       (cong (Kn→ΩKn+1 (suc (suc (suc (n +ℕ n)))) ∘ ∣_∣ₕ) (sym (merid north))))
-- open import Cubical.Foundations.Path
-- jₗ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jₗ n f g) (α∨ n f g)
--     ≡ Hopfα n f
-- jₗ-α n f g =
--     cong (coHomFun _ (jₗ n f g)) (α-∨-lem n f g)
--   ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst f)
--                       (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
--                         (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
--                       refl
--                       (λ _ → refl)
--                       λ j → refl))

-- jₗ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jₗ n f g) (βₗ n f g)
--     ≡ subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--             (Hopfβ n f)
-- jₗ-βₗ n f g =
--      cong (coHomFun _ (jₗ n f g)) (βₗ≡ n f g)
--   ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--   ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--         (cong ∣_∣₂
--           (funExt λ { (inl x) → refl
--                     ; (inr x) → refl
--                     ; (push a i₁) → refl}))

-- jₗ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jₗ n f g) (βᵣ n f g)
--     ≡ 0ₕ _
-- jₗ-βᵣ n f g =
--   cong (coHomFun _ (jₗ n f g)) (βᵣ≡ n f g)
--   ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jₗ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--   ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--       cool
--   where
--   cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jₗ n f g)
--       ∣ βᵣ'-fun n f g ∣₂ ≡ 0ₕ _
--   cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})

-- jᵣ-α : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jᵣ n f g) (α∨ n f g)
--     ≡ Hopfα n g
-- jᵣ-α n f g = cong (coHomFun _ (jᵣ n f g)) (α-∨-lem n f g)
--   ∙ cong ∣_∣₂ (funExt (HopfInvariantPushElim n (fst g)
--                       (isOfHLevelPath ((suc (suc (suc (suc (n +ℕ n))))))
--                         (isOfHLevelPlus' {n = n} (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n))) _ _)
--                       refl
--                       (λ _ → refl)
--                       (flipSquare (pp-inr n f g))))

-- jᵣ-βₗ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jᵣ n f g) (βₗ n f g) ≡ 0ₕ _
-- jᵣ-βₗ n f g =
--   cong (coHomFun _ (jᵣ n f g)) (βₗ≡ n f g)
--   ∙∙ natTranspLem ∣ βₗ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--   ∙∙ cong (subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--       cool
--   where
--   cool : coHomFun (suc (suc (suc (suc (n +ℕ n))))) (jᵣ n f g)
--       ∣ βₗ'-fun n f g ∣₂ ≡ 0ₕ _
--   cool = cong ∣_∣₂ (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i₁) → refl})


-- jᵣ-βᵣ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → coHomFun _ (jᵣ n f g) (βᵣ n f g)
--     ≡ subst (λ m → coHom m (HopfInvariantPush n (fst g)))
--             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--             (Hopfβ n g)
-- jᵣ-βᵣ n f g =
--   cong (coHomFun _ (jᵣ n f g)) (βᵣ≡ n f g)
--   ∙∙ natTranspLem ∣ βᵣ'-fun n f g ∣₂ (λ m → coHomFun m (jᵣ n f g)) (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--   ∙∙  cong (subst (λ m → coHom m (HopfInvariantPush n (fst g)))
--       (cong (suc ∘ suc ∘ suc) (sym (+-suc n n))))
--         (cong ∣_∣₂
--           (funExt λ { (inl x) → refl
--                     ; (inr x) → refl
--                     ; (push a i₁) → refl}))

-- gen₂ℤ×ℤ : gen₂-by (DirProd ℤGroup ℤGroup) (1 , 0) (0 , 1)
-- fst (gen₂ℤ×ℤ (x , y)) = x , y
-- snd (gen₂ℤ×ℤ (x , y)) =
--   ΣPathP ((cong₂ _+_ ((·Comm 1 x) ∙ cong fst (sym (distrLem 1 0 x))) ((·Comm 0 y) ∙ cong fst (sym (distrLem 0 1 y))))
--         , +Comm y 0 ∙ cong₂ _+_ (·Comm 0 x ∙ cong snd (sym (distrLem 1 0 x))) (·Comm 1 y ∙ cong snd (sym (distrLem 0 1 y))))
--   where
--   ℤ×ℤ = DirProd ℤGroup ℤGroup
--   _+''_ = GroupStr._·_ (snd ℤ×ℤ)

--   ll3 : (x : ℤ) → - x ≡ 0 - x
--   ll3 (pos zero) = refl
--   ll3 (pos (suc zero)) = refl
--   ll3 (pos (suc (suc n))) =
--     cong predℤ (ll3 (pos (suc n)))
--   ll3 (negsuc zero) = refl
--   ll3 (negsuc (suc n)) = cong sucℤ (ll3 (negsuc n))

--   distrLem : (x y : ℤ) (z : ℤ)
--          → Path (ℤ × ℤ) (z ℤ[ ℤ×ℤ ]· (x , y)) (z · x , z · y)
--   distrLem x y (pos zero) = refl
--   distrLem x y (pos (suc n)) =
--     (cong ((x , y) +''_) (distrLem x y (pos n)))
--   distrLem x y (negsuc zero) = ΣPathP (sym (ll3 x) , sym (ll3 y))
--   distrLem x y (negsuc (suc n)) =
--     cong₂ _+''_ (ΣPathP (sym (ll3 x) , sym (ll3 y)))
--                 (distrLem x y (negsuc n))
  
-- genH²ⁿC* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--          → gen₂-by (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
--                     (βₗ n f g)
--                     (βᵣ n f g)
-- genH²ⁿC* n f g =
--   Iso-pres-gen₂ (DirProd ℤGroup ℤGroup)
--     (coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g))
--     (1 , 0)
--     (0 , 1)
--     gen₂ℤ×ℤ
--     (invGroupIso (H⁴-C* n f g))

-- private

--   H⁴C* : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n)) → Group _
--   H⁴C* n f g = coHomGr ((2 +ℕ n) +' (2 +ℕ n)) (C* n f g)

--   X : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--       → ℤ
--   X n f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .fst .fst
--   Y : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--       → ℤ
--   Y n  f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .fst .snd

--   α∨≡ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--       → α∨ n f g ⌣ α∨ n f g ≡ ((X n f g) ℤ[ H⁴C* n f g ]· βₗ n f g)
--                             +ₕ ((Y n f g) ℤ[ H⁴C* n f g ]· βᵣ n f g)
--   α∨≡ n f g = (genH²ⁿC* n f g) (α∨ n f g ⌣ α∨ n f g) .snd


-- eq₁ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → (Hopfα n (∙Π f g)) ⌣ (Hopfα n (∙Π f g))
--     ≡ ((X n f g + Y n f g) ℤ[ coHomGr _ _ ]· (β+ n f g))
-- eq₁ n f g =
--     cong (λ x → x ⌣ x) (sym (q-α n f g) ∙ cong (coHomFun (suc (suc n)) (q n f g)) (α-∨-lem n f g))
--   ∙ cong ((coHomFun _) (q _ f g)) (cong (λ x → x ⌣ x) (sym (α-∨-lem n f g))
--                        ∙ α∨≡ n f g)
--   ∙ IsGroupHom.pres· (coHomMorph _ (q n f g) .snd) _ _
--   ∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (q n f g)) (βₗ n f g) (X n f g)
--                        ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
--                               (q-βₗ n f g))
--                (homPresℤ· (coHomMorph _ (q n f g)) (βᵣ n f g) (Y n f g)
--                        ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
--                               (q-βᵣ n f g))
--   ∙ sym (distrℤ· (coHomGr _ _) (β+ n f g) (X n f g) (Y n f g))

-- coHomFun⌣ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
--           → (n : ℕ) (x y : coHom n B)
--           → coHomFun _ f (x ⌣ y) ≡ coHomFun _ f x ⌣ coHomFun _ f y
-- coHomFun⌣ f n = sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl

-- eq₂ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → Hopfα n f ⌣ Hopfα n f
--     ≡ (X n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--             (Hopfβ n f))
-- eq₂ n f g =
--      cong (λ x → x ⌣ x) (sym (jₗ-α n f g))
--   ∙∙ sym (coHomFun⌣ (jₗ n f g) _ _ _)
--   ∙∙ cong (coHomFun _ (jₗ n f g)) (α∨≡ n f g)
--   ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jₗ n f g))) _ _
--   ∙∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (jₗ n f g)) (βₗ n f g) (X n f g))
--                 (homPresℤ· (coHomMorph _ (jₗ n f g)) (βᵣ n f g) (Y n f g)
--                           ∙ cong (λ z → (Y n f g) ℤ[ coHomGr _ _ ]· z)
--                                  (jₗ-βᵣ n f g))
--   ∙∙ cong₂ _+ₕ_ refl (rUnitℤ· (coHomGr _ _) (Y n f g))
--   ∙∙ (rUnitₕ _ _
--    ∙ cong (X n f g ℤ[ coHomGr _ _ ]·_) (jₗ-βₗ n f g))

-- eq₃ : (n : ℕ) (f g : S₊∙ (3 +ℕ (n +ℕ n)) →∙ S₊∙ (2 +ℕ n))
--     → Hopfα n g ⌣ Hopfα n g
--     ≡ (Y n f g ℤ[ coHomGr _ _ ]· subst (λ m → coHom m (HopfInvariantPush n (fst f)))
--             (cong (suc ∘ suc ∘ suc) (sym (+-suc n n)))
--             (Hopfβ n g))
-- eq₃ n f g =
--      cong (λ x → x ⌣ x) (sym (jᵣ-α n f g))
--   ∙∙ sym (coHomFun⌣ (jᵣ n f g) _ _ _)
--   ∙∙ cong (coHomFun _ (jᵣ n f g)) (α∨≡ n f g)
--   ∙∙ IsGroupHom.pres· (snd (coHomMorph _ (jᵣ n f g))) _ _
--   ∙∙ cong₂ _+ₕ_ (homPresℤ· (coHomMorph _ (jᵣ n f g)) (βₗ n f g) (X n f g)
--                           ∙ cong (λ z → (X n f g) ℤ[ coHomGr _ _ ]· z)
--                                  (jᵣ-βₗ n f g))
--                 (homPresℤ· (coHomMorph _ (jᵣ n f g)) (βᵣ n f g) (Y n f g))
--   ∙∙ cong₂ _+ₕ_ (rUnitℤ· (coHomGr _ _) (X n f g)) refl
--   ∙∙ ((lUnitₕ _ _) ∙ cong (Y n f g ℤ[ coHomGr _ _ ]·_) (jᵣ-βᵣ n f g))

-- eq₂-eq₂ : (n : ℕ) (f g : S₊∙ (suc (suc (suc (n +ℕ n)))) →∙ S₊∙ (suc (suc n)))
--         → HopfInvariant n (∙Π f g) ≡ HopfInvariant n f + HopfInvariant n g
-- eq₂-eq₂ n f g =
--       mainL
--    ∙ sym (cong₂ _+_ (help n f g) (helpg n f g))
--   where
--   transpLem : ∀ {ℓ} {G : ℕ → Group ℓ}
--              → (n m : ℕ)
--              → (x : ℤ)
--              → (p : m ≡ n)
--              → (g : fst (G n))
--              → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g) ≡ (x ℤ[ G n ]· g)
--   transpLem {G = G} n m x =
--     J (λ n p → (g : fst (G n)) → subst (fst ∘ G) p (x ℤ[ G m ]· subst (fst ∘ G) (sym p) g)
--                                 ≡ (x ℤ[ G n ]· g))
--       λ g → transportRefl _ ∙ cong (x ℤ[ G m ]·_) (transportRefl _)

--   mainL : HopfInvariant n (∙Π f g) ≡ X n f g + Y n f g
--   mainL = cong (Iso.fun (fst (Hopfβ-Iso n (∙Π f g))))
--                (cong (subst (λ x → coHom x (HopfInvariantPush n (fst (∙Π f g))))
--                             λ i₁ → suc (suc (suc (+-suc n n i₁))))
--                      (eq₁ n f g))
--        ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n (∙Π f g))))
--                (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst (∙Π f g)))} _ _
--                           (X n f g + Y n f g) (λ i₁ → suc (suc (suc (+-suc n n i₁))))
--                           (Iso.inv (fst (Hopfβ-Iso n (∙Π f g))) 1))
--        ∙∙ homPresℤ· (_ , snd (Hopfβ-Iso n (∙Π f g))) (Iso.inv (fst (Hopfβ-Iso n (∙Π f g))) 1)
--                    (X n f g + Y n f g) 
--        ∙∙ cong ((X n f g + Y n f g) ℤ[ ℤ , ℤGroup .snd ]·_)
--                (Iso.rightInv ((fst (Hopfβ-Iso n (∙Π f g)))) 1)
--        ∙∙ rUnitℤ·ℤ (X n f g + Y n f g)


--   help : (n : ℕ) (f g : _) → HopfInvariant n f ≡ X n f g
--   help n f g = cong (Iso.fun (fst (Hopfβ-Iso n f)))
--               (cong (subst (λ x → coHom x (HopfInvariantPush n (fst f)))
--                     (λ i₁ → suc (suc (suc (+-suc n n i₁))))) (eq₂ n f g))
--             ∙ cong (Iso.fun (fst (Hopfβ-Iso n f)))
--                    (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst f))} _ _
--                               (X n f g)
--                               ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
--                               (Hopfβ n f))
--             ∙ homPresℤ· (_ , snd (Hopfβ-Iso n f)) (Hopfβ n f) (X n f g)
--             ∙ cong (X n f g ℤ[ ℤ , ℤGroup .snd ]·_) (Hopfβ↦1 n f)
--             ∙ rUnitℤ·ℤ (X n f g)

--   helpg : (n : ℕ) (f g : _) → HopfInvariant n g ≡ Y n f g
--   helpg n f g =
--        cong (Iso.fun (fst (Hopfβ-Iso n g)))
--             (cong (subst (λ x → coHom x (HopfInvariantPush n (fst g)))
--                     (λ i₁ → suc (suc (suc (+-suc n n i₁)))))
--                       (eq₃ n f g))
--     ∙∙ cong (Iso.fun (fst (Hopfβ-Iso n g)))
--                    (transpLem {G = λ x → coHomGr x (HopfInvariantPush n (fst g))} _ _
--                               (Y n f g)
--                               ((cong (suc ∘ suc ∘ suc) (+-suc n n)))
--                               (Hopfβ n g))
--     ∙∙ homPresℤ· (_ , snd (Hopfβ-Iso n g)) (Hopfβ n g) (Y n f g)
--     ∙∙ cong (Y n f g ℤ[ ℤ , ℤGroup .snd ]·_) (Hopfβ↦1 n g)
--     ∙∙ rUnitℤ·ℤ (Y n f g)
