{-# OPTIONS --lossy-unification #-}
{-
This file contains a proof that the generator of Π₃S² has
hopf invariant ±1.
-}
module Cubical.Homotopy.HopfInvariant.HopfMap where

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Hopf
open S¹Hopf
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.HSpace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.Gysin

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sum
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
open import Cubical.Algebra.Group.GroupPath

open import Cubical.HITs.Pushout as Pushout
open import Cubical.HITs.Join
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec)

HopfMap : S₊∙ 3 →∙ S₊∙ 2
fst HopfMap x = JoinS¹S¹→TotalHopf (Iso.inv (IsoSphereJoin 1 1) x) .fst
snd HopfMap = refl

-- We use the Hopf fibration in order to connect it to the Gysin Sequence
module hopfS¹ =
  Hopf S1-AssocHSpace (sphereElim2 _ (λ _ _ → squash₁) ∣ refl ∣₁)

S¹Hopf = hopfS¹.Hopf
E* = hopfS¹.TotalSpacePush²'
IsoE*join = hopfS¹.joinIso₂
IsoTotalHopf' = hopfS¹.joinIso₁
CP² = hopfS¹.TotalSpaceHopfPush²
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
  conCP²' (push a i) = main a i
    where
    indLem : ∀ {ℓ} {A : hopfS¹.TotalSpaceHopfPush → Type ℓ}
        → ((a : _) → isProp (A a))
        → A (inl base)
        → ((a : hopfS¹.TotalSpaceHopfPush) → A a)
    indLem {A = A} p b =
      Pushout.elimProp _ p
        (sphereElim 0 (λ _ → p _) b)
        (sphereElim 0 (λ _ → p _) (subst A (push (base , base)) b))

    main : (a : hopfS¹.TotalSpaceHopfPush)
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
        → P (transp (λ j → isoToPath (invIso (IsoSphereJoin 1 1)) (i ∨ j)) i x))
        (sphereElim _ (λ _ → grp _) b)

TotalHopf→Gpd : ∀ {ℓ} (P : hopfS¹.TotalSpaceHopfPush → Type ℓ)
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
  transport (λ i → (x : ua (_ , hopfS¹.isEquivTotalSpaceHopfPush→TotalSpace) i)
          → P (transp (λ j → ua (_ , hopfS¹.isEquivTotalSpaceHopfPush→TotalSpace)
                                  (i ∨ j)) i x))
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
  lem : (a : hopfS¹.TotalSpaceHopfPush) → PathP (λ i → P (push a i)) b (s2 _)
  lem = TotalHopf→Gpd _  (λ _ → isOfHLevelPathP' 3 (grp _) _ _) pp

-- The function inducing the iso H²(S²) ≅ H²(CP²)
H²S²→H²CP²-raw : (S₊ 2 → coHomK 2) → (CP² → coHomK 2)
H²S²→H²CP²-raw f (inl x) = 0ₖ _
H²S²→H²CP²-raw f (inr x) = f x -ₖ f north
H²S²→H²CP²-raw f (push a i) =
    TotalHopf→Gpd (λ x → 0ₖ 2
  ≡ f (hopfS¹.TotalSpaceHopfPush→TotalSpace x .fst) -ₖ f north)
      (λ _ → isOfHLevelTrunc 4 _ _)
      (sym (rCancelₖ 2 (f north)))
      a i

H²S²→H²CP² : coHomGr 2 (S₊ 2) .fst → coHomGr 2 CP² .fst
H²S²→H²CP² = sMap H²S²→H²CP²-raw

cancel-H²S²→H²CP² : (f : CP² → coHomK 2)
  → ∥ H²S²→H²CP²-raw (f ∘ inr) ≡ f ∥₁
cancel-H²S²→H²CP² f =
  pRec squash₁
    (λ p → pRec squash₁
                (λ f → ∣ funExt f ∣₁)
                (cancelLem p))
    (connLem (f (inl tt)))
  where
  connLem : (x : coHomK 2) →  ∥ x ≡ 0ₖ 2 ∥₁
  connLem = coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash₁) ∣ refl ∣₁

  cancelLem : (p : f (inl tt) ≡ 0ₖ 2)
    → ∥ ((x : CP²) → H²S²→H²CP²-raw (f ∘ inr) x ≡ f x) ∥₁
  cancelLem p = trRec squash₁ (λ pp →
    ∣ CP²→Groupoid (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
                 (sym p)
                 (λ x → (λ i → f (inr x) -ₖ f (push (inl base) (~ i)))
                       ∙∙ (λ i → f (inr x) -ₖ p i)
                       ∙∙ rUnitₖ 2 (f (inr x))) pp ∣₁)
                help
    where
    help :
      hLevelTrunc 1
        (PathP (λ i₁ → H²S²→H²CP²-raw (f ∘ inr) (push (inl base) i₁)
                     ≡ f (push (inl base) i₁))
              (sym p)
              (((λ i₁ → f (inr north) -ₖ f (push (inl base) (~ i₁))) ∙∙
                (λ i₁ → f (inr north) -ₖ p i₁) ∙∙ rUnitₖ 2 (f (inr north)))))
    help = isConnectedPathP 1 (isConnectedPath 2 (isConnectedKn 1) _ _) _ _ .fst

H²CP²≅H²S² : GroupIso (coHomGr 2 CP²) (coHomGr 2 (S₊ 2))
Iso.fun (fst H²CP²≅H²S²) = sMap (_∘ inr)
Iso.inv (fst H²CP²≅H²S²) = H²S²→H²CP²
Iso.rightInv (fst H²CP²≅H²S²) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    λ f → trRec {B = Iso.fun (fst H²CP²≅H²S²) (Iso.inv (fst H²CP²≅H²S²) ∣ f ∣₂)
                   ≡ ∣ f ∣₂}
    (isOfHLevelPath 2 squash₂ _ _)
    (λ p → cong ∣_∣₂ (funExt λ x → cong (λ y → (f x) -ₖ y) p ∙ rUnitₖ 2 (f x)))
    (Iso.fun (PathIdTruncIso _)
             (isContr→isProp (isConnectedKn 1) ∣ f north ∣ ∣ 0ₖ 2 ∣))
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
snd (fst ⌣Equiv) = isEq⌣
  where
  isEq⌣ : isEquiv (GysinS².⌣-hom 2 .fst)
  isEq⌣ =
    SES→isEquiv
      (GroupPath _ _ .fst (invGroupEquiv
        (isContr→≃Unit isContrH³E
        , makeIsGroupHom λ _ _ → refl)))
      (GroupPath _ _ .fst (invGroupEquiv
        (isContr→≃Unit isContrH⁴E
        , makeIsGroupHom λ _ _ → refl)))
      (GysinS².susp∘ϕ 1)
      (GysinS².⌣-hom 2)
      (GysinS².p-hom 4)
      (GysinS².Ker-⌣e⊂Im-Susp∘ϕ _)
      (GysinS².Ker-p⊂Im-⌣e _)
snd ⌣Equiv = GysinS².⌣-hom 2 .snd

-- The generator of H²(CP²)
genCP² : coHom 2 CP²
genCP² = ∣ CP²→Groupoid (λ _ → isOfHLevelTrunc 4)
                      (0ₖ _)
                      ∣_∣
                      refl ∣₂

inrInjective : (f g : CP² → coHomK 2) → ∥ f ∘ inr ≡ g ∘ inr ∥₁
             → Path (coHom 2 CP²) ∣ f ∣₂ ∣ g ∣₂
inrInjective f g = pRec (squash₂ _ _)
  (λ p → pRec (squash₂ _ _) (λ id → trRec (squash₂ _ _)
               (λ pp → cong ∣_∣₂
                 (funExt (CP²→Groupoid
                           (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
                         id
                         (funExt⁻ p)
                         (compPathR→PathP pp))))
                   (conn2 (f (inl tt)) (g (inl tt)) id
                     (cong f (push (inl base))
                       ∙ (funExt⁻ p north) ∙ cong g (sym (push (inl base))))))
               (conn (f (inl tt)) (g (inl tt))))

  where
  conn : (x y : coHomK 2) → ∥ x ≡ y ∥₁
  conn = coHomK-elim _ (λ _ → isSetΠ λ _ → isOfHLevelSuc 1 squash₁)
           (coHomK-elim _ (λ _ → isOfHLevelSuc 1 squash₁) ∣ refl ∣₁)

  conn2 : (x y : coHomK 2) (p q : x ≡ y) → hLevelTrunc 1 (p ≡ q)
  conn2 x y p q =
    Iso.fun (PathIdTruncIso _)
      (isContr→isProp (isConnectedPath _ (isConnectedKn 1) x y) ∣ p ∣ ∣ q ∣)

-- A couple of basic lemma concerning the hSpace structure on S¹
private
  invLooperLem₁ : (a x : S¹)
    → (invEq (hopfS¹.μ-eq a) x) * a ≡ (invLooper a * x) * a
  invLooperLem₁ a x =
       secEq (hopfS¹.μ-eq a) x
    ∙∙ cong (_* x) (rCancelS¹ a)
    ∙∙ AssocHSpace.μ-assoc S1-AssocHSpace a (invLooper a) x
     ∙ commS¹ _ _

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
Gysin-e≡genCP² =
  inrInjective _ _ ∣ funExt (λ x → funExt⁻ (cong fst (main x)) south) ∣₁
  where
  mainId : (x : Σ (S₊ 2) hopfS¹.Hopf)
         → Path (hLevelTrunc 4 _) ∣ fst x ∣ ∣ north ∣
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
          cong (transport (λ i₁
               → Path (HubAndSpoke (Susp S¹) 3) ∣ merid a i₁ ∣ ∣ north ∣))
               ((λ i → (λ z → cong ∣_∣ₕ
                         (merid base
                        ∙ sym (merid (transport
                            (λ j → uaInvEquiv (hopfS¹.μ-eq a) (~ i) j) x))) z))
               ∙ λ i → cong ∣_∣ₕ (merid base
                     ∙ sym (merid (transportRefl (invEq (hopfS¹.μ-eq a) x) i))))
      ∙∙ (λ i → transp (λ i₁ → Path (HubAndSpoke (Susp S¹) 3)
                                      ∣ merid a (i₁ ∨ i) ∣ ∣ north ∣) i
                        (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                          (cong ∣_∣ₕ (merid base
                                  ∙ sym (merid (invLooperLem₂ a x i)))) i))
      ∙∙ cong ((cong ∣_∣ₕ) (sym (merid a)) ∙_)
          (cong (cong ∣_∣ₕ) (cong sym (symDistr (merid base)
                                               (sym (merid (invLooper a * x)))))
         ∙ cong sym (SuspS¹-hom (invLooper a) x)
         ∙ symDistr ((cong ∣_∣ₕ) (merid (invLooper a) ∙ sym (merid base)))
                     ((cong ∣_∣ₕ) (merid x ∙ sym (merid base)))
         ∙ isCommΩK 2 (sym (λ i₁ → ∣ (merid x
                                   ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
                      (sym (λ i₁ → ∣ (merid (invLooper a)
                                   ∙ (λ i₂ → merid base (~ i₂))) i₁ ∣))
         ∙ cong₂ _∙_ (cong sym (SuspS¹-inv a)
                       ∙ cong-∙ ∣_∣ₕ (merid a) (sym (merid base)))
                     (cong (cong ∣_∣ₕ) (symDistr (merid x) (sym (merid base)))
                       ∙ cong-∙ ∣_∣ₕ (merid base) (sym (merid x))))
      ∙∙ (λ j → (λ i₁ → ∣ merid a (~ i₁ ∨ j) ∣) ∙ ((λ i₁ → ∣ merid a (i₁ ∨ j) ∣)
                 ∙ (λ i₁ → ∣ merid base (~ i₁ ∨ j) ∣))
                 ∙ (λ i₁ → ∣ merid base (i₁ ∨ j) ∣)
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
           ∙ (funExt lem)
    where
    lem : (qb : _) →
       ∣ (subst (fst ∘ preThom.Q (CP² , inl tt) fibr)
                (sym (push (inl base))) qb) ∣
      ≡ gen' north .fst qb
    lem north = refl
    lem south = cong ∣_∣ₕ (sym (merid base))
    lem (merid a i) j =
      hcomp (λ k →
        λ { (i = i0) → ∣ merid a (~ k ∧ j) ∣
          ; (i  = i1) → ∣ merid base (~ j) ∣
          ; (j = i0) → ∣ transportRefl (merid a i) (~ k) ∣
          ; (j = i1) → ∣ compPath-filler
                          (merid base) (sym (merid a)) k (~ i) ∣ₕ})
            (hcomp (λ k →
              λ { (i = i0) → ∣ merid a (j ∨ ~ k) ∣
                ; (i  = i1) → ∣ merid base (~ j ∨ ~ k) ∣
                ; (j = i0) → ∣ merid a (~ k ∨ i) ∣
                ; (j = i1) → ∣ merid base (~ i ∨ ~ k) ∣ₕ})
             ∣ south ∣)

  setHelp : (x : S₊ 2)
    → isSet (preThom.Q (CP² , inl tt) fibr (inr x) →∙ coHomK-ptd 2)
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
  hopfS¹.TotalSpaceHopfPush→TotalSpace
    (Iso.inv IsoTotalHopf'
      (Iso.inv (IsoSphereJoin 1 1) x)) .fst

hopfMap≡HopfMap' : HopfMap ≡ (HopfMap' , refl)
hopfMap≡HopfMap' =
  ΣPathP ((funExt (λ x →
            cong (λ x → JoinS¹S¹→TotalHopf x .fst)
              (sym (Iso.rightInv IsoTotalHopf'
                   (Iso.inv (IsoSphereJoin 1 1) x)))
             ∙ sym (lem (Iso.inv IsoTotalHopf'
                   (Iso.inv (IsoSphereJoin 1 1) x)))))
         , flipSquare (sym (rUnit refl) ◁ λ _ _ → north))
  where
  lem : (x : _) → hopfS¹.TotalSpaceHopfPush→TotalSpace x .fst
               ≡ JoinS¹S¹→TotalHopf (Iso.fun IsoTotalHopf' x) .fst
  lem (inl x) = refl
  lem (inr x) = refl
  lem (push (base , snd₁) i) = refl
  lem (push (loop i₁ , a) i) k = merid (rotLoop² a (~ k) i₁) i

CP²' : Type _
CP²' = Pushout {A = S₊ 3} (λ _ → tt) HopfMap'

PushoutReplaceBase : ∀ {ℓ ℓ' ℓ''} {A B : Type ℓ} {C : Type ℓ'} {D : Type ℓ''}
       {f : A → C} {g : A → D} (e : B ≃ A)
    → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g
PushoutReplaceBase {f = f} {g = g} =
  EquivJ (λ _ e → Pushout (f ∘ fst e) (g ∘ fst e) ≡ Pushout f g) refl

CP2≡CP²' : CP²' ≡ CP²
CP2≡CP²' =
  PushoutReplaceBase
    (isoToEquiv (compIso (invIso (IsoSphereJoin 1 1)) (invIso IsoTotalHopf')))

-- packaging everything up:
⌣equiv→pres1 : ∀ {ℓ} {G H : Type ℓ} → (G ≡ H)
        → (g₁ : coHom 2 G) (h₁ : coHom 2 H)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ]
                      abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 H) ℤGroup ]
                      abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 H) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1
⌣equiv→pres1 {G = G} = J (λ H _ → (g₁ : coHom 2 G) (h₁ : coHom 2 H)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ]
                      abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 H) ℤGroup ]
                       abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 H) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1)
              help
  where
  help : (g₁ h₁ : coHom 2 G)
        → (fstEq : (Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ]
                      abs (fst (fst ϕ) g₁) ≡ 1))
        → (sndEq : ((Σ[ ϕ ∈ GroupEquiv (coHomGr 2 G) ℤGroup ]
                       abs (fst (fst ϕ) h₁) ≡ 1)))
        → isEquiv {A = coHom 2 G} {B = coHom 4 G} (_⌣ g₁)
        → (3rdEq : GroupEquiv (coHomGr 4 G) ℤGroup)
        → abs (fst (fst 3rdEq) (h₁ ⌣ h₁)) ≡ 1
  help g h (ϕ , idg) (ψ , idh) ⌣eq ξ =
    ⊎→abs _ _
      (groupEquivPresGen _
        (compGroupEquiv main (compGroupEquiv (invGroupEquiv main) ψ))
        h (abs→⊎ _ _ (cong abs (cong (fst (fst ψ)) (retEq (fst main) h))
                     ∙ idh)) (compGroupEquiv main ξ))
    where
    lem₁ : ((fst (fst ψ) h) ≡ 1) ⊎ (fst (fst ψ) h ≡ -1)
      → abs (fst (fst ϕ) h) ≡ 1
    lem₁ p = ⊎→abs _ _ (groupEquivPresGen _ ψ h p ϕ)

    lem₂ : ((fst (fst ϕ) h) ≡ 1) ⊎ (fst (fst ϕ) h ≡ -1)
          → ((fst (fst ϕ) g) ≡ 1) ⊎ (fst (fst ϕ) g ≡ -1)
          → (h ≡ g) ⊎ (h ≡ (-ₕ g))
    lem₂ (inl x) (inl x₁) =
      inl (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) (x ∙ sym x₁)
        ∙∙ retEq (fst ϕ) g)
    lem₂ (inl x) (inr x₁) =
      inr (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) x
         ∙ IsGroupHom.presinv (snd (invGroupEquiv ϕ)) (negsuc zero)
         ∙∙ cong (-ₕ_) (cong (invEq (fst ϕ)) (sym x₁) ∙ (retEq (fst ϕ) g)))
    lem₂ (inr x) (inl x₁) =
      inr (sym (retEq (fst ϕ) h)
        ∙∙ cong (invEq (fst ϕ)) x
        ∙∙ (IsGroupHom.presinv (snd (invGroupEquiv ϕ)) 1
          ∙ cong (-ₕ_) (cong (invEq (fst ϕ)) (sym x₁) ∙ (retEq (fst ϕ) g))))
    lem₂ (inr x) (inr x₁) =
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

    lem₃ : (h ≡ g) ⊎ (h ≡ (-ₕ g)) → isEquiv {A = coHom 2 G} (_⌣ h)
    lem₃ (inl x) = subst isEquiv (λ i → _⌣ (x (~ i))) ⌣eq
    lem₃ (inr x) =
      subst isEquiv (funExt (λ x → -ₕDistᵣ 2 2 x g) ∙ (λ i → _⌣ (x (~ i))))
            (theEq .snd)

    main : GroupEquiv (coHomGr 2 G) (coHomGr 4 G)
    fst main = _ ,
      (lem₃ (lem₂ (abs→⊎ _ _ (lem₁ (abs→⊎ _ _ idh))) (abs→⊎ _ _ idg)))
    snd main =
      makeIsGroupHom λ g1 g2 → rightDistr-⌣ _ _ g1 g2 h

-- The hopf invariant is ±1 for both definitions of the hopf map
HopfInvariant-HopfMap' :
  abs (HopfInvariant zero (HopfMap' , λ _ → HopfMap' (snd (S₊∙ 3)))) ≡ 1
HopfInvariant-HopfMap' =
  cong abs (cong (Iso.fun (fst (Hopfβ-Iso zero (HopfMap' , refl))))
           (transportRefl (⌣-α 0 (HopfMap' , refl))))
            ∙ ⌣equiv→pres1 (sym CP2≡CP²')
                GysinS².e (Hopfα zero (HopfMap' , refl))
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

HopfInvariant-HopfMap : abs (HopfInvariant zero HopfMap) ≡ 1
HopfInvariant-HopfMap = cong abs (cong (HopfInvariant zero) hopfMap≡HopfMap')
                      ∙ HopfInvariant-HopfMap'
