{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.CP2 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.Pushout as Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation

open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.HopfInvariant.HopfMap renaming (CP² to CP2 ; H²CP²≅ℤ to H²CP2≅ℤ)
open import Cubical.Homotopy.HSpace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws

open S¹Hopf
open IsGroupHom
open Iso

CP² : Type
CP² = Pushout {A = TotalHopf} fst λ _ → tt

characFunSpaceCP² : ∀ {ℓ} {A : Type ℓ}
  → Iso (CP² → A) (Σ[ x ∈ A ] Σ[ f ∈ (S₊ (suc (suc zero)) → A) ]
         ((y : TotalHopf) → f (fst y) ≡ x))
fun characFunSpaceCP² f = (f (inr tt)) , ((f ∘ inl ) , (λ a → cong f (push a)))
inv characFunSpaceCP² (a , f , p) (inl x) = f x
inv characFunSpaceCP² (a , f , p) (inr x) = a
inv characFunSpaceCP² (a , f , p) (push b i) = p b i
rightInv characFunSpaceCP² _ = refl
leftInv characFunSpaceCP² _ =
  funExt λ { (inl x) → refl
           ; (inr x) → refl
           ; (push a i) → refl}

H⁰CP²≅ℤ : GroupIso (coHomGr 0 CP²) ℤGroup
H⁰CP²≅ℤ =
  H⁰-connected (inr tt)
    (Pushout.elimProp _ (λ _ → squash₁)
      (sphereElim _ (λ _ → isOfHLevelSuc 1 squash₁)
        ∣ sym (push (north , base)) ∣₁)
    λ _ → ∣ refl ∣₁)

module M = MV (S₊ 2) Unit TotalHopf fst (λ _ → tt)

H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) ℤGroup
H²CP²≅ℤ = compGroupIso (BijectionIso→GroupIso bij)
            (compGroupIso (invGroupIso trivIso) (Hⁿ-Sⁿ≅ℤ 1))
  where
  isContrH¹TotalHopf : isContr (coHom 1 TotalHopf)
  isContrH¹TotalHopf =
    isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
      (isOfHLevelRetractFromIso 0 ((fst (H¹-Sⁿ≅0 1))) isContrUnit)

  isContrH²TotalHopf : isContr (coHom 2 TotalHopf)
  isContrH²TotalHopf =
    isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
      ((isOfHLevelRetractFromIso 0
        (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (sym (cong predℕ p)))) isContrUnit))

  trivIso : GroupIso (coHomGr 2 (Susp S¹)) (×coHomGr 2 (Susp S¹) Unit)
  fun (fst trivIso) x = x , 0ₕ _
  inv (fst trivIso) = fst
  rightInv (fst trivIso) (x , p) =
    ΣPathP (refl , isContr→isProp (isContrHⁿ-Unit 1) _ _)
  leftInv (fst trivIso) x = refl
  snd trivIso = makeIsGroupHom λ _ _ → refl

  bij : BijectionIso (coHomGr 2 CP²) (×coHomGr 2 (Susp S¹) Unit)
  BijectionIso.fun bij = M.i 2
  BijectionIso.inj bij x p =
    PT.rec (squash₂ _ _)
      (uncurry (λ z q
        → sym q
        ∙∙ cong (fst (M.d 1)) (isContr→isProp isContrH¹TotalHopf z (0ₕ _))
        ∙∙ (M.d 1) .snd .pres1))
      (M.Ker-i⊂Im-d 1 x p)
    where
    help : isInIm (M.d 1) x
    help = M.Ker-i⊂Im-d 1 x p
  BijectionIso.surj bij y =
    M.Ker-Δ⊂Im-i 2 y (isContr→isProp isContrH²TotalHopf _ _)


H⁴CP²≅ℤ : GroupIso (coHomGr 4 CP²) ℤGroup
H⁴CP²≅ℤ = compGroupIso (invGroupIso (BijectionIso→GroupIso bij))
          (compGroupIso help (Hⁿ-Sⁿ≅ℤ 2))
  where
  help : GroupIso (coHomGr 3 TotalHopf) (coHomGr 3 (S₊ 3))
  help = isoType→isoCohom 3 (invIso IsoS³TotalHopf)

  bij : BijectionIso (coHomGr 3 TotalHopf) (coHomGr 4 CP²)
  BijectionIso.fun bij = M.d 3
  BijectionIso.inj bij x p =
    PT.rec (squash₂ _ _)
         (uncurry (λ z q →
             sym q
          ∙∙ cong (M.Δ 3 .fst)
                (isOfHLevelΣ 1 (isContr→isProp
                  (isOfHLevelRetractFromIso 0
                    (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))) isContrUnit))
                (λ _ → isContr→isProp (isContrHⁿ-Unit 2))
                z (0ₕ _ , 0ₕ _))
          ∙∙ M.Δ 3 .snd .pres1))
         (M.Ker-d⊂Im-Δ _ x p)
  BijectionIso.surj bij y =
    M.Ker-i⊂Im-d 3 y (isOfHLevelΣ 1
      (isContr→isProp (isOfHLevelRetractFromIso 0
        (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isContrUnit))
        (λ _ → isContr→isProp (isContrHⁿ-Unit _)) _ _)


-- Characterisations of the trivial groups

private
    elim-TotalHopf : (B : TotalHopf → Type)
      → ((x : _) → isOfHLevel 3 (B x)) → B (north , base)
      → (x : _) → B x
    elim-TotalHopf =
      transport (λ i → (B : isoToPath IsoS³TotalHopf i → Type)
        → ((x : _) → isOfHLevel 3 (B x))
          → B (transp (λ j → isoToPath IsoS³TotalHopf (i ∨ ~ j)) i (north , base)) → (x : _) → B x)
          λ B hLev elim-TotalHopf → sphereElim _ (λ _ → hLev _) elim-TotalHopf

H¹-CP²≅0 : GroupIso (coHomGr 1 CP²) UnitGroup₀
H¹-CP²≅0 =
  contrGroupIsoUnit
    (isOfHLevelRetractFromIso 0 (setTruncIso characFunSpaceCP²)
    (isOfHLevelRetractFromIso 0 lem₂ lem₃))
  where
  lem₁ : (f : (Susp S¹ → coHomK 1)) → ∥ (λ _ → 0ₖ _) ≡ f ∥₁
  lem₁ f = PT.map (λ p → p)
                (Iso.fun PathIdTrunc₀Iso (isOfHLevelRetractFromIso 1
                  (fst (Hⁿ-Sᵐ≅0 0 1 (λ p → snotz (sym p)))) isPropUnit (0ₕ _) ∣ f ∣₂))

  lem₂ : Iso ∥ (Σ[ x ∈ coHomK 1 ] ( Σ[ f ∈ (Susp S¹ → coHomK 1) ] ((y : TotalHopf) → f (fst y) ≡ x))) ∥₂
             ∥ (Σ[ f ∈ (Susp S¹ → coHomK 1) ] ((y : TotalHopf) → f (fst y) ≡ 0ₖ 1)) ∥₂
  fun lem₂ = ST.map (uncurry λ x → uncurry λ f p → (λ y → (-ₖ x) +ₖ f y) , λ y → cong ((-ₖ x) +ₖ_) (p y) ∙ lCancelₖ _ x)
  inv lem₂ = ST.map λ p → 0ₖ _ , p
  rightInv lem₂ =
    ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
          λ {(f , p) → cong ∣_∣₂ (ΣPathP ((funExt (λ x → lUnitₖ _ (f x)))
          , (funExt (λ y → sym (rUnit (λ i → (-ₖ 0ₖ 1) +ₖ p y i)))
           ◁ λ j y i → lUnitₖ _ (p y i) j)))}
  leftInv lem₂ =
    ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      (uncurry (coHomK-elim _ (λ _ → isPropΠ (λ _ → squash₂ _ _))
       (uncurry λ f p → cong ∣_∣₂ (ΣPathP (refl , (ΣPathP ((funExt (λ x → lUnitₖ _ (f x)))
       , ((funExt (λ y → sym (rUnit (λ i → (-ₖ 0ₖ 1) +ₖ p y i)))
         ◁ λ j y i → lUnitₖ _ (p y i) j)))))))))

  lem₃ : isContr _
  fst lem₃ = ∣ (λ _ → 0ₖ 1) , (λ _ → refl) ∣₂
  snd lem₃ =
    ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      (uncurry λ f → PT.rec (isPropΠ (λ _ → squash₂ _ _))
      (J (λ f _ → (y : (y₁ : TotalHopf) → f (fst y₁) ≡ 0ₖ 1) →
      ∣ (λ _ → 0ₖ 1) , (λ _ _ → 0ₖ 1) ∣₂ ≡ ∣ f , y ∣₂)
      (λ y → cong ∣_∣₂ (ΣPathP ((funExt (λ z → sym (y (north , base)))) , toPathP (s y)))))
      (lem₁ f))

    where
    s : (y : TotalHopf → 0ₖ 1 ≡ 0ₖ 1)
     → transport (λ i → (_ : TotalHopf) → y (north , base) (~ i) ≡ ∣ base ∣)
                  (λ _ _ → 0ₖ 1) ≡ y
    s y = funExt (elim-TotalHopf _ (λ _ → isOfHLevelPath 3 (isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) _ _)
                 λ k → transp (λ i → y (north , base) (~ i ∧ ~ k) ≡ ∣ base ∣) k
                                λ j → y (north , base) (~ k ∨ j))

Hⁿ-CP²≅0-higher : (n : ℕ) → ¬ (n ≡ 1) → GroupIso (coHomGr (3 +ℕ n) CP²) UnitGroup₀
Hⁿ-CP²≅0-higher n p = contrGroupIsoUnit ((0ₕ _) , (λ x → sym (main x)))
  where
  h : GroupHom (coHomGr (2 +ℕ n) TotalHopf) (coHomGr (3 +ℕ n) CP²)
  h = M.d (2 +ℕ n)

  propᵣ : isProp (fst (×coHomGr (3 +ℕ n) (Susp S¹) Unit))
  propᵣ =
    isPropΣ
      (isOfHLevelRetractFromIso 1
         (fst (Hⁿ-Sᵐ≅0 (2 +ℕ n) 1 λ p → ⊥.rec (snotz (cong predℕ p)))) isPropUnit)
      λ _ → isContr→isProp (isContrHⁿ-Unit _)

  propₗ : isProp (coHom (2 +ℕ n) TotalHopf)
  propₗ = subst (λ x → isProp (coHom (2 +ℕ n) x)) (isoToPath IsoS³TotalHopf)
               (isOfHLevelRetractFromIso 1
                 (fst (Hⁿ-Sᵐ≅0 (suc n) 2 λ q → p (cong predℕ q))) isPropUnit)

  inIm : (x : coHom (3 +ℕ n) CP²) → isInIm h x
  inIm x = M.Ker-i⊂Im-d (2 +ℕ n) x (propᵣ _ _)

  main : (x : coHom (3 +ℕ n) CP²) → x ≡ 0ₕ _
  main x =
    PT.rec (squash₂ _ _)
      (uncurry (λ f p → sym p ∙∙ cong (h .fst) (propₗ f (0ₕ _)) ∙∙ pres1 (snd h)))
      (inIm x)

-- All trivial groups:
Hⁿ-CP²≅0 : (n : ℕ) → ¬ suc n ≡ 2 → ¬ suc n ≡ 4
       → GroupIso (coHomGr (suc n) CP²) UnitGroup₀
Hⁿ-CP²≅0 zero p q = H¹-CP²≅0
Hⁿ-CP²≅0 (suc zero) p q = ⊥.rec (p refl)
Hⁿ-CP²≅0 (suc (suc zero)) p q = Hⁿ-CP²≅0-higher 0 λ p → snotz (sym p)
Hⁿ-CP²≅0 (suc (suc (suc zero))) p q = ⊥.rec (q refl)
Hⁿ-CP²≅0 (suc (suc (suc (suc n)))) p q =
  Hⁿ-CP²≅0-higher (suc (suc n))
    λ p → snotz (cong predℕ p)

-- Another Brunerie number
ℤ→HⁿCP²→ℤ : ℤ → ℤ
ℤ→HⁿCP²→ℤ x =
  Iso.fun (fst H⁴CP²≅ℤ)
    (Iso.inv (fst H²CP²≅ℤ) x ⌣ Iso.inv (fst H²CP²≅ℤ) x)

brunerie2 : ℤ
brunerie2 = ℤ→HⁿCP²→ℤ 1

{-
|brunerie2|≡1 : abs (ℤ→HⁿCP²→ℤ 1) ≡ 1
|brunerie2|≡1 = refl
-}


-- Construction of an iso H⁴(CP²) ≅ ℤ sending s.t. the map
-- ℤ × ℤ → H²(CP²) × H²(CP²) → H⁴(CP²) → ℤ
-- constructed via the cup product sends (1 , 1) to 1
-- If brunerie2 computes (to 1), this could be avoided

CP²≡CP2 : Iso CP² CP2
CP²≡CP2 = compIso (equivToIso (symPushout fst (λ _ → tt))) (invIso CP²-iso)
  where
  module m = Hopf S1-AssocHSpace (sphereElim2 0 (λ _ _ → squash₁) ∣ (λ _ → base) ∣₁)
  F : (x : S₊ 2) → (m.Hopf x) → (HopfSuspS¹ (fun idIso x))
  F north y = y
  F south y = y
  F (merid x i) = toPathP lem i
    where
    lem : transport (λ i → m.Hopf (merid x i) → Glue S¹ (Border x i))
                     (λ x → x)
                    ≡ λ x → x
    lem = funExt λ z → commS¹ x (invEq (m.μ-eq x) z) ∙ secEq (m.μ-eq x) z

  F-eq : (x : S₊ 2) → isEquiv (F x)
  F-eq = suspToPropElim base (λ _ → isPropIsEquiv _) (idIsEquiv _)

  H = m.TotalSpaceHopfPush

  H≃TotalHopf : H ≃ TotalHopf
  H≃TotalHopf =
    compEquiv
    (m.TotalSpaceHopfPush→TotalSpace
     , m.isEquivTotalSpaceHopfPush→TotalSpace)
    (Σ-cong-equiv (idEquiv _)
      λ x → F x , F-eq x)

  CP²-iso : Iso CP2 (Pushout {A = TotalHopf} (λ _ → tt) fst)
  CP²-iso = pushoutIso _ _ _ _ H≃TotalHopf (idEquiv _) (idEquiv _) refl refl

Σℤ≅H⁴CP² : Σ[ ϕ₄ ∈ GroupEquiv ℤGroup (coHomGr 4 CP²) ]
           Iso.inv (fst H²CP²≅ℤ) 1 ⌣ Iso.inv (fst H²CP²≅ℤ) 1
         ≡ fst (fst ϕ₄) 1
Σℤ≅H⁴CP² = fst c , (cong (inv (fst H²CP²≅ℤ) (pos 1) ⌣_) lem ∙ snd c)
  where
  cupIsEquiv : {A B : Type₀}
    → (f : A ≃ B)
    → (e : coHom 2 A)
    → isEquiv {A = coHom 2 A} {B = coHom 4 A} (_⌣ e)
    → isEquiv {A = coHom 2 B} {B = coHom 4 B} (_⌣ coHomFun 2 (invEq f) e)
  cupIsEquiv {B = B} =
    EquivJ (λ A f →
      (e : coHom 2 A)
    → isEquiv {A = coHom 2 A} {B = coHom 4 A} (_⌣ e)
    → isEquiv {B = coHom 4 B} (_⌣ coHomFun 2 (invEq f) e))
        λ e p → subst isEquiv (help e) p
    where
    help : (e : coHom 2 B) → _⌣ e ≡ _⌣ coHomFun 2 (invEq (idEquiv B)) e
    help e i y = y ⌣ coHomFunId 2 (~ i) e

  gen' : coHom 2 CP²
  gen' = ∣ (λ { (inl x) → ∣ x ∣ ; (inr x) → 0ₖ 2 ; (push a i) → pp a i}) ∣₂
    where
    pp : (a : TotalHopf) → Path (coHomK 2) ∣ fst a ∣ₕ (0ₖ 2)
    pp = elim-TotalHopf _ (λ _ → (isOfHLevelTrunc 4 _ _)) refl


  genId : Iso.fun (fst (coHomIso 2 CP²≡CP2)) genCP² ≡ gen'
  genId = sym (Iso.leftInv (fst H²CP²≅ℤ) _)
     ∙∙ cong (Iso.inv (fst H²CP²≅ℤ)) lem
     ∙∙ Iso.leftInv (fst H²CP²≅ℤ) _
    where
    lem : Iso.fun (fst H²CP²≅ℤ) (Iso.fun (fst (coHomIso 2 CP²≡CP2)) genCP²)
        ≡ Iso.fun (fst H²CP²≅ℤ) gen'
    lem = refl

  isEquiv⌣gen' : GroupEquiv (coHomGr 2 CP²) (coHomGr 4 CP²)
  fst (fst isEquiv⌣gen') = _⌣ gen'
  snd (fst isEquiv⌣gen') =
    subst isEquiv (λ i x → x ⌣ genId i)
      ((cupIsEquiv (invEquiv (isoToEquiv CP²≡CP2))) genCP²
        (subst isEquiv (funExt (λ x → cong (x ⌣_) Gysin-e≡genCP²))
          (⌣Equiv .fst .snd)))
  snd isEquiv⌣gen' = makeIsGroupHom λ f g → rightDistr-⌣ _ _ f g _

  abstract
    main : {A B : Group₀}
         (A≃B : GroupEquiv A B)
         (Z≃A : GroupEquiv ℤGroup A)
      → Σ[ Z≃B ∈ GroupEquiv ℤGroup B ]
          fst (fst A≃B) (fst (fst Z≃A) (pos 1))
        ≡ fst (fst Z≃B) (pos 1)
    main {A = A} {B = B} =
      GroupEquivJ (λ B A≃B →
        (Z≃A : GroupEquiv ℤGroup A)
      → Σ[ Z≃B ∈ GroupEquiv ℤGroup B ]
          fst (fst A≃B) (fst (fst Z≃A) (pos 1))
        ≡ fst (fst Z≃B) (pos 1))
       (GroupEquivJ (λ A Z≃A → Σ[ ϕ ∈ GroupEquiv ℤGroup A ] fst (fst Z≃A) 1 ≡ fst (fst ϕ) 1)
         (idGroupEquiv , refl))

  lem : inv (fst H²CP²≅ℤ) (pos 1) ≡ gen'
  lem = Iso.leftInv (fst H²CP²≅ℤ) gen'

  c = main isEquiv⌣gen' (GroupIso→GroupEquiv (invGroupIso H²CP²≅ℤ))

H⁴CP²≅ℤ-pos : GroupIso (coHomGr 4 CP²) ℤGroup
H⁴CP²≅ℤ-pos = invGroupIso (GroupEquiv→GroupIso (Σℤ≅H⁴CP² .fst))

H⁴CP²≅ℤ-pos-resp⌣ : Iso.inv (fst H²CP²≅ℤ) (pos 1) ⌣ Iso.inv (fst H²CP²≅ℤ) (pos 1)
                   ≡ Iso.inv (fst H⁴CP²≅ℤ-pos) (pos 1)
H⁴CP²≅ℤ-pos-resp⌣ = Σℤ≅H⁴CP² .snd
