{-# OPTIONS --safe --experimental-lossy-unification #-}
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
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation

open import Cubical.Homotopy.Hopf

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct

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
    (PushoutToProp (λ _ → squash₁)
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


open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.Homotopy.Connected

pre-H : join S¹ S¹ → S₊ 2
pre-H (inl x) = north
pre-H (inr x) = north
pre-H (push a b i) = (merid (a * invLooper b) ∙ sym (merid base)) i

H : S₊ 3 → S₊ 2
H = pre-H ∘ Iso.inv (IsoSphereJoin 1 1)

CP' : Type
CP' = Pushout (λ _ → tt) H

crunchy : (f : CP' → coHomK 4)
        → f ∘ inr ≡ (λ _ → 0ₖ 4)
        → f (inl tt) ≡ 0ₖ 4
        → (S₊ 3 → coHomK 3)
crunchy f p q x = ΩKn+1→Kn 3 (sym q ∙∙ cong f (push x) ∙∙ funExt⁻ p (H x))

abra : (f : S₊ 2 → coHomK 4) → ∥ (f ≡ λ _ → 0ₖ 4) ∥₂
abra f = main
  where
  abstract
    main : ∥ (f ≡ λ _ → 0ₖ 4) ∥₂
    main =
      Trunc.rec
        (isOfHLevelPlus 2 squash₂)
        (λ fn
          → Trunc.rec (isOfHLevelPlus 2 squash₂)
            (λ fs → Trunc.rec
              (isOfHLevelSuc 2 squash₂)
              (λ f≡s → Trunc.rec squash₂
                (λ surf → ∣ funExt (λ { north → fn
                                      ; south → fs
                                      ; (merid base i) → f≡s i
                                      ; (merid (loop i) j) k → surf i j k}) ∣₂)
                  (help fn fs f≡s))
              (isConnectedPathP 3 {A = λ i → f (merid base i) ≡ 0ₖ 4}
                (isConnectedPathKn 3 _ _) fn fs .fst))
            (isConnectedPathKn 3 (f south) (0ₖ 4) .fst))
        (isConnectedPathKn 3 (f north) (0ₖ 4) .fst)
      where
      help : (fn : f north ≡ 0ₖ 4) → (fs : f south ≡ 0ₖ 4)
           → (f≡s : PathP (λ i₁ → f (merid base i₁) ≡ 0ₖ 4) fn fs)
           → hLevelTrunc 2
                 (Cube (λ j k → f≡s j k) (λ j k → f≡s j k)
                       (λ i k → fn k) (λ i k → fs k)
                       (λ i j → f (merid (loop i) j)) refl)
      help fn fs f≡s =
        isConnectedPathP 2
          (isConnectedPathP 3 (isConnectedPathKn 3 _ _) _ _) _ _ .fst

blahem : coHom 4 CP' → coHom 3 (S₊ 3)
blahem =
  ST.rec squash₂
    λ f
      → Trunc.rec
          (isOfHLevelPlus 2 squash₂)
          (λ p → ST.rec squash₂ (λ q → ∣ crunchy f q p ∣₂)
          (abra (f ∘ inr)))
          (isConnectedPathKn 3 (f (inl tt)) (0ₖ 4) .fst)


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

-- {-
-- |brunerie2|≡1 : abs (ℤ→HⁿCP²→ℤ 1) ≡ 1
-- |brunerie2|≡1 = refl
-- -}

-- open import Cubical.Homotopy.HopfInvariant.HopfMap renaming (CP² to CP2 ; H²CP²≅ℤ to H²CP2≅ℤ)
-- open import Cubical.Homotopy.HopfInvariant.Base
-- open import Cubical.Homotopy.Hopf
-- open import Cubical.ZCohomology.Gysin
-- open import Cubical.Homotopy.HSpace
-- open import Cubical.HITs.S1 renaming (_·_ to _*_)

-- CP²≡CP2 : CP² ≡ CP2
-- CP²≡CP2 = isoToPath (compIso (equivToIso (symPushout fst (λ _ → tt))) (invIso CP²-iso))
--   where
--   module m = Hopf S1-AssocHSpace (sphereElim2 0 (λ _ _ → squash₁) ∣ (λ _ → base) ∣₁)
--   funi : (x : S₊ 2) → (m.Hopf x) → (HopfSuspS¹ (fun idIso x))
--   funi north y = y
--   funi south y = y
--   funi (merid x i) = toPathP help i
--     where
--     help : transport (λ i → m.Hopf (merid x i) → Glue S¹ (Border x i))
--                      (λ x → x)
--                     ≡ λ x → x
--     help = funExt λ z → commS¹ x (invEq (m.μ-eq x) z) ∙ secEq (m.μ-eq x) z


--   funi-eq : (x : S₊ 2) → isEquiv (funi x)
--   funi-eq = suspToPropElim base (λ _ → isPropIsEquiv _) (idIsEquiv _)

--   H1 = m.TotalSpaceHopfPush

--   Iso₁ : H1 ≃ TotalHopf
--   Iso₁ = compEquiv (m.TotalSpaceHopfPush→TotalSpace , m.isEquivTotalSpaceHopfPush→TotalSpace)
--                  (Σ-cong-equiv (idEquiv _)
--                    λ x → funi x , funi-eq x)

--   CP²-flip : CP² ≃ (Pushout {A = TotalHopf} (λ _ → tt) fst)
--   CP²-flip = symPushout fst (λ _ → tt)

--   CP²-iso : Iso CP2 (Pushout {A = TotalHopf} (λ _ → tt) fst)
--   CP²-iso =
--     pushoutIso _ _ _ _
--       Iso₁
--       (idEquiv _)
--       (idEquiv _)
--       refl
--       refl


-- cupIsEquiv : ∀ {ℓ} {A B : Type ℓ}
--   → A ≡ B
--   → {!!}
-- cupIsEquiv = {!!}


-- garam-type : (A B : Type)
--   → Type
-- garam-type A B =
--   (ϕ₂ : GroupIso (coHomGr 2 A) ℤGroup)
--   → (ϕ₄ : GroupIso (coHomGr 4 A) ℤGroup)
--   → (ψ₂ : GroupIso (coHomGr 2 B) ℤGroup)
--   → (ψ₄ : GroupIso (coHomGr 4 B) ℤGroup)
--   → (a₁ : (coHom 2 A)) (b₁ : (coHom 2 B))
--   → Iso.fun (fst ϕ₂) a₁ ≡ Iso.fun (fst ψ₂) b₁
--   → abs (Iso.fun (fst ϕ₄) (a₁ ⌣ a₁)) ≡ 1 
--   → abs (Iso.fun (fst ψ₄) (b₁ ⌣ b₁)) ≡ 1

-- open import Cubical.Algebra.Group.GroupPath
-- open import Cubical.Data.Sum as ⊎
-- open import Cubical.Algebra.Group.ZAction
-- open import Cubical.ZCohomology.RingStructure.RingLaws
-- garam-masala : {A B : Type}
--   → A ≡ B
--   → garam-type A B
-- garam-masala {A = A} =
--   J (λ B _ → garam-type A B) lem
--   where
--   lem : garam-type A A
--   lem ϕ₂ ϕ₄ ψ₂ ψ₄ a₁ b₁ p1 p3 =
--     ⊎.rec (λ p → cong abs (cong (fun (fst ψ₄)) (smile≡ s) ∙ funExt⁻ (cong invEq (cong fst p)) (a₁ ⌣ a₁)) ∙ p3)
--           (λ p → (cong abs (cong (fun (fst ψ₄)) (smile≡ s) ∙ funExt⁻ (cong invEq (cong fst p)) (a₁ ⌣ a₁)) ∙ abs- (fun (fst ϕ₄) (a₁ ⌣ a₁))) ∙ p3)
--       (characIso2
--         (GroupIso→GroupEquiv (invGroupIso ϕ₄))
--           (GroupIso→GroupEquiv (invGroupIso ψ₄)))
--     where
--     characIso2 : {G : Group ℓ-zero}
--       (ψ ϕ : GroupEquiv ℤGroup G)
--         → (ϕ ≡ ψ) ⊎ (ϕ ≡ compGroupEquiv negEquivℤ ψ)
--     characIso2 =
--       GroupEquivJ
--         (λ G ψ → (ϕ : GroupEquiv ℤGroup G)
--                → (ϕ ≡ ψ) ⊎ (ϕ ≡ compGroupEquiv negEquivℤ ψ))
--         λ ϕ → ⊎.rec inl (λ p → inr (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--                            (Σ≡Prop (λ _ → isPropIsEquiv _)
--                              (cong fst (cong fst p)))))
--                         (characℤ≅ℤ ϕ)

--     s : (GroupIso→GroupEquiv (invGroupIso ψ₂) ≡
--        GroupIso→GroupEquiv (invGroupIso ϕ₂))
--       ⊎
--       (GroupIso→GroupEquiv (invGroupIso ψ₂) ≡
--        compGroupEquiv negEquivℤ (GroupIso→GroupEquiv (invGroupIso ϕ₂)))
--     s = (characIso2
--         (GroupIso→GroupEquiv (invGroupIso ϕ₂))
--           (GroupIso→GroupEquiv (invGroupIso ψ₂)))

--     smile≡ : (GroupIso→GroupEquiv (invGroupIso ψ₂) ≡
--        GroupIso→GroupEquiv (invGroupIso ϕ₂))
--       ⊎
--       (GroupIso→GroupEquiv (invGroupIso ψ₂) ≡
--        compGroupEquiv negEquivℤ (GroupIso→GroupEquiv (invGroupIso ϕ₂)))
--        → b₁ ⌣ b₁ ≡ a₁ ⌣ a₁ 
--     smile≡ (inl x) = cong (λ x → x ⌣ x) (sym (Iso.leftInv (fst ϕ₂) b₁)
--                    ∙ cong (Iso.inv (fst ϕ₂)) (funExt⁻ (sym (cong invEq (cong fst x))) b₁ ∙ sym p1)
--                    ∙ Iso.leftInv (fst ϕ₂) a₁)
--     smile≡ (inr x) =
--         sym (-ₕDistₗᵣ 2 2 b₁ b₁)
--       ∙ cong (λ x → x ⌣ x) (cong -ₕ_ (sym (Iso.leftInv (fst ϕ₂) b₁))
--                            ∙ sym (IsGroupHom.presinv (invGroupIso ϕ₂ .snd) (Iso.fun (fst ϕ₂) b₁))
--                            ∙ cong (Iso.inv (fst ϕ₂)) (funExt⁻ (sym (cong invEq (cong fst x))) b₁ ∙ sym p1)
--                            ∙ Iso.leftInv (fst ϕ₂) a₁)


-- CP'' : Type
-- CP'' = Pushout pre-H (λ _ → tt)

-- open import Cubical.Foundations.Path
-- abstr : (a : join S¹ S¹) → Path (coHomK 2) ∣ pre-H a ∣ₕ (0ₖ 2)
-- abstr (inl x) = (Kn→ΩKn+1 1 ∣ x ∣ₕ)
-- abstr (inr x) = sym (Kn→ΩKn+1 1 ∣ invLooper x ∣ₕ)
-- abstr (push a b i) = help2 a b i
--   where
--   help2 : (a b : S¹) → PathP (λ i → Path (∥ Susp S¹ ∥ 4)
--       ∣ (merid (a * invLooper b) ∙ (λ i₁ → merid base (~ i₁))) i ∣ (0ₖ 2))
--       (Kn→ΩKn+1 1 ∣ a ∣) (sym (Kn→ΩKn+1 1 ∣ invLooper b ∣))
--   help2 = wedgeconFun 0 0 (λ _ _ → isOfHLevelPathP' 2 (isOfHLevelTrunc 4 _ _) _ _)
--             (λ a → Kn→ΩKn+10ₖ 1 ◁ λ i j → Kn→ΩKn+1 1 ∣ invLooper a ∣ (i ∧ ~ j))
--             (λ b → flipSquare (cong (Kn→ΩKn+1 1) (cong ∣_∣ₕ (rUnitS¹ b))
--                   ◁ (λ i j → Kn→ΩKn+1 1 ∣ b ∣ (i ∨ j) ))
--                   ▷ cong sym (sym (Kn→ΩKn+10ₖ 1)))
--             {!!}


-- {- transport (λ i → (a : ua (isoToEquiv (invIso (IsoSphereJoin 1 1))) i) → Path (coHomK 2)
--                  ∣ pre-H (ua-unglue (isoToEquiv (invIso (IsoSphereJoin 1 1))) i a) ∣ₕ (0ₖ 2))
--                  (sphereElim 2 (λ _ → isOfHLevelTrunc 4 _ _) refl)
-- -}

-- genCP'' : coHom 2 CP''
-- genCP'' = ∣ (λ { (inl x) → ∣ x ∣ ; (inr x) → 0ₖ 2 ; (push a i) → abstr a i}) ∣₂


-- genH⁴ : coHom 4 CP''
-- genH⁴ = ∣ (λ { (inl x) → 0ₖ 4 ; (inr x) → 0ₖ 4 ; (push a i) → Kn→ΩKn+1 3 (∣ fun (IsoSphereJoin 1 1) a ∣ₕ) i}) ∣₂

-- genH⁴≡ : genH⁴ ≡ genCP'' ⌣ genCP''
-- genH⁴≡ = cong ∣_∣₂
--   (funExt λ { (inl x) → cool x
--             ; (inr x) → refl
--             ; (push (inl x) i) j → cool123 x j i
--             ; (push (inr x) i) j → cool4 x j i
--             ; (push (push a b k) i) j → thc a b k i j})
--   where
--   cool : (x : S₊ 2) → 0ₖ 4 ≡ ∣ x ∣ ⌣ₖ ∣ x ∣
--   cool north = refl
--   cool south = refl
--   cool (merid a i) j = help (~ j) i
--     where
--     help : cong (λ x → ∣ x ∣ ⌣ₖ ∣ x ∣) (merid a) ≡ (refl {x = 0ₖ 4})
--     help = cong₂Funct (λ x y → _⌣ₖ_ {n = 2} {m = 2} ∣ x ∣ₕ ∣ y ∣ₕ) (merid a) (merid a)
--          ∙ sym (rUnit _)
--          ∙ λ i j → ⌣ₖ-0ₖ 2 2 (∣ merid a j ∣ₕ) i

--   cool4 : (x : S¹)
--     →  Kn→ΩKn+1 3 ∣ south ∣
--       ≡ sym (cong (λ x → _⌣ₖ_ {n = 2} {m = 2} x x) (Kn→ΩKn+1 1 ∣ invLooper x ∣))
--   cool4 = λ x → (cong (Kn→ΩKn+1 3) (cong ∣_∣ₕ (sym (merid north)))
--                                    ∙ Kn→ΩKn+10ₖ 3
--                                     ∙ flipSquare
--                                       (cong cool
--                                         (sym (merid (invLooper x) ∙ sym (merid base)))))

--   cool123 : (x : S¹) → Kn→ΩKn+1 3 ∣ north ∣
--                      ≡ cong (λ x → _⌣ₖ_ {n = 2} {m = 2} x x) (Kn→ΩKn+1 1 ∣ x ∣)
--   cool123 = λ x → (Kn→ΩKn+10ₖ 3
--                                   ∙ flipSquare (cong cool (merid x ∙ sym (merid base))))

--   thc : (a b : S¹) → Cube (λ i j → cool123 a j i)
--                            (λ i j → cool4 b j i)
--                            (λ j k → cool ((merid (a * invLooper b) ∙ sym (merid base)) j) k)
--                            (λ j k → 0ₖ 4)
--                            (λ i k → Kn→ΩKn+1 3 ∣ merid (S¹×S¹→S² a b) i ∣ₕ k)
--                            λ i k → _⌣ₖ_ {n = 2} {m = 2} (abstr (push a b i) k) (abstr (push a b i) k)
--   thc = {!∃[ n ∈ ℕ ] (f !}


-- -- genH²CP² : coHom 2 CP²
-- -- genH²CP² = ∣ (λ { (inl x) → ∣ x ∣ ; (inr x) → 0ₖ 2 ; (push a i) → abstr a i}) ∣₂
-- --   where
-- --     abstract
-- --       abstr : (a : TotalHopf) → Path (coHomK 2) ∣ fst a ∣ₕ (0ₖ 2)
-- --       abstr = transport (λ i → (a : ua (isoToEquiv IsoS³TotalHopf) i) → Path (coHomK 2)
-- --                        ∣ fst (ua-unglue (isoToEquiv IsoS³TotalHopf) i a) ∣ₕ (0ₖ 2))
-- --                        (sphereElim 2 (λ _ → isOfHLevelTrunc 4 _ _) refl)

-- -- gen₁-by₁-CP² : gen₁-by (coHomGr 2 CP²) genH²CP²
-- -- gen₁-by₁-CP² b = fun (fst H²CP²≅ℤ) b
-- --               , ((sym (leftInv (fst H²CP²≅ℤ) b)
-- --                 ∙ cong (inv (fst H²CP²≅ℤ)) (·Comm (pos 1) (fun (fst H²CP²≅ℤ) b)
-- --                 ∙ ℤ·≡· (fun (fst H²CP²≅ℤ) b) 1))
-- --               ∙ homPresℤ·
-- --                 (GroupEquiv→GroupHom (invGroupEquiv (GroupIso→GroupEquiv H²CP²≅ℤ))) (pos 1) (fun (fst H²CP²≅ℤ) b))
-- --               ∙ cong (fun (fst H²CP²≅ℤ) b ℤ[ coHomGr 2 CP² ]·_)
-- --                      (sym (cong (inv (fst H²CP²≅ℤ)) help)
-- --                     ∙ leftInv (fst H²CP²≅ℤ) genH²CP²)
-- --   where
-- --   help : fun (fst H²CP²≅ℤ) genH²CP² ≡ 1 -- computation:-)
-- --   help = refl


-- -- main : abs (Iso.fun (fst H⁴CP²≅ℤ) (genH²CP² ⌣ genH²CP²)) ≡ 1
-- -- main =
-- --   garam-masala
-- --     {!!}
-- --     {!!}
-- --     {!!}
-- --     {!!}
-- --     H⁴CP²≅ℤ
-- --     {!!}
-- --     genH²CP²
-- --     {!!}
-- --     {!!} -- {!garam-masala ? ? ? ? ? ? ? ? ?!}

-- -- data coLim {ℓ : Level} (A : (n : ℕ) → Type ℓ) (i : (n : ℕ) → A n → A (suc n))  : Type ℓ where
-- --   inn : (n : ℕ) → (A n) → coLim A i
-- --   push : (n : ℕ) (x : A n) → inn n x ≡ inn (suc n) (i n x)

-- -- open import Cubical.Data.List

-- -- TypeList : ∀ {ℓ} → ((n : ℕ) → Type ℓ) → (n : ℕ) → List (Type ℓ)
-- -- TypeList A zero = [ A zero ]
-- -- TypeList A (suc n) = A (suc n) ∷ TypeList A n

-- -- inferArgs : {!∀ {ℓ} → ((n : ℕ) → Type ℓ) → (n : ℕ) → List (Type ℓ)!}
-- -- inferArgs = {!!}

-- -- SemiSimp : ℕ → Type₁
-- -- i : (n : ℕ) → SemiSimp (suc n) → SemiSimp n
-- -- PartialList : (n : ℕ) → SemiSimp n → List Type
-- -- SemiSimp zero = Type
-- -- SemiSimp (suc n) = {!!}
-- -- PartialList zero A = [ A ]
-- -- PartialList (suc n) A = {!TypeList ? ?!} ∷ PartialList n A
-- -- i zero A = {!!}
-- -- i (suc n) A = {!!}
