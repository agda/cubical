{-
This file contains a proof of the fact that the Brunerie number,
i.e. absolute value of the Hopf invariant of [e , e] : π₃S², is 2.
Here, e is the generator of π₂S² and [_,_] denotes the Whitehead
product. The proof follows Proposition 5.4.4. in Brunerie (2016)
closely, but, for simplicity, considers only the case n = 2.
-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.HopfInvariant.Brunerie where

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso
open import Cubical.Homotopy.Whitehead

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.SphereProduct
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Unit
open import Cubical.Data.Sum renaming (rec to ⊎rec)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Join
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation
  renaming (elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (map to pMap ; rec to pRec)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open Iso
open IsGroupHom
open PlusBis

-- Some abstract versions of imported lemmas/definitions from
-- ZCohomology.Groups.SphereProduct for faster type checking.
opaque
  H²-genₗabs : coHom 2 (S₊ 2 × S₊ 2)
  H²-genₗabs = H²-S²×S²-genₗ

  H²-genᵣabs : coHom 2 (S₊ 2 × S₊ 2)
  H²-genᵣabs = H²-S²×S²-genᵣ

  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs : (n m : ℕ)
    → GroupIso (coHomGr ((suc n) +' (suc m))
                    (S₊ (suc n) × S₊ (suc m)))
                ℤGroup
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs = Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ

  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs≡ : (n m : ℕ)
    → Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs n m ≡ Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ n m
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs≡ n m = refl

  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣ :
      fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1))
          (H²-S²×S²-genₗ ⌣ H²-S²×S²-genᵣ)
    ≡ 1
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣ =
     fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1)) (H²-S²×S²-genₗ ⌣ H²-S²×S²-genᵣ)
    ≡⟨ cong (fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1))) (sym H²-S²≅H⁴-S²×S²⌣) ⟩
    fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1)) (fun (fst (H²-S²≅H⁴-S²×S²)) ∣ ∣_∣ₕ ∣₂)
    ≡⟨ speedUp ∣_∣ₕ ⟩
    fun (fst (Hⁿ-Sⁿ≅ℤ 1)) ∣ ∣_∣ₕ ∣₂
    ≡⟨ refl ⟩ -- Computation! :-)
    1 ∎
    where
    speedUp : (f : _) →
         fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1)) (fun (fst (H²-S²≅H⁴-S²×S²)) ∣ f ∣₂)
       ≡ fun (fst (Hⁿ-Sⁿ≅ℤ 1)) ∣ f ∣₂
    speedUp f i =
      fun (fst (Hⁿ-Sⁿ≅ℤ 1)) (leftInv (fst H²-S²≅H⁴-S²×S²) ∣ f ∣₂ i)

-- Some abbreviations
private
  inl' : S₊ 2 × S₊ 2 → Pushout⋁↪fold⋁ (S₊∙ 2)
  inl' = inl

  qHom : GroupHom (coHomGr 4 (Pushout⋁↪fold⋁ (S₊∙ 2)))
                  (coHomGr 4 (S₊ 2 × S₊ 2))
  qHom = coHomMorph 4 inl'

  qHomGen : (n : ℕ) →
         GroupHom (coHomGr n (Pushout⋁↪fold⋁ (S₊∙ 2)))
                  (coHomGr n (S₊ 2 × S₊ 2))
  qHomGen n = coHomMorph n inl'

-- The type C and generator α, β in dim 2 and 4 respectively
-- Recall, the goal is to prove that α ⌣ α = ±2 β
  CHopf : Type
  CHopf = HopfInvariantPush 0 fold∘W

  Hopfαfold∘W = Hopfα 0 (fold∘W , refl)
  Hopfβfold∘W = Hopfβ 0 (fold∘W , refl)

-- Rewriting CHopf as our favourite pushout
-- S²×S² ← S²∨S² → S²
  CHopfIso : Iso CHopf (Pushout⋁↪fold⋁ (S₊∙ 2))
  CHopfIso =
    compIso (invIso (equivToIso
      (compEquiv (compEquiv pushoutSwitchEquiv
        (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
            pushoutSwitchEquiv)))
            (equivToIso Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁)

-- Cohomology group version of the Iso
  coHomCHopfIso : (n : ℕ)
    → GroupIso (coHomGr n CHopf) (coHomGr n (Pushout⋁↪fold⋁ (S₊∙ 2)))
  coHomCHopfIso n = invGroupIso (coHomIso n CHopfIso)


-- We instantiate Mayer-Vietoris for the pushout
module MV-⋁↪-fold⋁ = MV _ _ (S₊∙ 2 ⋁ S₊∙ 2) ⋁↪ fold⋁

-- This give us an iso H⁴(S²×S² ← S²∨S² → S²) ≅ H⁴(S²×S²)
isEquiv-qHom : GroupEquiv (coHomGr 4 (Pushout⋁↪fold⋁ (S₊∙ 2)))
                (coHomGr 4 (S₊ 2 × S₊ 2))
fst (fst isEquiv-qHom) = qHom .fst
snd (fst isEquiv-qHom) =
  subst isEquiv
    (funExt (sElim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (×UnitEquiv (isoToPath
      (invIso
        (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p)))))
           _ isEquiv-i)
  where
  ×UnitEquiv : {A B C : Type}
         → Unit ≡ C
         → (f : A → B × C)
         → isEquiv f
         → isEquiv (fst ∘ f)
  ×UnitEquiv {A = A} {B = B} =
    J (λ C _ → (f : A → B × C) → isEquiv f → isEquiv (fst ∘ f))
      λ f eq → record { equiv-proof =
        λ b → ((fst (fst (equiv-proof eq (b , tt))))
          , cong fst (fst (equiv-proof eq (b , tt)) .snd))
          , λ y → ΣPathP ((cong fst (equiv-proof eq (b , tt)
                                      .snd ((fst y)
            , ΣPathP ((snd y) , refl))))
            , λ i j → equiv-proof eq (b , tt) .snd ((fst y)
            , ΣPathP ((snd y) , refl)) i .snd j .fst) }

  isEquiv-i : isEquiv (fst (MV-⋁↪-fold⋁.i 4))
  isEquiv-i =
    SES→isEquiv
      (isContr→≡UnitGroup
        (isOfHLevelRetractFromIso 0
          (compIso
            (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 2))
            (compIso
              (prodIso (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p)))
                       (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))))
              rUnit×Iso))
          isContrUnit))
      ((isContr→≡UnitGroup
        (isOfHLevelRetractFromIso 0
          (compIso
            (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 3))
            (compIso
              (prodIso (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p)))
                       (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))))
              rUnit×Iso))
          isContrUnit)))
      (MV-⋁↪-fold⋁.d 3)
      (MV-⋁↪-fold⋁.i 4)
      (MV-⋁↪-fold⋁.Δ 4)
      (MV-⋁↪-fold⋁.Ker-i⊂Im-d 3)
      (MV-⋁↪-fold⋁.Ker-Δ⊂Im-i 4)
snd isEquiv-qHom = qHom .snd


-- The goal now is reducing α ⌣ α = ±2 β to gₗ ⌣ gᵣ = e for
-- gₗ, gᵣ generators of H²(S²×S²) ≅ ℤ × ℤ and e generator of
-- H⁴(S²×S²) ≅ ℤ. This essentially just elementary linear algebra at
-- this point. We do it for an arbitrary (well-behaved) iso
-- H⁴(S²×S²) ≅ ℤ in order to speed up type checking.
module BrunerieNumLem
  (is : GroupIso (coHomGr 4 (S₊ 2 × S₊ 2)) ℤGroup)
  (isEq : (fun (fst is) (H²-S²×S²-genₗ ⌣ H²-S²×S²-genᵣ) ≡ 1)) where

  x = H²-S²×S²-genₗ
  y = H²-S²×S²-genᵣ

  α = Hopfαfold∘W
  β = Hopfβfold∘W

  α' : coHom 2 (Pushout⋁↪fold⋁ (S₊∙ 2))
  α' = fun (fst (coHomCHopfIso 2)) α

  β' : coHom 4 (Pushout⋁↪fold⋁ (S₊∙ 2))
  β' = fun (fst (coHomCHopfIso 4)) β

  rewriteEquation :
       (α' ⌣ α' ≡ β' +ₕ β') ⊎ (α' ⌣ α' ≡ -ₕ (β' +ₕ β'))
    → (α ⌣ α ≡ β +ₕ β) ⊎ (α ⌣ α ≡ -ₕ (β +ₕ β))
  rewriteEquation (inl x) =
    inl ((λ i → leftInv (fst (coHomCHopfIso 2)) α (~ i)
               ⌣ leftInv (fst (coHomCHopfIso 2)) α (~ i))
       ∙∙ cong (inv (fst (coHomCHopfIso 4))) x
       ∙∙ leftInv (fst (coHomCHopfIso 4)) (β +ₕ β))
  rewriteEquation (inr x) =
    inr ((λ i → leftInv (fst (coHomCHopfIso 2)) α (~ i)
               ⌣ leftInv (fst (coHomCHopfIso 2)) α (~ i))
      ∙∙ cong (inv (fst (coHomCHopfIso 4))) x
      ∙∙ leftInv (fst (coHomCHopfIso 4))
           (-ₕ (β +ₕ β)))

  rewriteEquation2 : (qHom .fst β' ≡  x ⌣ y) ⊎ (qHom .fst β' ≡  -ₕ (x ⌣ y))
  rewriteEquation2 =
    ⊎rec
      (λ p → inl (sym (leftInv (fst is) (qHom .fst β'))
                ∙∙ cong (inv (fst is)) (p ∙ sym isEq)
                ∙∙ leftInv (fst is) (x ⌣ y)))
      (λ p → inr (sym (leftInv (fst is) (qHom .fst β'))
               ∙∙ cong (inv (fst is))
                    (p ∙ sym (cong (GroupStr.inv (snd ℤGroup)) isEq))
               ∙∙ (presinv (invGroupIso is .snd) (fun (fst is) (x ⌣ y))
                 ∙ cong -ₕ_ (leftInv (fst is) (x ⌣ y)))))
      eqs
    where
    grIso : GroupEquiv (coHomGr 4 (HopfInvariantPush 0 fold∘W)) ℤGroup
    grIso = compGroupEquiv (GroupIso→GroupEquiv (coHomCHopfIso 4))
          (compGroupEquiv
            isEquiv-qHom
            (GroupIso→GroupEquiv is))

    eqs : (fst (fst grIso) β ≡ 1) ⊎ (fst (fst grIso) β ≡ -1)
    eqs = groupEquivPresGen _ (GroupIso→GroupEquiv (Hopfβ-Iso 0 (fold∘W , refl)))
          β (inl (Hopfβ↦1 0 (fold∘W , refl))) grIso

  qpres⌣ : (x y : coHom 2 _)
    → fst qHom (x ⌣ y) ≡ fst (qHomGen 2) x ⌣ fst (qHomGen 2) y
  qpres⌣ = sElim2 (λ _ _ → isSetPathImplicit) λ _ _ → refl

  α'↦x+y : fst (qHomGen 2) α' ≡ x +ₕ y
  α'↦x+y = lem ((coHomFun 2 (inv CHopfIso) α)) refl
    where
    lem : (x' : coHom 2 (Pushout⋁↪fold⋁ (S₊∙ 2)))
        → coHomFun 2 inr x' ≡ ∣ ∣_∣ ∣₂
        → fst (qHomGen 2) x' ≡ x +ₕ y
    lem = sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
      λ f p → Cubical.HITs.PropositionalTruncation.rec
        (squash₂ _ _)
        (λ r → cong ∣_∣₂ (funExt (uncurry
          (wedgeconFun 1 1 (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
            (λ x → cong f (push (inr x)) ∙∙ funExt⁻ r x ∙∙ refl)
            ((λ x → cong f (push (inl x)) ∙∙ funExt⁻ r x ∙∙ sym (rUnitₖ 2 ∣ x ∣ₕ)))
            (cong (_∙∙ funExt⁻ r north ∙∙ refl)
              (cong (cong f) λ j i → push (push tt j) i))))))
        (fun PathIdTrunc₀Iso p)


  mainEq : ((fst qHom) (α' ⌣ α') ≡ qHom .fst (β' +ₕ β'))
         ⊎ ((fst qHom) (α' ⌣ α') ≡ qHom .fst (-ₕ (β' +ₕ β')))
  mainEq =
    ⊎rec
      (λ id → inl (lem₁ ∙ lem₂
                  ∙ cong (λ x → x +ₕ x) (sym id)
                  ∙ sym (pres· (snd qHom) β' β')))
      (λ id → inr (lem₁ ∙ lem₂
                 ∙ ((sym (distLem (x ⌣ y))
                 ∙ cong -ₕ_ (cong (λ x → x +ₕ x) (sym id)))
                 ∙ cong (-ₕ_) (pres· (snd qHom) β' β'))
                 ∙ sym (presinv (snd qHom) (β' +ₕ β'))))
      rewriteEquation2
    where
    triv⌣ : (a : S¹)
      → cong₂ (_⌣ₖ_ {n = 2} {m = 2}) (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (merid a))
       ≡ λ _ → ∣ north ∣ₕ
    triv⌣ a =
      cong₂Funct (_⌣ₖ_ {n = 2} {m = 2})
        (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (merid a))
        ∙ sym (rUnit λ j → _⌣ₖ_ {n = 2} {m = 2} ∣ merid a j ∣ₕ ∣ north ∣)
        ∙ (λ i j → ⌣ₖ-0ₖ 2 2 ∣ merid a j ∣ₕ i)

    distLem : (x : coHom 4 (S₊ 2 × S₊ 2)) → -ₕ ((-ₕ x) +ₕ (-ₕ x)) ≡ x +ₕ x
    distLem =
      sElim (λ _ → isSetPathImplicit)
        λ f → cong ∣_∣₂ (funExt λ x → cong -ₖ_ (sym (-distrₖ 4 (f x) (f x)))
                       ∙ -ₖ^2  (f x +ₖ f x))

    x⌣x≡0 : x ⌣ x ≡ 0ₕ 4
    x⌣x≡0 =
      cong ∣_∣₂
       (funExt (uncurry λ { north y → refl
                          ; south y → refl
                          ; (merid a i) y j → triv⌣ a j i}))

    y⌣y≡0 : y ⌣ y ≡ 0ₕ 4
    y⌣y≡0 =
      cong ∣_∣₂
       (funExt (uncurry λ { x north → refl
                          ; x south → refl
                          ; x (merid a i) j → triv⌣ a j i}))

    -ₕ'Id : (x : coHom 4 (S₊ 2 × S₊ 2)) → (-ₕ'^ 2 · 2) x ≡ x
    -ₕ'Id =
      sElim (λ _ → isSetPathImplicit)
         λ f → cong ∣_∣₂ (funExt λ x → -ₖ'-gen-inl-left 2 2 tt (inl tt) (f x))

    y⌣x≡x⌣y : y ⌣ x ≡ x ⌣ y
    y⌣x≡x⌣y =
      y ⌣ x                                 ≡⟨ gradedComm'-⌣ 2 2 y x ⟩
      (-ₕ'^ 2 · 2) (transport refl (x ⌣ y))  ≡⟨ -ₕ'Id (transport refl (x ⌣ y)) ⟩
      transport refl (x ⌣ y)                ≡⟨ transportRefl (x ⌣ y) ⟩
      x ⌣ y ∎

    lem₂ : (x +ₕ y) ⌣ (x +ₕ y) ≡ (x ⌣ y) +ₕ (x ⌣ y)
    lem₂ =
     (x +ₕ y) ⌣ (x +ₕ y)                       ≡⟨ leftDistr-⌣ 2 2 (x +ₕ y) x y ⟩
     ((x +ₕ y) ⌣ x) +ₕ ((x +ₕ y) ⌣ y)          ≡⟨ cong₂ _+ₕ_ (rightDistr-⌣ 2 2 x y x) (rightDistr-⌣ 2 2 x y y) ⟩
     ((x ⌣ x +ₕ y ⌣ x)) +ₕ (x ⌣ y +ₕ y ⌣ y)    ≡⟨ cong₂ _+ₕ_ (cong (_+ₕ y ⌣ x) x⌣x≡0 ∙ lUnitₕ 4 (y ⌣ x))
                                                             (cong (x ⌣ y +ₕ_) y⌣y≡0 ∙ rUnitₕ 4 (x ⌣ y)) ⟩
     y ⌣ x +ₕ x ⌣ y                            ≡⟨ cong (_+ₕ (x ⌣ y)) y⌣x≡x⌣y ⟩
     ((x ⌣ y) +ₕ (x ⌣ y)) ∎

    lem₁ : (fst qHom) (α' ⌣ α') ≡ (x +ₕ y) ⌣ (x +ₕ y)
    lem₁ =
     fst qHom (α' ⌣ α')                        ≡⟨ refl ⟩
     fst (qHomGen 2) α' ⌣ fst (qHomGen 2) α'   ≡⟨ cong (λ x → x ⌣ x) α'↦x+y ⟩
     ((x +ₕ y) ⌣ (x +ₕ y)) ∎

  main⊎ : (HopfInvariant 0 (fold∘W , refl) ≡ 2)
        ⊎ (HopfInvariant 0 (fold∘W , refl) ≡ -2)
  main⊎ =
    ⊎rec (λ p → inl (lem₁
                   ∙ cong (fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) p
                   ∙ pres· (Hopfβ-Iso 0 (fold∘W , refl) .snd) β β
                   ∙ cong (λ x → x + x) (Hopfβ↦1 0 (fold∘W , refl))))
         (λ p → inr (lem₁
                   ∙ cong (fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) p
                   ∙ presinv (Hopfβ-Iso 0 (fold∘W , refl) .snd) (β +ₕ β)
                   ∙ cong (GroupStr.inv (snd ℤGroup))
                          (pres· (Hopfβ-Iso 0 (fold∘W , refl) .snd) β β
                         ∙ cong (λ x → x + x) (Hopfβ↦1 0 (fold∘W , refl)))))
         lem₂
    where
    lem₁ : HopfInvariant 0 (fold∘W , refl)
       ≡ fun (fst (Hopfβ-Iso 0 (fold∘W , refl))) (α ⌣ α)
    lem₁ =
      cong (fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) (transportRefl (α ⌣ α))

    lem₂ : (α ⌣ α ≡ β +ₕ β) ⊎ (α ⌣ α ≡ -ₕ (β +ₕ β))
    lem₂ =
      rewriteEquation
      (⊎rec (λ p → inl (sym (retEq (fst isEquiv-qHom) (α' ⌣ α'))
                              ∙∙ cong (invEq (fst isEquiv-qHom)) p
                              ∙∙ retEq (fst isEquiv-qHom) (β' +ₕ β')))
             (λ p → inr ((sym (retEq (fst isEquiv-qHom) (α' ⌣ α'))
                       ∙∙ cong (invEq (fst isEquiv-qHom)) p
                       ∙∙ retEq (fst isEquiv-qHom) (-ₕ (β' +ₕ β')))))
             mainEq)

  main : abs (HopfInvariant 0 (fold∘W , refl)) ≡ 2
  main = ⊎→abs _ 2 main⊎

-- We instantiate the module
Brunerie'≡2 : abs (HopfInvariant 0 (fold∘W , refl)) ≡ 2
Brunerie'≡2 = BrunerieNumLem.main (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1) Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣

-- We rewrite the it slightly, to get the definition of the Brunerie
-- number in Brunerie (2016)
Brunerie'≡Brunerie : [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π' ≡ ∣ fold∘W , refl ∣₂
Brunerie'≡Brunerie =
    sym fold∘W≡Whitehead
  ∙ cong ∣_∣₂ (∘∙-idˡ (fold∘W , refl))

-- And we get the main result
Brunerie≡2 : Brunerie ≡ 2
Brunerie≡2 =
  cong abs (cong (HopfInvariant-π' 0) Brunerie'≡Brunerie)
  ∙ Brunerie'≡2
