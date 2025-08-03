{-# OPTIONS --lossy-unification #-}
{-
This file computes πₙᵃᵇ(cofib α) and α : ⋁Sⁿ →∙ ⋁Sⁿ
-}
module Cubical.Homotopy.Group.PiAbCofibFinSphereBouquetMap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int renaming (_·_ to _·ℤ_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Pushout as PO
open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.HITs.AbPath

open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.IsomorphismTheorems

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PiSphereBouquet
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap

open Iso renaming (inv to inv')

-- Part 1: Computation of πᵃᵇ₁(cofib α) for α
-- α : ⋁S¹ →∙ ⋁S¹
-- Preliminary definitions:
module _ {m k : ℕ} (f : Fin m → FreeGroup (Fin k)) where
  gens→finSphereBouquetMap : SphereBouquet 1 (Fin m) → SphereBouquet 1 (Fin k)
  gens→finSphereBouquetMap = fun Iso-Bouquet→∙-SphereBouquet₁→∙
                               (inv' CharacFinBouquetFunIso f) .fst

  AbFreeGroup≅ℤ[] : (m : _)
    → AbGroupIso (AbelianizationAbGroup (freeGroupGroup (Fin m)))
                  (ℤ[Fin m ])
  AbFreeGroup≅ℤ[] m = compGroupIso GroupIso-AbelienizeFreeGroup→FreeAbGroup
                                   (invGroupIso (ℤFin≅FreeAbGroup m))

  AbFreeGroup→ℤ[] : (m : _) →
    AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin m)))
               (ℤ[Fin m ])
  AbFreeGroup→ℤ[] m = GroupIso→GroupHom (AbFreeGroup≅ℤ[] m)


  bouquetDegree-AbFreeGroup→ℤ[] : (x : _)
    → fst (bouquetDegree gens→finSphereBouquetMap) (AbFreeGroup→ℤ[] m .fst x)
     ≡ AbFreeGroup→ℤ[] k .fst (AbelianizationFun (FG.rec f) .fst x)
  bouquetDegree-AbFreeGroup→ℤ[] =
    Abi.elimProp _ (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
     (funExt⁻ (cong fst (help main)))
    where
    help = freeGroupHom≡
      {f = compGroupHom
             (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                           (AbFreeGroup→ℤ[] m))
            (bouquetDegree gens→finSphereBouquetMap)}
      {g = compGroupHom
             (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                           (AbelianizationFun (FG.rec f))) (AbFreeGroup→ℤ[] k)}

    main : (a : _) → bouquetDegree gens→finSphereBouquetMap .fst
                       (AbFreeGroup→ℤ[] m .fst (η (η a)))
                    ≡ AbFreeGroup→ℤ[] k .fst
                       (fst (AbelianizationFun (FG.rec f)) (η (η a)))
    main a = funExt λ s
      → sumFin-choose _ _ (λ _ → refl) +Comm _ _ a
          (characdiag s)
           λ x p → cong₂ _·ℤ_ (charac¬  x p) refl
      where
      charac¬ : (x' : Fin m) → ¬ x' ≡ a
        → fst (AbFreeGroup→ℤ[] m) (η (η a)) x' ≡ pos 0
      charac¬ x' p with (fst a ≟ᵗ fst x')
      ... | lt x = refl
      ... | eq x = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) (sym x)))
      ... | gt x = refl

      lem : ℤFinGenerator a a ≡ 1
      lem with (fst a ≟ᵗ fst a)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq x = refl
      ... | gt x = ⊥.rec (¬m<ᵗm x)

      aux : (x : FreeGroup (Fin k)) (y : S¹)
        → fst (SphereBouquet∙ 1 (Fin k))
      aux b base = inl tt
      aux b (loop i) =
        Bouquet→SphereBouquet (inv' Iso-ΩFinBouquet-FreeGroup b i)
      auxId : (x : _) → gens→finSphereBouquetMap (inr (a , x)) ≡ aux (f a) x
      auxId base = refl
      auxId (loop i) = refl

      characdiagMain : (w : _)
        → (λ s → degree (suc zero) (λ x → pickPetal s (aux w x)))
         ≡ fst (AbFreeGroup→ℤ[] k) (η w)
      characdiagMain =
        funExt⁻ (cong fst (freeGroupHom≡ {Group = AbGroup→Group ℤ[Fin k ]}
          {f = _ , makeIsGroupHom λ f g
            → funExt λ t → cong (degree 1)
              (funExt (λ { base → refl
                         ; (loop i) j → lem2 t f g j i}))
              ∙ (degreeHom {n = 0}
                ((λ x → pickPetal t (aux f x)) , refl)
                ((λ x → pickPetal t (aux g x)) , refl))}
          {g = _ , compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                                (AbFreeGroup→ℤ[] k) .snd}
          λ s → funExt λ w → final s w ∙ ℤFinGeneratorComm w s))
        where
        final : (s w : Fin k) → degree 1 (λ x → pickPetal w (aux (η s) x))
                           ≡ ℤFinGenerator w s
        final s w with (fst w ≟ᵗ fst s)
        ... | lt x = refl
        ... | eq x = refl
        ... | gt x = refl

        lem2 : (t : _) (f g : FreeGroup (Fin k))
          → cong (pickPetal t ∘ aux (f FG.· g)) loop
          ≡ (cong (pickPetal t ∘ aux f) loop ∙ refl)
           ∙ cong (pickPetal t ∘ aux g) loop ∙ refl
        lem2 t f g =
           cong (cong (pickPetal t ∘ Bouquet→SphereBouquet))
              (invIso-ΩFinBouquet-FreeGroupPresStr f g)
          ∙ cong-∙ (pickPetal t ∘ Bouquet→SphereBouquet)
              (inv' Iso-ΩFinBouquet-FreeGroup f)
              (inv' Iso-ΩFinBouquet-FreeGroup g)
          ∙ cong₂ _∙_ (rUnit _) (rUnit _)

      characdiag : (s : _) →
           ℤFinGenerator a a
        ·ℤ degree 1 (λ x → pickPetal s (gens→finSphereBouquetMap (inr (a , x))))
        ≡ fst (AbFreeGroup→ℤ[] k)
              (fst (AbelianizationFun (FG.rec f)) (η (η a))) s
      characdiag s = cong₂ _·ℤ_ lem refl
                   ∙ cong (degree (suc zero))
                          (funExt λ x → cong (pickPetal s) (auxId x))
                   ∙ funExt⁻ (characdiagMain (f a))  s

-- Part 2: Computation of πᵃᵇ₁(cofib α) for α : ⋁S¹ →∙ ⋁S¹
-- with α 'strictified' (induced by a set of generators in
-- FreeGroup (Fin k))
module _ {m k : ℕ} (α' : Fin m → FreeGroup (Fin k)) where
  private
    α :  Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k)
    α = inv' CharacFinBouquetFunIso α'

    αSphereBouquet : SphereBouquet∙ (suc zero) (Fin m)
                  →∙ SphereBouquet∙ (suc zero) (Fin k)
    αSphereBouquet = fun Iso-Bouquet→∙-SphereBouquet₁→∙ α

    _·f_ : ∀ {ℓ} {A : Type ℓ} → FreeGroup A → FreeGroup A → FreeGroup A
    _·f_ = FG._·_

  Bouquet→CofibFinBouquetMap : Bouquet (Fin k) → cofib (fst α)
  Bouquet→CofibFinBouquetMap = inr

  Freeᵃᵇ/ImFinBouquetMap : AbGroup ℓ-zero
  Freeᵃᵇ/ImFinBouquetMap =
    AbelianizationAbGroup (freeGroupGroup (Fin k))
      /Im AbelianizationFun (FG.rec α')

  FinBouquetCode : Bouquet (Fin k) → Type
  FinBouquetCode base = Freeᵃᵇ/ImFinBouquetMap .fst
  FinBouquetCode (loop x i) =
    ua (isoToEquiv (·GroupAutomorphismR (AbGroup→Group (Freeᵃᵇ/ImFinBouquetMap))
                                        [ η (η x) ])) i

  substFinBouquetCode : (p : _) (x : _)
    → subst FinBouquetCode (inv' Iso-ΩFinBouquet-FreeGroup p) [ η x ]
     ≡ [ η (x FG.· p)  ]
  substFinBouquetCode = FG.elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
    (λ a x i → [ η (transportRefl x i FG.· η (transportRefl a i)) ])
    (λ g1 g2 p q x
      → cong (λ P → subst FinBouquetCode P [ η x ])
             (invIso-ΩFinBouquet-FreeGroupPresStr g1 g2)
      ∙ substComposite FinBouquetCode
         (inv' Iso-ΩFinBouquet-FreeGroup g1)
         (inv' Iso-ΩFinBouquet-FreeGroup g2) [ η x ]
      ∙ cong (subst FinBouquetCode (inv' Iso-ΩFinBouquet-FreeGroup g2))
             (p x)
      ∙ q (x FG.· g1)
      ∙ λ i → [ η (FG.assoc x g1 g2 (~ i)) ])
    (λ x i → [ η ((transportRefl x ∙ FG.idr x) i) ])
    λ g p x
      → cong (λ P → subst FinBouquetCode P [ η x ])
          (invIso-ΩFinBouquet-FreeGroupPresInv g)
       ∙ cong (subst FinBouquetCode (sym (inv' Iso-ΩFinBouquet-FreeGroup g)))
           (λ i → [ η ((FG.idr x
                     ∙ cong₂ FG._·_ refl (sym (FG.invl g))
                     ∙ (FG.assoc x (inv g) g)) i) ])
       ∙ sym (cong (subst FinBouquetCode (sym (inv' Iso-ΩFinBouquet-FreeGroup g)))
               (p (x FG.· inv g)))
       ∙ subst⁻Subst FinBouquetCode (inv' Iso-ΩFinBouquet-FreeGroup g )
         [ η (x FG.· inv g) ]

  CofibFinBoquetFunCode : cofib (fst α) → Type
  CofibFinBoquetFunCode (inl x) = Freeᵃᵇ/ImFinBouquetMap .fst
  CofibFinBoquetFunCode (inr x) = FinBouquetCode x
  CofibFinBoquetFunCode (push base i) = Freeᵃᵇ/ImFinBouquetMap .fst
  CofibFinBoquetFunCode (push (loop x j) i) = lem i j
    where
    open AbelianizationGroupStructure (freeGroupGroup (Fin k))
    lem : refl ≡ cong (FinBouquetCode) (inv' Iso-ΩFinBouquet-FreeGroup (α' x))
    lem = sym uaIdEquiv
        ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _)
          (funExt (SQ.elimProp (λ _ → squash/ _ _)
            (Abi.elimProp _ (λ _ → squash/ _ _)
              λ g → sym (substFinBouquetCode (α' x) g
                  ∙ eq/ _ _ ∣ (η (η x))
                           , (sym (ridAb (η (α' x)))
                           ∙ commAb (η (α' x)) 1Ab)
                           ∙ cong₂ _·Ab_ (sym (rinvAb (η g))) refl
                           ∙ sym (assocAb (η g) (η (inv g)) (η (α' x)))
                           ∙ cong₂ _·Ab_ refl (commAb (η (inv g)) (η (α' x)))
                           ∙ assocAb (η g) (η (α' x)) (η (inv g)) ∣₁)))))
        ∙ retEq univalence _

  isSetCofibFinBoquetFunCode : (x : _) → isSet (CofibFinBoquetFunCode x)
  isSetCofibFinBoquetFunCode =
    PO.elimProp _ (λ _ → isPropIsSet)
      (λ _ → AbGroupStr.is-set (Freeᵃᵇ/ImFinBouquetMap .snd))
      (elimPropBouquet
        (λ _ → isPropIsSet)
        (AbGroupStr.is-set (Freeᵃᵇ/ImFinBouquetMap .snd)))

  FG→π₁cofibFinBouquetMap :
    GroupHom (freeGroupGroup (Fin k))
             (πGr 0 (cofib (fst α) , inr base))
  fst FG→π₁cofibFinBouquetMap b =
    ∣ (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup b i)) ∣₂
  snd FG→π₁cofibFinBouquetMap = makeIsGroupHom λ a b
    → cong ∣_∣₂ ((λ i j → inr (invIso-ΩFinBouquet-FreeGroupPresStr a b i j))
     ∙ cong-∙ inr (inv' Iso-ΩFinBouquet-FreeGroup a)
                  (inv' Iso-ΩFinBouquet-FreeGroup b))

  private
    loopCofibFinBouquetMap : (x : Fin m)
      → Path (Path (cofib (fst α)) (inr base) (inr base))
             (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup (α' x) i))
             refl
    loopCofibFinBouquetMap x i j =
      hcomp (λ k → λ {(i = i0) → push (loop x j) k
                     ; (i = i1) → push base k
                     ; (j = i0) → push base k
                     ; (j = i1) → push base k})
            (inl tt)

  AbFG→π₁ᵃᵇCofibFinBouquetMap : Abelianization (freeGroupGroup (Fin k))
                → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂
  AbFG→π₁ᵃᵇCofibFinBouquetMap = fst Abelianizeπ₁→π₁ᵃᵇ
    ∘ AbelianizationFun FG→π₁cofibFinBouquetMap .fst

  Hom-AbFG-π₁ᵃᵇCofibFinBouquetMap :
    AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin k)))
               (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  Hom-AbFG-π₁ᵃᵇCofibFinBouquetMap =
    compGroupHom (AbelianizationFun FG→π₁cofibFinBouquetMap) Abelianizeπ₁→π₁ᵃᵇ

  AbFG→π₁ᵃᵇCofibFinBouquetMap≡' : (x : Abelianization (freeGroupGroup (Fin m)))
    → (a : FreeGroup (Fin k))
    → ·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap ((AbelianizationFun (FG.rec α')) .fst x))
           (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a))
     ≡ AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)
  AbFG→π₁ᵃᵇCofibFinBouquetMap≡' =
    Abi.elimProp _ (λ _ → isPropΠ λ _ → squash₂ _ _)
     (FG.elimProp (λ _ → isPropΠ λ _ → squash₂ _ _)
     (λ c a → (λ i → ·πᵃᵇ ∣ paths (loopCofibFinBouquetMap c i) ∣₂
                           (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))
                  ∙ cong ∣_∣₂ (cong paths (sym (lUnit _))))
     (λ g1 g2 p q a
       → cong₂ ·πᵃᵇ (cong AbFG→π₁ᵃᵇCofibFinBouquetMap
                     (IsGroupHom.pres·
                       (snd (AbelianizationFun (FG.rec α'))) (η g1) (η g2))
        ∙ IsGroupHom.pres·
           (snd (compGroupHom (AbelianizationFun FG→π₁cofibFinBouquetMap)
             (Abelianizeπ₁→π₁ᵃᵇ)))
           (fst (AbelianizationFun (FG.rec α')) (η g1))
           (fst (AbelianizationFun (FG.rec α')) (η g2)))
           (λ _ → (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))
         ∙ sym (·πᵃᵇassoc (AbFG→π₁ᵃᵇCofibFinBouquetMap
                           (AbelianizationFun (FG.rec α') .fst (η g1)))
                         (AbFG→π₁ᵃᵇCofibFinBouquetMap
                           (AbelianizationFun (FG.rec α') .fst (η g2)))
                           (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))
         ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap
                       (AbelianizationFun (FG.rec α') .fst (η g1)))) (q a)
         ∙ p a)
       (λ a → ·πᵃᵇlUnit (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))
       λ g p a → cong₂ ·πᵃᵇ
          (sym (sym (IsGroupHom.presinv (snd (compGroupHom
                     (AbelianizationFun FG→π₁cofibFinBouquetMap)
                     (Abelianizeπ₁→π₁ᵃᵇ)))
                     (AbelianizationFun (FG.rec α') .fst (η g)))
            ∙ cong AbFG→π₁ᵃᵇCofibFinBouquetMap
                    (IsGroupHom.presinv
                      (snd (AbelianizationFun (FG.rec α'))) (η g))))
          (sym (sym (IsGroupHom.presinv (snd (compGroupHom
                     (AbelianizationFun FG→π₁cofibFinBouquetMap)
                  (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
        ∙ cong (AbFG→π₁ᵃᵇCofibFinBouquetMap ∘ η)
               (GroupTheory.invInv (freeGroupGroup (Fin k)) a)))
        ∙ sym (-πᵃᵇinvDistr (AbFG→π₁ᵃᵇCofibFinBouquetMap
                            ((AbelianizationFun (FG.rec α')) .fst (η g)))
                           (AbFG→π₁ᵃᵇCofibFinBouquetMap (η (inv a))))
        ∙ cong -πᵃᵇ (p (inv a))
        ∙ sym (IsGroupHom.presinv (snd (compGroupHom
                (AbelianizationFun FG→π₁cofibFinBouquetMap)
                  (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
        ∙ cong (AbFG→π₁ᵃᵇCofibFinBouquetMap ∘ η)
               (GroupTheory.invInv (freeGroupGroup (Fin k)) a))

  AbFG→π₁ᵃᵇCofibFinBouquetMap≡ : (x : Abelianization (freeGroupGroup (Fin m)))
    (a b : FreeGroup (Fin k))
      (q : ·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap (AbelianizationFun (FG.rec α') .fst x))
               (AbFG→π₁ᵃᵇCofibFinBouquetMap (η b))
              ≡ AbFG→π₁ᵃᵇCofibFinBouquetMap (η a))
     → Path (∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂)
             (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a))
             (AbFG→π₁ᵃᵇCofibFinBouquetMap (η b))
  AbFG→π₁ᵃᵇCofibFinBouquetMap≡ x a b q =
    sym q ∙ AbFG→π₁ᵃᵇCofibFinBouquetMap≡' x b

  decodeCofibαinl : Abelianization (freeGroupGroup (Fin k))
    → ∥ inr base ≡ᵃᵇ inl tt ∥₂
  decodeCofibαinl =
    Abi.rec _ squash₂
      (λ s → ·πᵃᵇ (∣ paths (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup s i)) ∣₂)
                   ∣ paths (sym (push base)) ∣₂)
   λ a b c → cong₂ ·πᵃᵇ (cong ∣_∣₂ (lem a b c)
                    ∙ cong (·πᵃᵇ (∣ paths (t a) ∣₂))
                           (·πᵃᵇcomm ∣ paths (t b) ∣₂ ∣ paths (t c) ∣₂)
                    ∙ sym (cong ∣_∣₂ (lem a c b)))
                        (λ _ → ∣ paths (sym (push base)) ∣₂)
    where
    t : (x : _) → Path (cofib (fst α)) _ _
    t x i = inr (inv' Iso-ΩFinBouquet-FreeGroup x i)

    lem : (x y z : _)
      → Path (Pathᵃᵇ (cofib (fst α)) _ _)
              (paths (t (x ·f (y ·f z))))
              (paths (t x ∙ t y ∙ t z))
    lem x y z =
      cong paths (((λ j i → inr (invIso-ΩFinBouquet-FreeGroupPresStr x (y ·f z) j i))
         ∙ cong-∙ inr (inv' Iso-ΩFinBouquet-FreeGroup x)
                      (inv' Iso-ΩFinBouquet-FreeGroup (y ·f z)))
        ∙ cong₂ _∙_ refl
           ((λ j i → inr (invIso-ΩFinBouquet-FreeGroupPresStr y z j i))
          ∙ cong-∙ inr (inv' Iso-ΩFinBouquet-FreeGroup y)
                       (inv' Iso-ΩFinBouquet-FreeGroup z)))

  Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap :
    AbGroupHom Freeᵃᵇ/ImFinBouquetMap
               (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  fst Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap =
    SQ.rec squash₂ AbFG→π₁ᵃᵇCofibFinBouquetMap main
    where
    main : (a b :  fst (AbelianizationAbGroup (freeGroupGroup (Fin k))))
           (q : ∃[ x ∈ fst (AbelianizationAbGroup (freeGroupGroup (Fin m))) ]
                _ ≡ _)
           → AbFG→π₁ᵃᵇCofibFinBouquetMap a ≡ AbFG→π₁ᵃᵇCofibFinBouquetMap b
    main = Abi.elimProp2 _ (λ _ _ → isPropΠ (λ _ → squash₂ _ _))
      λ a b → PT.elim (λ _ → squash₂ _ _)
        λ {(x , q)
          → AbFG→π₁ᵃᵇCofibFinBouquetMap≡ x a b
             (cong (λ s → ·πᵃᵇ s (AbFG→π₁ᵃᵇCofibFinBouquetMap (η b)))
                (cong AbFG→π₁ᵃᵇCofibFinBouquetMap q
                ∙ IsGroupHom.pres· (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetMap)
                                   (η a) (η (inv b)))
                ∙ (sym (·πᵃᵇassoc (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a))
                                  (AbFG→π₁ᵃᵇCofibFinBouquetMap (η (inv b)))
                                  (AbFG→π₁ᵃᵇCofibFinBouquetMap (η b))))
                ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))
                   (cong₂ ·πᵃᵇ (IsGroupHom.presinv
                                (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetMap) (η b)) refl
                   ∙ ·πᵃᵇlCancel ((AbFG→π₁ᵃᵇCofibFinBouquetMap (η b))))
                ∙ ·πᵃᵇrUnit (AbFG→π₁ᵃᵇCofibFinBouquetMap (η a)))}
  snd Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap =
     makeIsGroupHom (SQ.elimProp2
      (λ _ _ → squash₂ _ _)
      (IsGroupHom.pres· (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetMap)))

  decodeFinBouquetCode : (x : _) → FinBouquetCode x
    → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr x) ∥₂
  decodeFinBouquetCode base = fst Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap
  decodeFinBouquetCode (loop x i) = help i
    where
    lem : (p : _)
     → transport (λ i → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
                  (·πᵃᵇ p (-πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap (η (η x))))) ≡ p
    lem = ST.elim (λ _ → isSetPathImplicit)
      (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p
        → (λ j → transp (λ i → ∥ Pathᵃᵇ (cofib (fst α))
                                    (inr base) (inr (loop x (i ∨ j))) ∥₂) j
                        ∣ paths (p ∙ (λ i → inr (loop x (~ i ∨ j)))) ∣₂)
       ∙ cong ∣_∣₂ (cong paths (sym (rUnit p))))

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR
                                          (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                                                             [ η (η x) ])) i
                      → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
            (fst Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap)
            (fst Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap)
    help = toPathP (funExt (SQ.elimProp (λ _ → squash₂ _ _)
      λ s → cong (transport (λ i → ∥ Pathᵃᵇ (cofib (fst α))
                                             (inr base) (inr (loop x i)) ∥₂))
         ((cong (fst Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap)
           (cong (inv' (·GroupAutomorphismR
                         (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                                                [ η (η x) ]))
             (transportRefl [ s ]))
          ∙ IsGroupHom.pres· (snd Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap)
            [ s ] [ η (inv (η x)) ]
          ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetMap s))
               (IsGroupHom.presinv
                (snd Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap)
                  [ η (η x) ])))
       ∙ lem (AbFG→π₁ᵃᵇCofibFinBouquetMap s)))

  decodeCofibFinBoquetFun : (x : _) → CofibFinBoquetFunCode x
    → ∥ inr base ≡ᵃᵇ x ∥₂
  decodeCofibFinBoquetFun (inl x) p =
    ·πᵃᵇ (decodeFinBouquetCode base p) ∣ paths (sym (push base)) ∣₂
  decodeCofibFinBoquetFun (inr x) = decodeFinBouquetCode x
  decodeCofibFinBoquetFun (push a i) = help a i
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → CofibFinBoquetFunCode (push a i)
                   → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (push a i) ∥₂)
               (λ p → ·πᵃᵇ (decodeFinBouquetCode base p)
                           ∣ paths (sym (push base)) ∣₂)
               (decodeFinBouquetCode (inv' CharacFinBouquetFunIso α' .fst a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → squash₂)) _ _)
        (funExt (SQ.elimProp (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
          (Abi.elimProp _ (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
            λ g → λ i → ∣ paths (compPath-filler
              (λ i₂ → inr (inv' Iso-ΩFinBouquet-FreeGroup g i₂))
              (sym (push base)) (~ i)) ∣₂)))

  FinBouquetCode+ : (x : _) → Freeᵃᵇ/ImFinBouquetMap .fst
    → FinBouquetCode x → FinBouquetCode x
  FinBouquetCode+ base p q = AbGroupStr._+_ (snd Freeᵃᵇ/ImFinBouquetMap) p q
  FinBouquetCode+ (loop x i) p = commPathP i
    where
    typecheck : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B)
      (f : A → A) (g : B → B)
      → ((x : _) → transport p (f (transport (sym p) x)) ≡ g x)
      → PathP (λ i → p i → p i) f g
    typecheck = λ A → J> λ f g p
      → funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl x)) ∙ p x

    typecheck' : ∀ {ℓ} {A B : Type ℓ} (p : A ≃ B)
      {f : A → A} {g : B → B} → ((x : _) → fst p (f (invEq p x)) ≡ g x)
        → PathP (λ i → ua p i → ua p i) f g
    typecheck' p {f = f} {g} h =
      typecheck _ _ (ua p) f g λ b
        → transportRefl _
         ∙ cong (fst p) (cong f (cong (invEq p) (transportRefl b))) ∙ h b


    commPathP : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR
                                        (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                                        [ η (η x) ])) i
                      → ua (isoToEquiv (·GroupAutomorphismR
                                        (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                                        [ η (η x) ])) i)
                 (AbGroupStr._+_ (snd Freeᵃᵇ/ImFinBouquetMap) p)
                 (AbGroupStr._+_ (snd Freeᵃᵇ/ImFinBouquetMap) p)
    commPathP =
     typecheck' (isoToEquiv (·GroupAutomorphismR
                               (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                               [ η (η x) ]))
      (SQ.elimProp (λ _ → squash/ _ _)
        (Abi.elimProp _ (λ _ → squash/ _ _) λ g
          → sym (AbGroupStr.+Assoc (snd Freeᵃᵇ/ImFinBouquetMap) p
                  (invEq (isoToEquiv (·GroupAutomorphismR (AbGroup→Group Freeᵃᵇ/ImFinBouquetMap)
                                       [ η (η x) ])) [ η g ])
                  [ η (η x) ])
              ∙ cong (snd Freeᵃᵇ/ImFinBouquetMap AbGroupStr.+ p)
                 (sym (AbGroupStr.+Assoc (snd Freeᵃᵇ/ImFinBouquetMap)
                      [ η g ] [ η (inv (η x)) ]  [ η (η x) ])
                ∙ cong (snd Freeᵃᵇ/ImFinBouquetMap AbGroupStr.+ [ η g ])
                  (AbGroupStr.+InvL (snd Freeᵃᵇ/ImFinBouquetMap) [ η (η x) ])
                ∙ AbGroupStr.+IdR (snd Freeᵃᵇ/ImFinBouquetMap) [ η g ])))

  CofibFinBoquetFunCode+ : (x : _) → Freeᵃᵇ/ImFinBouquetMap .fst
    → CofibFinBoquetFunCode x → CofibFinBoquetFunCode x
  CofibFinBoquetFunCode+ (inl x) p q =
    AbGroupStr._+_ (snd Freeᵃᵇ/ImFinBouquetMap) p q
  CofibFinBoquetFunCode+ (inr x) = FinBouquetCode+ x
  CofibFinBoquetFunCode+ (push x i) p = help x i
   where
   help : (x : Bouquet (Fin m))
     → PathP (λ i → CofibFinBoquetFunCode (push x i)
                   → CofibFinBoquetFunCode (push x i))
             (snd Freeᵃᵇ/ImFinBouquetMap AbGroupStr.+ p)
             (FinBouquetCode+ (α .fst x) p)
   help = elimPropBouquet (λ _ → isOfHLevelPathP' 1
                           (isSetΠ (λ _ → isSetCofibFinBoquetFunCode _)) _ _)
                          refl

  encodeCofibFinBoquetFun' : (x : _)
    → Pathᵃᵇ (cofib (fst α)) (inr base) x → CofibFinBoquetFunCode x
  encodeCofibFinBoquetFun' x (paths q) = subst CofibFinBoquetFunCode q [ η ε ]
  encodeCofibFinBoquetFun' x (com p q r i) =
    encodeCofibFinBoquetFun'-comm _ q p r i
    where
    Code' : (x : _) (p : Path (cofib (fst α)) (inr base) (inr x)) → hProp ℓ-zero
    fst (Code' base p) =
      ∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ λ i → inr (r i)
    snd (Code' base p) = squash₁
    fst (Code' (loop x i) p) =
      ∃[ r ∈ Path (Bouquet (Fin k)) base (loop x i) ] p ≡ λ i → inr (r i)
    snd (Code' (loop x i) p) = squash₁

    Code : (x : cofib (fst α)) (p : inr base ≡ x) → Type
    Code (inl x) p = ∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                      (p ≡ (λ i → inr (r i)) ∙ sym (push base))
    Code (inr x) p = fst (Code' x p)
    Code (push a i) p = help a i p .fst
      where
      help : (a : Bouquet (Fin m))
        → PathP (λ i → Path (cofib (fst α))  (inr base) (push a i) →
                       hProp ℓ-zero)
                 (λ a → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                   a ≡ (λ i → inr (r i)) ∙ sym (push base)) , squash₁)
                 (Code' (fst α a))
      help =
        elimPropBouquet (λ _ → isOfHLevelPathP' 1
                                 (isSetΠ (λ _ → isSetHProp)) _ _)
          λ i p → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                    p ≡ compPath-filler (λ i → inr (r i)) (sym (push base)) (~ i))
                  , squash₁

    aux : (x : cofib (fst α)) (p : inr base ≡ x) → Code x p
    aux = J> ∣ refl , refl ∣₁

    encodeCofibFinBoquetFun'-comm : (x : _) (q p r : inr base ≡ x)
      → subst CofibFinBoquetFunCode (p ∙ sym q ∙ r) [ η ε ]
       ≡ subst CofibFinBoquetFunCode (r ∙ sym q ∙ p) [ η ε ]
    encodeCofibFinBoquetFun'-comm = J> λ p q
      → cong (λ p → subst CofibFinBoquetFunCode p [ η ε ])
              (cong (p ∙_) (sym (lUnit q)))
      ∙ substComposite CofibFinBoquetFunCode p q [ η ε ]
      ∙ PT.rec2 (squash/ _ _)
          (λ {(x' , xe) (y' , ye)
            → lem (fun Iso-ΩFinBouquet-FreeGroup x')
                  (fun Iso-ΩFinBouquet-FreeGroup y')
                  p
                  (cong (cong Bouquet→CofibFinBouquetMap)
                    (leftInv Iso-ΩFinBouquet-FreeGroup x') ∙ sym xe)
                  q
                  (cong (cong Bouquet→CofibFinBouquetMap)
                    (leftInv Iso-ΩFinBouquet-FreeGroup y') ∙ sym ye)})
          (aux _ p)
          (aux _ q)
      ∙ sym (substComposite CofibFinBoquetFunCode q p [ η ε ])
      ∙ cong (λ p → subst CofibFinBoquetFunCode p [ η ε ])
             (cong (q ∙_) (lUnit p))
      where
      lem : (x y : FreeGroup (Fin k))
            (p : Path (cofib (fst α)) (inr base) (inr base))
            (s : (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup x i)) ≡ p)
            (q : Path (cofib (fst α)) (inr base) (inr base))
            (s' : (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup y i)) ≡ q)
         → subst CofibFinBoquetFunCode q (subst CofibFinBoquetFunCode p [ η ε ])
          ≡ subst CofibFinBoquetFunCode p (subst CofibFinBoquetFunCode q [ η ε ])
      lem x y =
        J> (J> cong (subst CofibFinBoquetFunCode y')
              (substFinBouquetCode x ε
             ∙ AbGroupStr.+IdL (snd Freeᵃᵇ/ImFinBouquetMap) [ η x ])
         ∙ substFinBouquetCode y x
         ∙ cong [_] (AbelianizationGroupStructure.commAb
                     (freeGroupGroup (Fin k)) (η x) (η y))
         ∙ sym (substFinBouquetCode x y)
         ∙ cong (subst CofibFinBoquetFunCode x')
             (sym (substFinBouquetCode y ε
                ∙ AbGroupStr.+IdL (snd Freeᵃᵇ/ImFinBouquetMap) [ η y ])) )
        where
        x' y' : Path (cofib (fst α)) (inr base) (inr base)
        x' =  (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup x i))
        y' =  (λ i → inr (inv' Iso-ΩFinBouquet-FreeGroup y i))

  encodeCofibFinBoquetFun : (x : _)
    → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂ → CofibFinBoquetFunCode x
  encodeCofibFinBoquetFun x =
    ST.rec (isSetCofibFinBoquetFunCode _) (encodeCofibFinBoquetFun' x)

  decodeEncodeCofibFinBouquetMap : (x : _)
    (p : ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂)
    → decodeCofibFinBoquetFun x (encodeCofibFinBoquetFun x p) ≡ p
  decodeEncodeCofibFinBouquetMap x =
    ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
      (J (λ x p → decodeCofibFinBoquetFun x
                    (encodeCofibFinBoquetFun x ∣ paths p ∣₂) ≡ ∣ paths p ∣₂)
         refl))

  encodeDecodeCofibFinBouquetMap : (p : _)
    → encodeCofibFinBoquetFun (inr base) (decodeCofibFinBoquetFun (inr base) p)
     ≡ p
  encodeDecodeCofibFinBouquetMap = SQ.elimProp (λ _ → squash/ _ _)
    (Abi.elimProp _ (λ _ → squash/ _ _)
      λ w → substFinBouquetCode w ε ∙ λ i → [ η (FG.idl w (~ i)) ])

  --- Main results ---
  Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap :
    AbGroupIso Freeᵃᵇ/ImFinBouquetMap
              (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  fun (fst Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap) =
    Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap .fst
  inv' (fst Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap) =
    encodeCofibFinBoquetFun (inr base)
  rightInv (fst Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap) =
    decodeEncodeCofibFinBouquetMap (inr base)
  leftInv (fst Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap) =
    encodeDecodeCofibFinBouquetMap
  snd Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap =
    Hom-Freeᵃᵇ/ImFinBouquetMap-π₁ᵃᵇCofibFinBouquetMap .snd

  Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap' :
    AbGroupIso Freeᵃᵇ/ImFinBouquetMap
               (AbelianizationAbGroup (πGr 0 (cofib (fst α) , inr base)))
  Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap' =
    compGroupIso Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap
      (invGroupIso (Abelianizeπ₁≅π₁ᵃᵇ (_ , inr base)))

  Iso-CofibFinBouquetMap-CofibFinSphereBouquetMap :
    Iso (cofib (fst α)) (cofib (fst αSphereBouquet))
  Iso-CofibFinBouquetMap-CofibFinSphereBouquetMap =
    pushoutIso _ _ _ _
     (invEquiv (Bouquet≃∙SphereBouquet .fst)) (idEquiv _)
     (invEquiv (Bouquet≃∙SphereBouquet .fst))
     (λ i x → tt)
     (funExt λ x → cong (invEq (isoToEquiv Iso-SphereBouquet-Bouquet))
       (cong (fst α) (sym (rightInv Iso-SphereBouquet-Bouquet x))))

  -- π₁ᵃᵇ(cofib α) ≅ Freeᵃᵇ/Im(deg(α))
  Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap :
    AbGroupIso Freeᵃᵇ/ImFinBouquetMap
               (AbelianizationAbGroup
                 (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
  Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap =
    compGroupIso Freeᵃᵇ/ImFinBouquetMap≅π₁ᵃᵇCofibFinBouquetMap'
      (GroupEquiv→GroupIso (AbelianizationEquiv
        (compGroupEquiv
          (GroupIso→GroupEquiv
            (invGroupIso (π'Gr≅πGr 0 (cofib (fst α) , inr base))))
          (GroupIso→GroupEquiv
            (π'GrIso 0 (isoToEquiv
              (Iso-CofibFinBouquetMap-CofibFinSphereBouquetMap)
              , sym (push (inl tt))))))))

  -- Freeᵃᵇ/Im(deg(α)) ≅ ℤ[]/Im(deg(α))
  Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree :
    AbGroupIso Freeᵃᵇ/ImFinBouquetMap
               (ℤ[Fin k ] /Im bouquetDegree (fst αSphereBouquet))
  Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree =
    Hom/ImIso _ _ (AbFreeGroup≅ℤ[] α' m) (AbFreeGroup≅ℤ[] α' k)
                  (bouquetDegree-AbFreeGroup→ℤ[] α')

  -- Locked versions for faster type checking
  Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock : lockUnit {ℓ-zero}
    → AbGroupIso (AbelianizationAbGroup
                   (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
                  Freeᵃᵇ/ImFinBouquetMap
  Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock unlock =
    invGroupIso Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap

  Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock : lockUnit {ℓ-zero}
    → AbGroupIso Freeᵃᵇ/ImFinBouquetMap
                 (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock unlock =
    Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree

  π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock : lockUnit {ℓ-zero}
    → AbGroupIso (AbelianizationAbGroup (π'Gr 0 (cofib∙ (fst αSphereBouquet))))
                  (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock t =
    compGroupIso (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock t)
                 (Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock t)

  π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1 :
    AbGroupIso (AbelianizationAbGroup
              (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
             (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1 =
    π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock unlock

-- Part 3: Same thing for arbitrary α : ⋁Sⁿ →∙ ⋁Sⁿ
-- (arbtirary n and α)
module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where

  preπ'FinSphereBouquetMapGenerator : (k : Fin k) → S₊∙ (suc n) →∙ cofib∙ (fst α)
  preπ'FinSphereBouquetMapGenerator k =
    (λ x → inr (inr (k , x))) ,
    (λ i → inr (push k (~ i))) ∙ (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))

  π'FinSphereBouquetMapGenerator : (k : Fin k) → π'Gr n (cofib∙ (fst α)) .fst
  π'FinSphereBouquetMapGenerator k =
     ∣ preπ'FinSphereBouquetMapGenerator k ∣₂

  πᵃᵇFinSphereBouquetMapGenerator : (k : Fin k)
    → Abelianization (π'Gr n (cofib∙ (fst α)))
  πᵃᵇFinSphereBouquetMapGenerator k = η (π'FinSphereBouquetMapGenerator k)

private
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain : {n m k : ℕ}
    (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
    → Σ[ ϕ ∈ AbGroupIso
               (AbelianizationAbGroup (π'Gr n (cofib∙ (fst α))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst α))) ]
         ((w : Fin k) → fun (fst ϕ) (πᵃᵇFinSphereBouquetMapGenerator α w)
                      ≡ [ ℤFinGenerator w ])
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain {n = zero} {m} {k} α =
    lem (inv' (compIso (invIso CharacFinBouquetFunIso)
                           Iso-Bouquet→∙-SphereBouquet₁→∙) α) α
         (rightInv (compIso (invIso CharacFinBouquetFunIso)
                                 Iso-Bouquet→∙-SphereBouquet₁→∙) α)
    where
    Goal : (α : _) (s : (w : _) → _) → Type
    Goal α s =
      Σ[ ϕ ∈ AbGroupIso
               (AbelianizationAbGroup (π'Gr zero (cofib∙ (fst α))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst α))) ]
         ((w : Fin k) → fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])
    module _ (α' : Fin m → FreeGroup (Fin k)) where
      gens→finSphereBouquetMap∙ : SphereBouquet∙ 1 (Fin m)
                               →∙ SphereBouquet∙ 1 (Fin k)
      gens→finSphereBouquetMap∙ = fun Iso-Bouquet→∙-SphereBouquet₁→∙
                                   (inv' CharacFinBouquetFunIso α')

      gens→finSphereBouquetMap∙snd : snd gens→finSphereBouquetMap∙ ≡ refl
      gens→finSphereBouquetMap∙snd = cong₃ _∙∙_∙∙_ (λ _ → refl)
        (cong (cong (fst (fun (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
              (inv' CharacFinBouquetFunIso α'))))
              (cong₂ _∙_ (cong sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit refl)))
                (cong₃ _∙∙_∙∙_ (sym (rUnit _)
                  ∙ cong (cong (inv' (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))))
                         lem) refl (sym (rUnit _))
                ∙ sym (rUnit refl))
              ∙ sym (rUnit refl) ))
        (cong₃ _∙∙_∙∙_ refl refl
          (sym (lUnit _) ∙ ∙∙lCancel _))
          ∙ cong₃ _∙∙_∙∙_ refl refl (sym (rUnit refl))
          ∙ sym (rUnit refl)
         where
         lem : rightInv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))
              ((fst (isoToEquiv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))))
                (pt (Bouquet∙ (Fin m))))) ≡ refl
         lem = ∙∙lCancel _

      module _ (lock : lockUnit {ℓ-zero}) where
        lockIso : Iso _ _
        lockIso =
          fst (invGroupIso ((π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α')
                lock))

      η' : _ → Abelianization (π'Gr 0 (cofib∙ (fst gens→finSphereBouquetMap∙)))
      η' = η

      presGen : (lock : _) (w : Fin k) (t : _)
        (p : t ≡ πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
        → inv' (lockIso lock) t ≡ [ ℤFinGenerator w ]
      presGen l w t p =
        (cong (fun (fst (Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock α' l)))
            (lem3 l))
          ∙ lem l
        where
        lem : (l : _)
          → fun (fst (Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock α' l))
                [ η (η w) ] ≡ [ ℤFinGenerator w ]
        lem unlock = refl

        lem2 : inv' (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst) [ η (η w) ]
            ≡ πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w
        lem2 = cong η' (cong ∣_∣₂
          (ΣPathP (funExt
          (λ { base i → inr (push w i)
            ; (loop i) j → inr (doubleCompPath-filler
                                 (push w)
                                 (λ j → inr (w , loop j))
                                 (sym (push w)) (~ j) i)})
            , ((sym (lUnit (sym (push (inl tt)))))
            ◁ compPath-filler' (λ i → inr (push w (~ i))) (sym (push (inl tt))))
            ▷ (cong₂ _∙_ refl (lUnit (sym (push (inl tt))))))
          ∙ λ i → preπ'FinSphereBouquetMapGenerator
                   (gens→finSphereBouquetMap α'
                   , gens→finSphereBouquetMap∙snd (~ i)) w))

        lem3 : (l : _)
          → fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock α' l
                  .fst) t ≡ [ η (η w) ]
        lem3 unlock =
            cong (fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst)) p
          ∙ cong (fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst)) (sym lem2)
           ∙ rightInv (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst) [ η (η w) ]

        presGen' : (lock : _) (w : Fin k)
          → inv' (lockIso lock)
                  (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
          ≡ [ ℤFinGenerator w ]
        presGen' l w = presGen l w _ refl

        presGen⁻ : (lock : _)(w : Fin k)
          → fun (lockIso lock) [ ℤFinGenerator w ]
           ≡ (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
        presGen⁻ lock w =
           cong (fun (lockIso lock)) (sym (presGen lock w _ refl))
         ∙ rightInv (lockIso lock)
            (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)

      abstract
        lockIso' : (lock : lockUnit {ℓ-zero})
          → AbGroupIso (ℤ[Fin k ] /Im (bouquetDegree (gens→finSphereBouquetMap α')))
                      (AbelianizationAbGroup
                        (π'Gr zero (cofib∙ (gens→finSphereBouquetMap α'))))
        fst (lockIso' l) = lockIso l
        snd (lockIso' l) =
          isGroupHomInv (GroupIso→GroupEquiv
            (π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α' l))

      G : lockUnit → (a : (w : _) → _) (t : (w : _)
        → a w ≡ (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w))
        → Goal gens→finSphereBouquetMap∙ a
      fst (G l a t) = π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α' l
      snd (G l a t) w = cong (inv' (lockIso l)) (t w) ∙ presGen l w _ refl


    lem : (w : Fin m → FreeGroup (Fin k))
          (α : SphereBouquet∙ (suc zero) (Fin m)
            →∙ SphereBouquet∙ (suc zero) (Fin k))
          (s : fun Iso-Bouquet→∙-SphereBouquet₁→∙
                  (inv' CharacFinBouquetFunIso w) ≡ α)
         → Goal α (πᵃᵇFinSphereBouquetMapGenerator α)
    lem w = J> G w unlock _ (λ _ → refl)
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain {n = suc n} {m} {k} α =
    →Goal unlock _ (λ _ → refl)
    where
    open πCofibFinSphereBouquetMap _ _ _ α

    lockIso : (lock : lockUnit {ℓ-zero})
      → GroupIso (π'Gr (suc n) (cofib∙ (fst α)))
                  (AbGroup→Group (ℤ[Fin k ] /Im (bouquetDegree (fst α))))
    lockIso unlock = π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α

    lockInvIso : (lock : lockUnit {ℓ-zero}) → _
    lockInvIso lock = invGroupIso (lockIso lock)

    lockInvHom = GroupIso→GroupHom (lockInvIso unlock)

    lockInvIso≡ : (l : _) (f : _)
      → inv' (fst (lockInvIso l)) f
       ≡ fun (fst Iso3) (fun (fst Iso2) (fun (fst Iso1) f))
    lockInvIso≡ unlock f = refl

    lockInvIso≡' : (f : _) (r : _) (q : _)
      → fun (fst (surjImIso (π'∘∙Hom (suc n) inr') isSurjective-π'∘∙Hominr))
                   (∣ r ∣₂ , ∣ q ∣₁) ≡ ∣ f ∣₂
      → fun (fst Iso3) (fun (fst Iso2) (fun (fst Iso1) ∣ f ∣₂))
       ≡ [ fst (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)) (fst q) ]
    lockInvIso≡' f r q t =
        cong (fun (fst (πCofibFinSphereBouquetMap.Iso3 n k _ α)))
             (cong (fun (fst (πCofibFinSphereBouquetMap.Iso2 n k _ α)))
               (cong (fun (fst (isoThm1 _)))
                 (sym (cong (inv' (fst (surjImIso (π'∘∙Hom (suc n) inr')
                                         isSurjective-π'∘∙Hominr))) t)
               ∙ leftInv (fst (surjImIso (π'∘∙Hom (suc n) inr')
                                isSurjective-π'∘∙Hominr))
                                  (∣ r ∣₂ , ∣ q ∣₁))))

    lockInvHomGen : (l : _) (w : _)
      → inv' (fst (lockInvIso l)) (π'FinSphereBouquetMapGenerator α w)
       ≡ [ ℤFinGenerator  w ]
    lockInvHomGen l w =
        lockInvIso≡ l (∣ preπ'FinSphereBouquetMapGenerator α w ∣₂)
      ∙ lockInvIso≡' _ (preπ'FinSphereBouquetMapGenerator α w)
                   (∣ (λ x → inr (w , x)) , sym (push w) ∣₂ , refl)
                   refl
       ∙ cong [_] (πₙ⋁Sⁿ≅ℤ[]Generator _ _ _)

    lockInvHomGen' : (l : lockUnit {ℓ-zero}) (w : _) (s : _)
      (q : π'FinSphereBouquetMapGenerator α w ≡ s)
      → fun (fst (lockIso l)) s  ≡ [ ℤFinGenerator  w ]
    lockInvHomGen' l w = J> lockInvHomGen l w

    Goal : (s : (w : _) → _) → Type
    Goal s =
      Σ[ ϕ ∈ (AbGroupIso (AbelianizationAbGroup (π'Gr (suc n) (cofib∙ (fst α))))
                        (ℤ[Fin k ] /Im (bouquetDegree (fst α)))) ]
         ((w : Fin k) → fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])

    →Goal : lockUnit {ℓ-zero} → (s : (w : _) → _)
            (p : (w : _) → s w ≡ πᵃᵇFinSphereBouquetMapGenerator α w) → Goal s
    fst (→Goal l s p) =
      compGroupIso (invGroupIso (AbelianizationIdempotent
                                  (Group→AbGroup _ (π'-comm _))))
                   (lockIso l)
    snd (→Goal l s p) w =
      cong (fun (fst (lockIso l)))
         (cong (inv' (fst (AbelianizationIdempotent
                           (Group→AbGroup _ (π'-comm _))))) (p w))
      ∙ lockInvHomGen' l w _ refl

-- Main results of file --
module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where

  -- πₙᵃᵇ(cofib α) ≅ ℤ[]/Im α
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree :
    AbGroupIso (AbelianizationAbGroup (π'Gr n (cofib∙ (fst α))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst α)))
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree =
    fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain α)

  -- Characterisation of generators
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens : (w : Fin k) →
    fun (fst π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree)
      (πᵃᵇFinSphereBouquetMapGenerator α w) ≡ [ ℤFinGenerator w ]
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens =
    snd (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain α)
