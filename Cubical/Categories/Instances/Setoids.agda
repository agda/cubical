{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Setoids where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Logic hiding (_⇒_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Functors
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Setoid

open import Cubical.HITs.SetQuotients as /
open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open Functor


module _ ℓ where
  SETOID : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
  ob SETOID = Setoid ℓ ℓ
  Hom[_,_] SETOID = SetoidMor
  fst (id SETOID) _ = _
  snd (id SETOID) r = r
  fst ((SETOID ⋆ _) _) = _
  snd ((SETOID ⋆ (_ , f)) (_ , g)) = g ∘ f
  ⋆IdL SETOID _ = refl
  ⋆IdR SETOID _ = refl
  ⋆Assoc SETOID _ _ _ = refl
  isSetHom SETOID {y = (_ , isSetB) , ((_ , isPropR) , _)} =
   isSetΣ (isSet→ isSetB) (isProp→isSet ∘ isPropRespects isPropR )

  open Iso

  IsoPathCatIsoSETOID : ∀ {x y} → Iso (x ≡ y) (CatIso SETOID x y)
  fun (IsoPathCatIsoSETOID) = pathToIso
  inv (IsoPathCatIsoSETOID {y = _ , ((y , _) , _) }) ((_ , r) , ci) =
    cong₂ _,_
     (TypeOfHLevel≡ 2 (isoToPath i))
     (toPathP (EquivPropRel≡
       ( substRel y ((cong fst c.sec ≡$ _) ∙_ ∘ transportRefl) ∘ r
       , snd c.inv ∘ substRel y (sym ∘ transportRefl))
       ))
   where
   module c = isIso ci
   i : Iso _ _
   fun i = _ ; inv i = fst c.inv
   rightInv i = cong fst c.sec ≡$_ ; leftInv i = cong fst c.ret ≡$_

  rightInv (IsoPathCatIsoSETOID {x = x} {y = y}) ((f , _) , _) =
    CatIso≡ _ _ (SetoidMor≡ x y
       (funExt λ _ → transportRefl _ ∙ cong f (transportRefl _)))
  leftInv (IsoPathCatIsoSETOID) a =
    ΣSquareSet (λ _ → isSetEquivPropRel)
      (TypeOfHLevelPath≡ 2 (λ _ →
       transportRefl _ ∙ cong (subst (fst ∘ fst) a) (transportRefl _)))

  isUnivalentSETOID : isUnivalent SETOID
  isUnivalent.univ isUnivalentSETOID _ _ =
   isoToIsEquiv IsoPathCatIsoSETOID


  Quot Forget : Functor SETOID (SET ℓ)
  IdRel FullRel : Functor (SET ℓ) SETOID


  F-ob Quot (_ , ((R , _) , _)) = (_ / R) , squash/
  F-hom Quot (f , r) = /.rec squash/ ([_] ∘  f) λ _ _ → eq/ _ _ ∘ r
  F-id Quot = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)
  F-seq Quot _ _ = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)

  F-ob IdRel A = A , (_ , snd A) , isEquivRelIdRel
  F-hom IdRel = _, cong _
  F-id IdRel = refl
  F-seq IdRel _ _ = refl

  F-ob Forget = fst
  F-hom Forget = fst
  F-id Forget = refl
  F-seq Forget _ _ = refl

  F-ob FullRel = _, fullEquivPropRel
  F-hom FullRel = _, _
  F-id FullRel = refl
  F-seq FullRel _ _ = refl

  isFullyFaithfulIdRel : isFullyFaithful IdRel
  isFullyFaithfulIdRel x y = isoToIsEquiv
    (iso _ fst
     (λ _ → SetoidMor≡ (IdRel ⟅ x ⟆) (IdRel ⟅ y ⟆) refl)
      λ _ → refl)

  isFullyFaithfulFullRel : isFullyFaithful FullRel
  isFullyFaithfulFullRel x y = isoToIsEquiv
    (iso _ fst (λ _ → refl) λ _ → refl)

  IdRel⇒FullRel : IdRel ⇒ FullRel
  NatTrans.N-ob IdRel⇒FullRel x = idfun _ , _
  NatTrans.N-hom IdRel⇒FullRel f = refl


  open Cubical.Categories.Adjoint.NaturalBijection
  open _⊣_

  Quot⊣IdRel : Quot ⊣ IdRel
  adjIso Quot⊣IdRel {d = (_ , isSetD)} = setQuotUniversalIso isSetD
  adjNatInD Quot⊣IdRel {c = c} {d' = d'} f k = SetoidMor≡ c (IdRel ⟅ d' ⟆) refl
  adjNatInC Quot⊣IdRel {d = d} g h =
   funExt (/.elimProp (λ _ → snd d _ _) λ _ → refl)

  IdRel⊣Forget : IdRel ⊣ Forget
  fun (adjIso IdRel⊣Forget) = fst
  inv (adjIso IdRel⊣Forget {d = d}) f =
    f , J (λ x' p → fst (fst (snd d)) (f _) (f x'))
      (BinaryRelation.isEquivRel.reflexive (snd (snd d)) (f _))
  rightInv (adjIso IdRel⊣Forget) _ = refl
  leftInv (adjIso IdRel⊣Forget {c = c} {d = d}) _ =
    SetoidMor≡ (IdRel ⟅ c ⟆) d refl
  adjNatInD IdRel⊣Forget _ _ = refl
  adjNatInC IdRel⊣Forget _ _ = refl

  Forget⊣FullRel : Forget ⊣ FullRel
  fun (adjIso Forget⊣FullRel) = _
  inv (adjIso Forget⊣FullRel) = fst
  rightInv (adjIso Forget⊣FullRel) _ = refl
  leftInv (adjIso Forget⊣FullRel) _ = refl
  adjNatInD Forget⊣FullRel _ _ = refl
  adjNatInC Forget⊣FullRel _ _ = refl


  pieces : Functor SETOID SETOID
  pieces = IdRel ∘F Quot

  points : Functor SETOID SETOID
  points = IdRel ∘F Forget

  pieces⊣points : pieces ⊣ points
  pieces⊣points = Compose.LF⊣GR Quot⊣IdRel IdRel⊣Forget

  points→pieces : points ⇒ pieces
  points→pieces =
      ε (adj'→adj _ _ IdRel⊣Forget)
   ●ᵛ η (adj'→adj _ _ Quot⊣IdRel)
   where open UnitCounit._⊣_

  piecesHavePoints : ∀ A →
    isEpic SETOID {points ⟅ A ⟆ } {pieces ⟅ A ⟆}
     (points→pieces ⟦ A ⟧)
  piecesHavePoints  A {z = z@((_ , isSetZ) , _) } =
    SetoidMor≡ (pieces ⟅ A ⟆) z ∘
      (funExt ∘ /.elimProp (λ _ → isSetZ _ _) ∘ funExt⁻ ∘ cong fst)

  pieces→≃→points : (A B : Setoid ℓ ℓ) →
         SetoidMor (pieces ⟅ A ⟆) B
       ≃ SetoidMor A (points ⟅ B ⟆)
  pieces→≃→points A B =
     NaturalBijection._⊣_.adjEquiv
       (pieces⊣points)
       {c = A} {d = B}

  -⊗- : Functor (SETOID ×C SETOID) SETOID
  F-ob -⊗- = uncurry _⊗_
  fst (F-hom -⊗- _) = _
  snd (F-hom -⊗- (f , g)) (x , y) = snd f x , snd g y
  F-id -⊗- = refl
  F-seq -⊗- _ _ = refl

  InternalHomFunctor : Functor (SETOID ^op ×C SETOID) SETOID
  F-ob InternalHomFunctor = uncurry _⟶_
  fst (F-hom InternalHomFunctor (f , g )) (_ , y) = _ , snd g ∘ y ∘ (snd f)
  snd (F-hom InternalHomFunctor (f , g)) q = snd g ∘ q ∘ fst f
  F-id InternalHomFunctor = refl
  F-seq InternalHomFunctor _ _ = refl

  -^_ : ∀ X → Functor SETOID SETOID
  -^_ X = (λF SETOID _ (SETOID ^op) InternalHomFunctor ⟅ X ⟆)

  -⊗_ : ∀ X → Functor SETOID SETOID
  -⊗_ X = (λF SETOID _ (SETOID) (-⊗- ∘F fst (Swap SETOID SETOID)) ⟅ X ⟆)

  ⊗⊣^ : ∀ X → (-⊗ X) ⊣ (-^ X)
  adjIso (⊗⊣^ X) {A} {B} = setoidCurryIso X A B
  adjNatInD (⊗⊣^ X) {A} {d' = C} _ _ = SetoidMor≡ A (X ⟶ C) refl
  adjNatInC (⊗⊣^ X) {A} {d = C} _ _ = SetoidMor≡ (A ⊗ X) C refl


  open WeakEquivalence
  open isWeakEquivalence

  module FullRelationsSubcategory = FullSubcategory SETOID
    (BinaryRelation.isFull ∘ EquivPropRel→Rel ∘ snd)

  FullRelationsSubcategory : Category _ _
  FullRelationsSubcategory = FullRelationsSubcategory.FullSubcategory

  FullRelationsSubcategory≅SET : WeakEquivalence FullRelationsSubcategory (SET ℓ)
  func FullRelationsSubcategory≅SET = Forget ∘F FullRelationsSubcategory.FullInclusion
  fullfaith (isWeakEquiv FullRelationsSubcategory≅SET) x y@(_ , is-full-rel) =
     isoToIsEquiv (iso _ (_, λ _ → is-full-rel _ _) (λ _ → refl)
       λ _ → SetoidMor≡ (fst x) (fst y) refl)
  esssurj (isWeakEquiv FullRelationsSubcategory≅SET) d =
    ∣ (FullRel ⟅ d ⟆ , _)  , idCatIso ∣₁

  module IdRelationsSubcategory = FullSubcategory SETOID
    (BinaryRelation.impliesIdentity ∘ EquivPropRel→Rel ∘ snd)

  IdRelationsSubcategory : Category _ _
  IdRelationsSubcategory = IdRelationsSubcategory.FullSubcategory

  IdRelationsSubcategory≅SET : WeakEquivalence IdRelationsSubcategory (SET ℓ)
  func IdRelationsSubcategory≅SET = Forget ∘F IdRelationsSubcategory.FullInclusion
  fullfaith (isWeakEquiv IdRelationsSubcategory≅SET)
    x@(_ , implies-id) y@((_ , ((rel , _) , is-equiv-rel)) , _) =
     isoToIsEquiv (iso _ (λ f → f , λ z →
      isRefl→impliedByIdentity rel reflexive (cong f (implies-id z))) (λ _ → refl)
       λ _ → SetoidMor≡ (fst x) (fst y) refl)
   where open BinaryRelation ; open isEquivRel is-equiv-rel

  esssurj (isWeakEquiv IdRelationsSubcategory≅SET) d =
    ∣ (IdRel ⟅ d ⟆ , idfun _)  , idCatIso ∣₁
