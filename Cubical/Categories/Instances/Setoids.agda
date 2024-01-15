{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Setoids where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Logic hiding (_⇒_)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Functors
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Setoid

open import Cubical.Categories.Monoidal

open import Cubical.Categories.Limits.Pullback

open import Cubical.HITs.SetQuotients as /
open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open Functor



SETPullback : ∀ ℓ → Pullbacks (SET ℓ)
SETPullback ℓ (cospan l m r s₁ s₂) = w
 where
 open Pullback
 w : Pullback (SET ℓ) (cospan l m r s₁ s₂)
 pbOb w = _ , isSetΣ (isSet× (snd l) (snd r))
  (uncurry λ x y → isOfHLevelPath 2 (snd m) (s₁ x) (s₂ y))
 pbPr₁ w = fst ∘ fst
 pbPr₂ w = snd ∘ fst
 pbCommutes w = funExt snd
 fst (fst (univProp w h k H')) d = _ , (H' ≡$ d)
 snd (fst (univProp w h k H')) = refl , refl
 snd (univProp w h k H') y =
  Σ≡Prop
   (λ _ → isProp× (isSet→ (snd l) _ _) (isSet→ (snd r) _ _))
    (funExt λ x → Σ≡Prop (λ _ → (snd m) _ _)
       λ i → fst (snd y) i x , snd (snd y) i x)
   
module SetLCCC ℓ {X@(_ , isSetX) Y@(_ , isSetY) : hSet ℓ} (f : ⟨ X ⟩ →  ⟨ Y ⟩) where
 open BaseChangeFunctor (SET ℓ) X (SETPullback ℓ) {Y} f

 open Cubical.Categories.Adjoint.NaturalBijection
 open _⊣_

 open import Cubical.Categories.Instances.Cospan
 open import Cubical.Categories.Limits.Limits

 Π/ : Functor (SliceCat (SET ℓ) X) (SliceCat (SET ℓ) Y)
 F-ob Π/ (sliceob {S-ob = _ , isSetA} h) =
   sliceob {S-ob = _ , (isSetΣ isSetY $
                     λ y → isSetΠ λ ((x , _) : fiber f y) →
                           isOfHLevelFiber 2 isSetA isSetX h x)} fst
 F-hom Π/ {a} {b} (slicehom g p) =
   slicehom (map-snd (map-sndDep (λ q → (p ≡$ _) ∙ q ) ∘_)) refl
 F-id Π/ = SliceHom-≡-intro' _ _ $
   funExt λ x' → cong ((fst x') ,_)
     (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)
 F-seq Π/ _ _ = SliceHom-≡-intro' _ _ $
   funExt λ x' → cong ((fst x') ,_)
     (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)

 f*⊣Π/ : BaseChangeFunctor ⊣ Π/
 Iso.fun (adjIso f*⊣Π/) (slicehom h p) =
   slicehom (λ _ → _ , λ (_ , q) → h (_ , q) , (p ≡$ _)) refl
 Iso.inv (adjIso f*⊣Π/) (slicehom h p) =
   slicehom _  $ funExt λ (_ , q) → snd (snd (h _) (_ , q ∙ ((sym p) ≡$ _))) 
 Iso.rightInv (adjIso f*⊣Π/) b = SliceHom-≡-intro' _ _ $
    funExt λ _ → cong₂ _,_ (sym (S-comm b ≡$ _))
      $ toPathP $ funExt λ _ →
        Σ≡Prop (λ _ → isSetX _ _) $ transportRefl _ ∙
          cong (fst ∘ snd (S-hom b _))
               (Σ≡Prop (λ _ → isSetY _ _) $ transportRefl _)
 Iso.leftInv (adjIso f*⊣Π/) a = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong (S-hom a) $ Σ≡Prop (λ _ → isSetY _ _) refl
 adjNatInD f*⊣Π/ _ _ = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong₂ _,_ refl $
     funExt λ _ → Σ≡Prop (λ _ → isSetX _ _) refl
 adjNatInC f*⊣Π/ g h = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong (fst ∘ (snd (S-hom g (S-hom h _)) ∘ (_ ,_))) $ isSetY _ _ _ _

 Σ/ : Functor (SliceCat (SET ℓ) X) (SliceCat (SET ℓ) Y)
 F-ob Σ/ (sliceob {S-ob = ob} arr) = sliceob {S-ob = ob} (f ∘ arr )
 F-hom Σ/ (slicehom g p) = slicehom _ (cong (f ∘_) p)
 F-id Σ/ = refl
 F-seq Σ/ _ _ = SliceHom-≡-intro' _ _ $ refl

 Σ/⊣f* : Σ/ ⊣ BaseChangeFunctor
 Iso.fun (adjIso Σ/⊣f*) (slicehom g p) = slicehom (λ _ → _ , (sym p ≡$ _ )) refl 
 Iso.inv (adjIso Σ/⊣f*) (slicehom g p) = slicehom (snd ∘ fst ∘ g) $
  funExt (λ x → sym (snd (g x))) ∙ cong (f ∘_) p
 Iso.rightInv (adjIso Σ/⊣f*) (slicehom g p) =
  SliceHom-≡-intro' _ _ $
   funExt λ xx → Σ≡Prop (λ _ → isSetY _ _)
    (ΣPathP (sym (p ≡$ _) , refl))
 Iso.leftInv (adjIso Σ/⊣f*) _ = SliceHom-≡-intro' _ _ $ refl
 adjNatInD Σ/⊣f* _ _ = SliceHom-≡-intro' _ _ $
    funExt λ x → Σ≡Prop (λ _ → isSetY _ _) refl 
 adjNatInC Σ/⊣f* _ _ = SliceHom-≡-intro' _ _ $ refl
 
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
  -^_ X = λF SETOID _ (SETOID ^op) InternalHomFunctor ⟅ X ⟆

  -⊗_ : ∀ X → Functor SETOID SETOID
  -⊗_ X = λF SETOID _ (SETOID) (-⊗- ∘F fst (Swap SETOID SETOID)) ⟅ X ⟆

  ⊗⊣^ : ∀ X → (-⊗ X) ⊣ (-^ X)
  adjIso (⊗⊣^ X) {A} {B} = setoidCurryIso X A B
  adjNatInD (⊗⊣^ X) {A} {d' = C} _ _ = SetoidMor≡ A (X ⟶ C) refl
  adjNatInC (⊗⊣^ X) {A} {d = C} _ _ = SetoidMor≡ (A ⊗ X) C refl

  -- SetoidsMonoidalStr : StrictMonStr SETOID
  -- TensorStr.─⊗─ (StrictMonStr.tenstr SetoidsMonoidalStr) = -⊗-
  -- TensorStr.unit (StrictMonStr.tenstr SetoidsMonoidalStr) = setoidUnit
  -- StrictMonStr.assoc SetoidsMonoidalStr _ _ _ =
  --  Setoid≡ _ _ (invEquiv Σ-assoc-≃) λ _ _ → invEquiv Σ-assoc-≃
  -- StrictMonStr.idl SetoidsMonoidalStr _ =
  --   Setoid≡ _ _ (isoToEquiv lUnit*×Iso) λ _ _ → isoToEquiv lUnit*×Iso
  -- StrictMonStr.idr SetoidsMonoidalStr _ =
  --   Setoid≡ _ _ (isoToEquiv rUnit*×Iso) λ _ _ → isoToEquiv rUnit*×Iso 
  
  SetoidsMonoidalStrα :
      -⊗- ∘F (𝟙⟨ SETOID ⟩ ×F -⊗-) ≅ᶜ
      -⊗- ∘F (-⊗- ×F 𝟙⟨ SETOID ⟩) ∘F ×C-assoc SETOID SETOID SETOID
  NatTrans.N-ob (NatIso.trans SetoidsMonoidalStrα) _ =
    invEq Σ-assoc-≃ , invEq Σ-assoc-≃
  NatTrans.N-hom (NatIso.trans SetoidsMonoidalStrα) {x} {y} _ =
    SetoidMor≡
     (F-ob (-⊗- ∘F (𝟙⟨ SETOID ⟩ ×F -⊗-)) x)
      ((-⊗- ∘F (-⊗- ×F 𝟙⟨ SETOID ⟩) ∘F ×C-assoc SETOID SETOID SETOID)
       .F-ob y)
     refl
  isIso.inv (NatIso.nIso SetoidsMonoidalStrα _) =
    fst Σ-assoc-≃ , fst Σ-assoc-≃
  isIso.sec (NatIso.nIso SetoidsMonoidalStrα x) = refl
  isIso.ret (NatIso.nIso SetoidsMonoidalStrα x) = refl

  SetoidsMonoidalStrη : -⊗- ∘F rinj SETOID SETOID setoidUnit ≅ᶜ 𝟙⟨ SETOID ⟩
  NatIso.trans SetoidsMonoidalStrη =
    natTrans (λ _ → Iso.fun lUnit*×Iso , Iso.fun lUnit*×Iso)
             λ {x} {y} _ →
              SetoidMor≡ (F-ob (-⊗- ∘F rinj SETOID SETOID setoidUnit) x) y refl
  NatIso.nIso SetoidsMonoidalStrη x =
   isiso (Iso.inv lUnit*×Iso , Iso.inv lUnit*×Iso) refl refl

  SetoidsMonoidalStrρ :  -⊗- ∘F linj SETOID SETOID setoidUnit ≅ᶜ 𝟙⟨ SETOID ⟩
  NatIso.trans SetoidsMonoidalStrρ =
    natTrans (λ _ → Iso.fun rUnit*×Iso , Iso.fun rUnit*×Iso)
             λ {x} {y} _ →
              SetoidMor≡ (F-ob (-⊗- ∘F linj SETOID SETOID setoidUnit) x) y refl
  NatIso.nIso SetoidsMonoidalStrρ x =
   isiso (Iso.inv rUnit*×Iso , Iso.inv rUnit*×Iso) refl refl


  SetoidsMonoidalStr : MonoidalStr SETOID
  TensorStr.─⊗─ (MonoidalStr.tenstr SetoidsMonoidalStr) = -⊗-
  TensorStr.unit (MonoidalStr.tenstr SetoidsMonoidalStr) = setoidUnit
  MonoidalStr.α SetoidsMonoidalStr = SetoidsMonoidalStrα
  MonoidalStr.η SetoidsMonoidalStr = SetoidsMonoidalStrη
  MonoidalStr.ρ SetoidsMonoidalStr = SetoidsMonoidalStrρ
  MonoidalStr.pentagon SetoidsMonoidalStr w x y z = refl
  MonoidalStr.triangle SetoidsMonoidalStr x y = refl

  E-Category =
   EnrichedCategory (record { C = _ ; monstr = SetoidsMonoidalStr })

  E-SETOIDS : E-Category (ℓ-suc ℓ)
  EnrichedCategory.ob E-SETOIDS = Setoid ℓ ℓ
  EnrichedCategory.Hom[_,_] E-SETOIDS = _⟶_
  EnrichedCategory.id E-SETOIDS {x} =
    (λ _ → id SETOID {x}) ,
      λ _ _ → BinaryRelation.isEquivRel.reflexive (snd (snd x)) _
  EnrichedCategory.seq E-SETOIDS x y z =
    uncurry (_⋆_ SETOID {x} {y} {z})  ,
            λ {(f , g)} {(f' , g')} (fr , gr) a →
               transitive' (gr (fst f a)) (snd g' (fr a))
    where open BinaryRelation.isEquivRel (snd (snd z))
  EnrichedCategory.⋆IdL E-SETOIDS x y =
    SetoidMor≡ (setoidUnit ⊗ (x ⟶ y)) (x ⟶ y) refl
  EnrichedCategory.⋆IdR E-SETOIDS x y =
    SetoidMor≡ ((x ⟶ y) ⊗ setoidUnit) (x ⟶ y) refl
  EnrichedCategory.⋆Assoc E-SETOIDS x y z w =
    SetoidMor≡ ((x ⟶ y) ⊗ ( (y ⟶ z) ⊗ (z ⟶ w))) (x ⟶ w) refl



  pullbacks : Pullbacks SETOID
  pullbacks cspn = w
   where
   open Cospan cspn
   open Pullback
   w : Pullback (SETOID) cspn
   pbOb w = PullbackSetoid l r m s₁ s₂
   pbPr₁ w = fst ∘ fst , fst
   pbPr₂ w = snd ∘ fst , snd 
   pbCommutes w = SetoidMor≡ (PullbackSetoid l r m s₁ s₂) m (funExt snd)
   fst (fst (univProp w h k H')) = (λ x → (fst h x , fst k x) ,
     (cong fst H' ≡$ x)) ,
      λ {a} {b} x → (snd h x) , (snd k x) 
   snd (fst (univProp w {d} h k H')) = SetoidMor≡ d l refl , SetoidMor≡ d r refl
   snd (univProp w {d} h k H') y = Σ≡Prop
     (λ _ → isProp× (isSetHom (SETOID) {d} {l} _ _)
                    (isSetHom (SETOID) {d} {r} _ _))
    (SetoidMor≡ d (PullbackSetoid l r m s₁ s₂)
     (funExt λ x → Σ≡Prop (λ _ → snd (fst m) _ _)
             (cong₂ _,_ (λ i → fst (fst (snd y) i) x)
                        (λ i → fst (snd (snd y) i) x))))


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


-- -- -- --   pullbacks : Pullbacks SETOID
-- -- -- --   pullbacks cspn = w
-- -- -- --    where
-- -- -- --    open Cospan cspn
-- -- -- --    open Pullback
-- -- -- --    w : Pullback (SETOID) cspn
-- -- -- --    pbOb w = PullbackSetoid l r m s₁ s₂
-- -- -- --    pbPr₁ w = fst ∘ fst , fst ∘ fst
-- -- -- --    pbPr₂ w = snd ∘ fst , snd ∘ fst
-- -- -- --    pbCommutes w = SetoidMor≡ (PullbackSetoid l r m s₁ s₂) m (funExt snd)
-- -- -- --    fst (fst (univProp w h k H')) = (λ x → (fst h x , fst k x) ,
-- -- -- --      (cong fst H' ≡$ x)) ,
-- -- -- --       λ {a} {b} x → ((snd h x) , (snd k x)) , snd s₁ ((snd h x)) 
-- -- -- --    snd (fst (univProp w {d} h k H')) = SetoidMor≡ d l refl , SetoidMor≡ d r refl
-- -- -- --    snd (univProp w {d} h k H') y = Σ≡Prop
-- -- -- --      (λ _ → isProp× (isSetHom (SETOID) {d} {l} _ _)
-- -- -- --                     (isSetHom (SETOID) {d} {r} _ _))
-- -- -- --     (SetoidMor≡ d (PullbackSetoid l r m s₁ s₂)
-- -- -- --      (funExt λ x → Σ≡Prop (λ _ → snd (fst m) _ _)
-- -- -- --              (cong₂ _,_ (λ i → fst (fst (snd y) i) x)
-- -- -- --                         (λ i → fst (snd (snd y) i) x))))


  module _ {X Y : ob SETOID} (f : SetoidMor X Y) where
   open BaseChangeFunctor SETOID X pullbacks {Y} f public

   SΣ : ∀ {X} → (x : SliceOb SETOID X) → _
   SΣ {X} = λ x → SetoidΣ (S-ob x) X (S-arr x)

   SΠ : ∀ {X} → (x : SliceOb SETOID X) → _
   SΠ {X} = λ x → setoidSection (S-ob x) X (S-arr x)

   SETOIDΣ : Functor (SliceCat SETOID X) (SliceCat SETOID Y)
   S-ob (F-ob SETOIDΣ x) = SΣ x
   S-arr (F-ob SETOIDΣ x) = SETOID ._⋆_ {SΣ x} {X} {Y}
    (setoidΣ-pr₁ (S-ob x) X (S-arr x)) f 
   fst (S-hom (F-hom SETOIDΣ x)) = fst (S-hom x)
   snd (S-hom (F-hom SETOIDΣ x)) x₁ =
    snd (S-hom x) (fst x₁) , subst2 (fst (fst (snd X)))
           (cong fst (sym (S-comm x)) ≡$ _)
           (cong fst (sym (S-comm x)) ≡$ _) (snd x₁) 
   S-comm (F-hom SETOIDΣ {x} {y} g)  =
     SetoidMor≡ (SΣ x) Y
       (funExt λ u → cong (fst f) (cong fst (S-comm g) ≡$ u))
   F-id SETOIDΣ {x = x} = SliceHom-≡-intro' _ _ 
    (SetoidMor≡ (SΣ x) (SΣ x) refl)
   F-seq SETOIDΣ {x = x} {_} {z} _ _ = SliceHom-≡-intro' _ _ 
    (SetoidMor≡ (SΣ x) (SΣ z) refl)

   SetoidΣ⊣BaseChange : SETOIDΣ ⊣ BaseChangeFunctor
   fst (S-hom (fun (adjIso SetoidΣ⊣BaseChange {c}) h)) x =
     (fst (S-arr c) x , fst (S-hom h) x ) , sym (cong fst (S-comm h) ≡$ x)
   snd (S-hom (fun (adjIso SetoidΣ⊣BaseChange {c}) h)) g =
      ((snd (S-arr c) g) , snd (S-hom h)  (g , snd (S-arr c) g))
   S-comm (fun (adjIso SetoidΣ⊣BaseChange {c} ) _) = SetoidMor≡ (S-ob c) X refl
   fst (S-hom (inv (adjIso SetoidΣ⊣BaseChange) h)) x =
     snd (fst (fst (S-hom h) x)) 
   snd (S-hom (inv (adjIso SetoidΣ⊣BaseChange) x)) {c} {d} (r , r') =
     snd (snd (S-hom x) r)
   S-comm (inv (adjIso SetoidΣ⊣BaseChange {c} {d}) (slicehom (x , _) y)) =
    SetoidMor≡ (SΣ c) Y
       (sym (funExt (snd ∘ x)) ∙ congS ((fst f ∘_) ∘ fst) y)
   rightInv (adjIso SetoidΣ⊣BaseChange {c} {d}) b = SliceHom-≡-intro' _ _
      (SetoidMor≡ (S-ob c) (S-ob (BaseChangeFunctor ⟅ d ⟆))
        (funExt λ x → Σ≡Prop (λ _ → snd (fst Y) _ _)
            (cong (_, _) (sym (cong fst (S-comm b) ≡$ x)))))
   leftInv (adjIso SetoidΣ⊣BaseChange {c} {d}) a = SliceHom-≡-intro' _ _
      (SetoidMor≡ ((S-ob (SETOIDΣ ⟅ c ⟆))) (S-ob d) refl)
   adjNatInD SetoidΣ⊣BaseChange {c} {_} {d'} _ _ = SliceHom-≡-intro' _ _
      (SetoidMor≡ (S-ob c) (S-ob (BaseChangeFunctor ⟅ d' ⟆))
        (funExt λ _ → Σ≡Prop (λ _ → snd (fst Y) _ _) refl))
   adjNatInC SetoidΣ⊣BaseChange _ _ = SliceHom-≡-intro' _ _ refl


  ¬BaseChange⊣SetoidΠ : ({X Y : ob SETOID} (f : SetoidMor X Y) →
     Σ _ (BaseChangeFunctor {X} {Y} f ⊣_)) → ⊥.⊥
  ¬BaseChange⊣SetoidΠ isLCCC = Πob-full-rel Πob-full

   where

   𝕀 : Setoid ℓ ℓ
   𝕀 = (Lift Bool , isOfHLevelLift 2 isSetBool) , fullEquivPropRel

   𝟚 : Setoid ℓ ℓ
   𝟚 = (Lift Bool , isOfHLevelLift 2 isSetBool) ,
         ((_ , isOfHLevelLift 2 isSetBool) , isEquivRelIdRel)

   𝑨 : SetoidMor (setoidUnit {ℓ} {ℓ}) 𝕀
   𝑨 = (λ _ → lift true) , λ _ → _

   𝟚/ = sliceob {S-ob = 𝟚} ((λ _ → tt*) , λ {x} {x'} _ → tt*) 


   open Σ (isLCCC {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨) renaming (fst to ΠA ; snd to Π⊣A*)
   open _⊣_ Π⊣A* renaming (adjIso to aIso)    

   module lem2 where
    G = sliceob {S-ob = setoidUnit} ((λ x → lift false) , _)

    bcf = BaseChangeFunctor {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨 ⟅ G ⟆

    isPropFiberFalse : isProp (fiber (fst (S-arr (ΠA ⟅ 𝟚/ ⟆))) (lift false))
    isPropFiberFalse (x , p) (y , q) =
      Σ≡Prop (λ _ _ _ → cong (cong lift) (isSetBool _ _ _ _))
       ((cong (fst ∘ S-hom) (isoInvInjective (aIso {G} {𝟚/})
          (slicehom
            ((λ _ → x) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
                (S-ob (F-ob ΠA 𝟚/)))) _)
                 ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → p)))
          ((slicehom
            ((λ _ → y) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
                (S-ob (F-ob ΠA 𝟚/)))) _)
                 ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → q))))
          (SliceHom-≡-intro' _ _
             (SetoidMor≡ (bcf .S-ob) (𝟚/ .S-ob)
               (funExt λ z → ⊥.rec (true≢false (cong lower (snd z)))
               ))))) ≡$ _ )
      
    
   module lem3 where
    G = sliceob {S-ob = 𝕀} (SETOID .id {𝕀})

    aL : Iso
           (fst (fst (S-ob 𝟚/)))
           (SliceHom SETOID setoidUnit (BaseChangeFunctor 𝑨 ⟅ G ⟆) 𝟚/)
             
    fun aL h =
      slicehom ((λ _ → h)
        , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
                (S-ob 𝟚/))) _) refl
    inv aL (slicehom (f , _) _) = f (_ , refl)
    rightInv aL b =
      SliceHom-≡-intro' _ _
       (SetoidMor≡
      ((BaseChangeFunctor {X = (setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨 ⟅ G ⟆)  .S-ob)
      (𝟚/ .S-ob) (funExt λ x' →
         cong (λ (x , y) → fst (S-hom b) ((tt* , x) , y))
           (isPropSingl _ _)))
    leftInv aL _ = refl

    lem3 : Iso (fst (fst (S-ob 𝟚/))) (SliceHom SETOID 𝕀 G (ΠA ⟅ 𝟚/ ⟆))
    lem3 = compIso aL (aIso {G} {𝟚/})



   module zzz3 = Iso (compIso LiftIso (lem3.lem3))


   open BinaryRelation.isEquivRel (snd (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))


   piPt : Bool → fiber
                    (fst
                     (S-arr
                      (ΠA ⟅ 𝟚/ ⟆))) (lift true)
   piPt b =  (fst (S-hom (zzz3.fun b)) (lift true)) ,
     (cong fst (S-comm (zzz3.fun b)) ≡$ lift true)
   


   finLLem : fst (piPt true) ≡ fst (piPt false)
              → ⊥.⊥
   finLLem p =
     true≢false (isoFunInjective (compIso LiftIso (lem3.lem3)) _ _
           $ SliceHom-≡-intro' _ _
             $ SetoidMor≡
              ((lem3.G) .S-ob)
              ((ΠA ⟅ 𝟚/ ⟆) .S-ob)
              (funExt (
          λ where (lift false) → (congS fst (lem2.isPropFiberFalse
                        (_ , ((cong fst (S-comm (fun (lem3.lem3) (lift true))) ≡$ lift false)))
                        (_ , (cong fst (S-comm (fun (lem3.lem3) (lift false))) ≡$ lift false))))
                  (lift true) → p))) 


   Πob-full : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
                      (fst (piPt false))
                      (fst (piPt true))
      
   Πob-full = 
      ((transitive' ((snd (S-hom (zzz3.fun false)) {lift true} {lift false} _))
            (transitive'
              ((BinaryRelation.isRefl→impliedByIdentity
                    (fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))) reflexive
                      (congS fst (lem2.isPropFiberFalse
                        (_ , ((cong fst (S-comm (fun (lem3.lem3) (lift false))) ≡$ lift false)))
                        (_ , (cong fst (S-comm (fun (lem3.lem3) (lift true))) ≡$ lift false))))
                        ))
              (snd (S-hom (zzz3.fun true)) {lift false} {lift true}  _))))

   Πob-full-rel : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
                      (fst (piPt false))
                      (fst (piPt true))
      → ⊥.⊥
   Πob-full-rel rr = elim𝟚<fromIso ((invIso
           (compIso aL (aIso {sliceob ((λ _ → lift true) , _)} {𝟚/}))))
          mT mF mMix
         ( finLLem ∘S cong λ x → fst (S-hom x) (lift false))
         (finLLem ∘S cong λ x → fst (S-hom x) (lift false))
         (finLLem ∘S (sym ∘S cong λ x → fst (S-hom x) (lift true)))
      
     where

     aL : Iso Bool
        ((SliceHom SETOID setoidUnit _  𝟚/))
     fun aL b = slicehom ((λ _ → lift b) , λ _ → refl) refl
     inv aL (slicehom f _) = lower (fst f ((_ , lift true) , refl ))
     rightInv aL b = SliceHom-≡-intro' _ _
        (SetoidMor≡
          (S-ob ((BaseChangeFunctor {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨)
            ⟅ sliceob {S-ob = 𝕀} ((λ _ → lift true) , _) ⟆))  𝟚
              (funExt λ x → snd (S-hom b) {(_ , lift true) , refl} {x} _))
     leftInv aL _ = refl
 
     mB : Bool → (SliceHom SETOID 𝕀
                 (sliceob {S-ob = 𝕀} ((λ _ → lift true) , (λ {x} {x'} _ → tt*))) (ΠA ⟅ 𝟚/ ⟆))
     mB b = slicehom ((λ _ → fst (piPt b)) ,
            λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd (S-ob (ΠA ⟅ 𝟚/ ⟆)))) _)
          (ΣPathP ((funExt λ _ → snd (piPt b)) , refl) )


     mF mT mMix : _
     mF = mB false 
     mT = mB true 
     mMix = slicehom ((fst ∘ piPt) ∘ lower ,
         λ where {lift false} {lift false} _ → reflexive _
                 {lift true} {lift true} _ → reflexive _
                 {lift false} {lift true} _ → rr
                 {lift true} {lift false} _ → symmetric _ _ rr)
                      ((ΣPathP ((funExt λ b → snd (piPt (lower b))) , refl) ))


  -- ¬BaseChange⊣SetoidΠ : ({X Y : ob SETOID} (f : SetoidMor X Y) →
  --    Σ _ (BaseChangeFunctor {X} {Y} f ⊣_)) → ⊥.⊥
  -- ¬BaseChange⊣SetoidΠ isLCCC = Πob-full-rel Πob-full

  --  where

  --  𝕀 : Setoid ℓ ℓ
  --  𝕀 = (Lift Bool , isOfHLevelLift 2 isSetBool) , fullEquivPropRel

  --  𝟚 : Setoid ℓ ℓ
  --  𝟚 = (Lift Bool , isOfHLevelLift 2 isSetBool) ,
  --        ((_ , isOfHLevelLift 2 isSetBool) , isEquivRelIdRel)

  --  𝑨 : SetoidMor (setoidUnit {ℓ} {ℓ}) 𝕀
  --  𝑨 = (λ _ → lift true) , λ _ → _

  --  open Σ (isLCCC {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨) renaming (fst to ΠA ; snd to Π⊣A*)
  --  open _⊣_ Π⊣A* renaming (adjIso to aIso)    

  --  module lem2 (H : _) where
  --   G = sliceob {S-ob = setoidUnit} ((λ x → lift false) , _)

  --   bcf = BaseChangeFunctor {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨 ⟅ G ⟆

  --   isPropFiberFalse : isProp (fiber (fst (S-arr (ΠA ⟅ H ⟆))) (lift false))
  --   isPropFiberFalse (x , p) (y , q) =
  --     Σ≡Prop (λ _ _ _ → cong (cong lift) (isSetBool _ _ _ _))
  --      ((cong (fst ∘ S-hom) (isoInvInjective (aIso {G} {H})
  --         (slicehom
  --           ((λ _ → x) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob (F-ob ΠA H)))) _)
  --                ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → p)))
  --         ((slicehom
  --           ((λ _ → y) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob (F-ob ΠA H)))) _)
  --                ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → q))))
  --         (SliceHom-≡-intro' _ _
  --            (SetoidMor≡ (bcf .S-ob) (H .S-ob)
  --              (funExt λ z → ⊥.rec (true≢false (cong lower (snd z)))
  --              ))))) ≡$ _ )
      
    
  --  module lem3 (H : _) where
  --   G = sliceob {S-ob = 𝕀} (SETOID .id {𝕀})

  --   aI : Iso (SliceHom SETOID setoidUnit (BaseChangeFunctor 𝑨 ⟅ G ⟆) H)
  --            (SliceHom SETOID 𝕀 G (ΠA ⟅ H ⟆))
  --   aI = aIso {G} {H}

  --   aL : Iso
  --          (fst (fst (S-ob H)))
  --          (SliceHom SETOID setoidUnit (BaseChangeFunctor 𝑨 ⟅ G ⟆) H)
             
  --   fun aL h =
  --     slicehom ((λ _ → h)
  --       , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob H))) _) refl
  --   inv aL (slicehom (f , _) _) = f (_ , refl)
  --   rightInv aL b =
  --     SliceHom-≡-intro' _ _
  --      (SetoidMor≡
  --     ((BaseChangeFunctor {X = (setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨 ⟅ G ⟆)  .S-ob)
  --     (H .S-ob) (funExt λ x' →
  --        cong (λ (x , y) → fst (S-hom b) ((tt* , x) , y))
  --          (isPropSingl _ _)))
  --   leftInv aL _ = refl

  --   lem3 : Iso (fst (fst (S-ob H))) (SliceHom SETOID 𝕀 G (ΠA ⟅ H ⟆))
  --   lem3 = compIso aL aI

  --   open BinaryRelation.isEquivRel (snd (snd (S-ob (ΠA ⟅ H ⟆))))

  --  𝟚/ = sliceob {S-ob = 𝟚} ((λ _ → tt*) , λ {x} {x'} _ → tt*) 


  --  module zzz3 = Iso (compIso LiftIso (lem3.lem3 𝟚/))


  --  open BinaryRelation.isEquivRel (snd (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))


  --  piPt : Bool → fiber
  --                   (fst
  --                    (S-arr
  --                     (ΠA ⟅ 𝟚/ ⟆))) (lift true)
  --  piPt b =  (fst (S-hom (zzz3.fun b)) (lift true)) ,
  --    (cong fst (S-comm (zzz3.fun b)) ≡$ lift true)
   


  --  finLLem : fst (piPt true) ≡ fst (piPt false)
  --             → ⊥.⊥
  --  finLLem p =
  --    true≢false (isoFunInjective (compIso LiftIso (lem3.lem3 𝟚/)) _ _
  --          $ SliceHom-≡-intro' _ _
  --            $ SetoidMor≡
  --             ((lem3.G 𝟚/) .S-ob)
  --             ((ΠA ⟅ 𝟚/ ⟆) .S-ob)
  --             (funExt (
  --         λ where (lift false) → (congS fst (lem2.isPropFiberFalse 𝟚/
  --                       (_ , ((cong fst (S-comm (fun (lem3.lem3 𝟚/) (lift true))) ≡$ lift false)))
  --                       (_ , (cong fst (S-comm (fun (lem3.lem3 𝟚/) (lift false))) ≡$ lift false))))
  --                 (lift true) → p))) 


  --  Πob-full : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
  --                     (fst (S-hom (zzz3.fun false)) (lift true))
  --                     (fst (S-hom (zzz3.fun true)) (lift true))
      
  --  Πob-full = 
  --     ((transitive' ((snd (S-hom (zzz3.fun false)) {lift true} {lift false} _))
  --           (transitive'
  --             ((BinaryRelation.isRefl→impliedByIdentity
  --                   (fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))) reflexive
  --                     (congS fst (lem2.isPropFiberFalse 𝟚/
  --                       (_ , ((cong fst (S-comm (fun (lem3.lem3 𝟚/) (lift false))) ≡$ lift false)))
  --                       (_ , (cong fst (S-comm (fun (lem3.lem3 𝟚/) (lift true))) ≡$ lift false))))
  --                       ))
  --             (snd (S-hom (zzz3.fun true)) {lift false} {lift true}  _))))

  --  Πob-full-rel : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
  --                     (fst (S-hom (zzz3.fun false)) (lift true))
  --                     (fst (S-hom (zzz3.fun true)) (lift true))
  --     → ⊥.⊥
  --  Πob-full-rel rr = elim𝟚<fromIso ((invIso (compIso aL aI)))
  --         mT mF mMix
  --        ( finLLem ∘S cong λ x → fst (S-hom x) (lift false))
  --        (finLLem ∘S cong λ x → fst (S-hom x) (lift false))
  --        (finLLem ∘S (sym ∘S cong λ x → fst (S-hom x) (lift true)))
      
  --    where

  --    aL : Iso Bool
  --       ((SliceHom SETOID setoidUnit _  𝟚/))
  --    fun aL b = slicehom ((λ _ → lift b) , λ _ → refl) refl
  --    inv aL (slicehom f _) = lower (fst f ((_ , lift true) , refl ))
  --    rightInv aL b = SliceHom-≡-intro' _ _
  --       (SetoidMor≡
  --         (S-ob ((BaseChangeFunctor {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨)
  --           ⟅ sliceob {S-ob = 𝕀} ((λ _ → lift true) , _) ⟆))  𝟚
  --             (funExt λ x → snd (S-hom b) {(_ , lift true) , refl} {x} _))
  --    leftInv aL _ = refl
 
  --    aI : Iso (SliceHom SETOID setoidUnit (sliceob {S-ob = _} ((λ _ → tt*) , (λ {x} {x'} _ → tt*)))  𝟚/)
  --              (SliceHom SETOID 𝕀
  --                (sliceob {S-ob = 𝕀} ((λ _ → lift true) , (λ {x} {x'} _ → tt*))) (ΠA ⟅ 𝟚/ ⟆))
  --    aI = aIso {sliceob ((λ _ → lift true) , _)} {𝟚/}   

  --    mB : Bool → (SliceHom SETOID 𝕀
  --                (sliceob {S-ob = 𝕀} ((λ _ → lift true) , (λ {x} {x'} _ → tt*))) (ΠA ⟅ 𝟚/ ⟆))
  --    mB b = slicehom ((λ _ → fst (piPt b)) ,
  --           λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd (S-ob (ΠA ⟅ 𝟚/ ⟆)))) _)
  --         (ΣPathP ((funExt λ _ → snd (piPt b)) , refl) )


  --    mF mT mMix : 

  --            (SliceHom SETOID 𝕀
  --                (sliceob {S-ob = 𝕀} ((λ _ → lift true) , (λ {x} {x'} _ → tt*))) (ΠA ⟅ 𝟚/ ⟆))
  --    mF = mB false --mB false
  --    mT = mB true --mB true
  --    mMix = 
  --      slicehom ((fst ∘ piPt) ∘ lower ,
  --        λ where {lift false} {lift false} _ → reflexive _
  --                {lift true} {lift true} _ → reflexive _
  --                {lift false} {lift true} _ → rr
  --                {lift true} {lift false} _ → symmetric _ _ rr)
  --                     ((ΣPathP ((funExt λ b → snd (piPt (lower b))) , refl) ))
