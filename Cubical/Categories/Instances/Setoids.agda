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
open import Cubical.Categories.Equivalence.AdjointEquivalence
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

open import Cubical.Categories.Category.Path

open import Cubical.Categories.Instances.Cat

open import Cubical.Categories.Monoidal

open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Slice.Functor

open import Cubical.HITs.SetQuotients as /
open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open Functor



-- SETPullback : ∀ ℓ → Pullbacks (SET ℓ)
-- SETPullback ℓ (cospan l m r s₁ s₂) = w
--  where
--  open Pullback
--  w : Pullback (SET ℓ) (cospan l m r s₁ s₂)
--  pbOb w = _ , isSetΣ (isSet× (snd l) (snd r))
--   (uncurry λ x y → isOfHLevelPath 2 (snd m) (s₁ x) (s₂ y))
--  pbPr₁ w = fst ∘ fst
--  pbPr₂ w = snd ∘ fst
--  pbCommutes w = funExt snd
--  fst (fst (univProp w h k H')) d = _ , (H' ≡$ d)
--  snd (fst (univProp w h k H')) = refl , refl
--  snd (univProp w h k H') y =
--   Σ≡Prop
--    (λ _ → isProp× (isSet→ (snd l) _ _) (isSet→ (snd r) _ _))
--     (funExt λ x → Σ≡Prop (λ _ → (snd m) _ _)
--        λ i → fst (snd y) i x , snd (snd y) i x)
   
-- module SetLCCC ℓ {X@(_ , isSetX) Y@(_ , isSetY) : hSet ℓ} (f : ⟨ X ⟩ →  ⟨ Y ⟩) where
--  open BaseChange (SETPullback ℓ)

--  open Cubical.Categories.Adjoint.NaturalBijection
--  open _⊣_

--  open import Cubical.Categories.Instances.Cospan
--  open import Cubical.Categories.Limits.Limits

--  Π/ : Functor (SliceCat (SET ℓ) X) (SliceCat (SET ℓ) Y)
--  F-ob Π/ (sliceob {S-ob = _ , isSetA} h) =
--    sliceob {S-ob = _ , (isSetΣ isSetY $
--                      λ y → isSetΠ λ ((x , _) : fiber f y) →
--                            isOfHLevelFiber 2 isSetA isSetX h x)} fst
--  F-hom Π/ {a} {b} (slicehom g p) =
--    slicehom (map-snd (map-sndDep (λ q → (p ≡$ _) ∙ q ) ∘_)) refl
--  F-id Π/ = SliceHom-≡-intro' _ _ $
--    funExt λ x' → cong ((fst x') ,_)
--      (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)
--  F-seq Π/ _ _ = SliceHom-≡-intro' _ _ $
--    funExt λ x' → cong ((fst x') ,_)
--      (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)

--  f*⊣Π/ : f ＊ ⊣ Π/
--  Iso.fun (adjIso f*⊣Π/) (slicehom h p) =
--    slicehom (λ _ → _ , λ (_ , q) → h (_ , q) , (p ≡$ _)) refl
--  Iso.inv (adjIso f*⊣Π/) (slicehom h p) =
--    slicehom _  $ funExt λ (_ , q) → snd (snd (h _) (_ , q ∙ ((sym p) ≡$ _))) 
--  Iso.rightInv (adjIso f*⊣Π/) b = SliceHom-≡-intro' _ _ $
--     funExt λ _ → cong₂ _,_ (sym (S-comm b ≡$ _))
--       $ toPathP $ funExt λ _ →
--         Σ≡Prop (λ _ → isSetX _ _) $ transportRefl _ ∙
--           cong (fst ∘ snd (S-hom b _))
--                (Σ≡Prop (λ _ → isSetY _ _) $ transportRefl _)
--  Iso.leftInv (adjIso f*⊣Π/) a = SliceHom-≡-intro' _ _ $
--    funExt λ _ → cong (S-hom a) $ Σ≡Prop (λ _ → isSetY _ _) refl
--  adjNatInD f*⊣Π/ _ _ = SliceHom-≡-intro' _ _ $
--    funExt λ _ → cong₂ _,_ refl $
--      funExt λ _ → Σ≡Prop (λ _ → isSetX _ _) refl
--  adjNatInC f*⊣Π/ g h = SliceHom-≡-intro' _ _ $
--    funExt λ _ → cong (fst ∘ (snd (S-hom g (S-hom h _)) ∘ (_ ,_))) $ isSetY _ _ _ _

-- --  Σ/ : Functor (SliceCat (SET ℓ) X) (SliceCat (SET ℓ) Y)
-- --  F-ob Σ/ (sliceob {S-ob = ob} arr) = sliceob {S-ob = ob} (f ∘ arr )
-- --  F-hom Σ/ (slicehom g p) = slicehom _ (cong (f ∘_) p)
-- --  F-id Σ/ = refl
-- --  F-seq Σ/ _ _ = SliceHom-≡-intro' _ _ $ refl

-- --  Σ/⊣f* : Σ/ ⊣ BaseChangeFunctor
-- --  Iso.fun (adjIso Σ/⊣f*) (slicehom g p) = slicehom (λ _ → _ , (sym p ≡$ _ )) refl 
-- --  Iso.inv (adjIso Σ/⊣f*) (slicehom g p) = slicehom (snd ∘ fst ∘ g) $
-- --   funExt (λ x → sym (snd (g x))) ∙ cong (f ∘_) p
-- --  Iso.rightInv (adjIso Σ/⊣f*) (slicehom g p) =
-- --   SliceHom-≡-intro' _ _ $
-- --    funExt λ xx → Σ≡Prop (λ _ → isSetY _ _)
-- --     (ΣPathP (sym (p ≡$ _) , refl))
-- --  Iso.leftInv (adjIso Σ/⊣f*) _ = SliceHom-≡-intro' _ _ $ refl
-- --  adjNatInD Σ/⊣f* _ _ = SliceHom-≡-intro' _ _ $
-- --     funExt λ x → Σ≡Prop (λ _ → isSetY _ _) refl 
-- --  adjNatInC Σ/⊣f* _ _ = SliceHom-≡-intro' _ _ $ refl


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

  SETOID' : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
  SETOID' = ΣPropCat (Cat ℓ ℓ) ((λ C → _ , isProp× (isPropIsThin C) (isPropIsGroupoidCat C)) ∘ fst)


  SETOID→SETOID' : Functor SETOID SETOID' 
  F-ob SETOID→SETOID' ((X , isSetX) , ((_∼_ , isProp∼) , isEquivRel∼))  = (w , isSetX)
      , isProp∼ , λ f → isiso (symmetric _ _ f) (isProp∼ _ _ _ _) (isProp∼ _ _ _ _)
    where
    open BinaryRelation.isEquivRel isEquivRel∼
    w : (Category ℓ ℓ)
    ob w = X
    Hom[_,_] w = _∼_
    id w = reflexive _
    _⋆_ w = transitive'
    ⋆IdL w _ = isProp∼ _ _ _ _
    ⋆IdR w _ = isProp∼ _ _ _ _
    ⋆Assoc w _ _ _ = isProp∼ _ _ _ _
    isSetHom w = isProp→isSet (isProp∼ _ _)

  F-hom SETOID→SETOID' {y = (_ , ((_ , isProp∼') , _))} (f , f-resp) = w
    where
    w : Functor _ _
    F-ob w = f
    F-hom w = f-resp
    F-id w = isProp∼' _ _ _ _
    F-seq w _ _ = isProp∼' _ _ _ _
  F-id SETOID→SETOID' = Functor≡ (λ _ → refl) λ _ → refl
  F-seq SETOID→SETOID' _ _ = Functor≡ (λ _ → refl) λ _ → refl

  SETOID'→SETOID : Functor SETOID' SETOID
  F-ob SETOID'→SETOID ((C , isSetCob) , thin , isGrpCat) =
    (_ , isSetCob) , (C [_,_] , thin) ,
      BinaryRelation.equivRel (λ _ → C .id) (λ _ _ → isIso.inv ∘ isGrpCat)
        λ _ _ _ → C ._⋆_
    
  F-hom SETOID'→SETOID F = _ , F-hom F
  F-id SETOID'→SETOID = refl
  F-seq SETOID'→SETOID _ _ = refl

  -- open AdjointEquivalence
  -- WE : AdjointEquivalence SETOID SETOID'
  -- fun WE = SETOID→SETOID'
  -- inv WE = SETOID'→SETOID
  -- NatTrans.N-ob (NatIso.trans (η WE)) _ = _
  -- NatTrans.N-hom (NatIso.trans (η WE)) _ = refl
  -- NatIso.nIso (η WE) _ = snd (idCatIso)
  -- F-ob (NatTrans.N-ob (NatIso.trans (ε WE)) _) = idfun _
  -- F-hom (NatTrans.N-ob (NatIso.trans (ε WE)) _) = idfun _
  -- F-id (NatTrans.N-ob (NatIso.trans (ε WE)) _) = refl
  -- F-seq (NatTrans.N-ob (NatIso.trans (ε WE)) _) _ _ = refl
  -- NatTrans.N-hom (NatIso.trans (ε WE)) _ = Functor≡ (λ _ → refl) (λ _ → refl)
  -- F-ob (isIso.inv (NatIso.nIso (ε WE) (_ , _ , isGrpCat))) = idfun _
  -- F-hom (isIso.inv (NatIso.nIso (ε WE) (_ , _ , isGrpCat))) = idfun _
  -- F-id (isIso.inv (NatIso.nIso (ε WE) (_ , _ , isGrpCat))) = refl
  -- F-seq (isIso.inv (NatIso.nIso (ε WE) (_ , _ , isGrpCat))) _ _ = refl
  -- isIso.sec (NatIso.nIso (ε WE) (_ , _ , isGrpCat)) = {!SetoidMor !}
  -- isIso.ret (NatIso.nIso (ε WE) (_ , _ , isGrpCat)) = {!!}
  -- triangleIdentities WE = {!!}

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


  -- -- works but slow!
  -- SetoidsMonoidalStrα :
  --     -⊗- ∘F (𝟙⟨ SETOID ⟩ ×F -⊗-) ≅ᶜ
  --     -⊗- ∘F (-⊗- ×F 𝟙⟨ SETOID ⟩) ∘F ×C-assoc SETOID SETOID SETOID
  -- NatTrans.N-ob (NatIso.trans SetoidsMonoidalStrα) _ =
  --   invEq Σ-assoc-≃ , invEq Σ-assoc-≃
  -- NatTrans.N-hom (NatIso.trans SetoidsMonoidalStrα) {x} {y} _ =
  --   SetoidMor≡
  --    (F-ob (-⊗- ∘F (𝟙⟨ SETOID ⟩ ×F -⊗-)) x)
  --     ((-⊗- ∘F (-⊗- ×F 𝟙⟨ SETOID ⟩) ∘F ×C-assoc SETOID SETOID SETOID)
  --      .F-ob y)
  --    refl
  -- isIso.inv (NatIso.nIso SetoidsMonoidalStrα _) =
  --   fst Σ-assoc-≃ , fst Σ-assoc-≃
  -- isIso.sec (NatIso.nIso SetoidsMonoidalStrα x) = refl
  -- isIso.ret (NatIso.nIso SetoidsMonoidalStrα x) = refl

  -- SetoidsMonoidalStrη : -⊗- ∘F rinj SETOID SETOID setoidUnit ≅ᶜ 𝟙⟨ SETOID ⟩
  -- NatIso.trans SetoidsMonoidalStrη =
  --   natTrans (λ _ → Iso.fun lUnit*×Iso , Iso.fun lUnit*×Iso)
  --            λ {x} {y} _ →
  --             SetoidMor≡ (F-ob (-⊗- ∘F rinj SETOID SETOID setoidUnit) x) y refl
  -- NatIso.nIso SetoidsMonoidalStrη x =
  --  isiso (Iso.inv lUnit*×Iso , Iso.inv lUnit*×Iso) refl refl

  -- SetoidsMonoidalStrρ :  -⊗- ∘F linj SETOID SETOID setoidUnit ≅ᶜ 𝟙⟨ SETOID ⟩
  -- NatIso.trans SetoidsMonoidalStrρ =
  --   natTrans (λ _ → Iso.fun rUnit*×Iso , Iso.fun rUnit*×Iso)
  --            λ {x} {y} _ →
  --             SetoidMor≡ (F-ob (-⊗- ∘F linj SETOID SETOID setoidUnit) x) y refl
  -- NatIso.nIso SetoidsMonoidalStrρ x =
  --  isiso (Iso.inv rUnit*×Iso , Iso.inv rUnit*×Iso) refl refl

  
  -- SetoidsMonoidalStr : MonoidalStr SETOID
  -- TensorStr.─⊗─ (MonoidalStr.tenstr SetoidsMonoidalStr) = -⊗-
  -- TensorStr.unit (MonoidalStr.tenstr SetoidsMonoidalStr) = setoidUnit
  -- MonoidalStr.α SetoidsMonoidalStr = SetoidsMonoidalStrα
  -- MonoidalStr.η SetoidsMonoidalStr = SetoidsMonoidalStrη
  -- MonoidalStr.ρ SetoidsMonoidalStr = SetoidsMonoidalStrρ
  -- MonoidalStr.pentagon SetoidsMonoidalStr w x y z = refl
  -- MonoidalStr.triangle SetoidsMonoidalStr x y = refl

  -- E-Category =
  --  EnrichedCategory (record { C = _ ; monstr = SetoidsMonoidalStr })

  -- E-SETOIDS : E-Category (ℓ-suc ℓ)
  -- EnrichedCategory.ob E-SETOIDS = Setoid ℓ ℓ
  -- EnrichedCategory.Hom[_,_] E-SETOIDS = _⟶_
  -- EnrichedCategory.id E-SETOIDS {x} =
  --   (λ _ → id SETOID {x}) ,
  --     λ _ _ → BinaryRelation.isEquivRel.reflexive (snd (snd x)) _
  -- EnrichedCategory.seq E-SETOIDS x y z =
  --   uncurry (_⋆_ SETOID {x} {y} {z})  ,
  --           λ {(f , g)} {(f' , g')} (fr , gr) a →
  --              transitive' (gr (fst f a)) (snd g' (fr a))
  --   where open BinaryRelation.isEquivRel (snd (snd z))
  -- EnrichedCategory.⋆IdL E-SETOIDS x y =
  --   SetoidMor≡ (setoidUnit ⊗ (x ⟶ y)) (x ⟶ y) refl
  -- EnrichedCategory.⋆IdR E-SETOIDS x y =
  --   SetoidMor≡ ((x ⟶ y) ⊗ setoidUnit) (x ⟶ y) refl
  -- EnrichedCategory.⋆Assoc E-SETOIDS x y z w =
  --   SetoidMor≡ ((x ⟶ y) ⊗ ( (y ⟶ z) ⊗ (z ⟶ w))) (x ⟶ w) refl



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





  -- open BaseChange pullbacks public

  -- ¬BaseChange⊣SetoidΠ : ({X Y : ob SETOID} (f : SETOID .Hom[_,_] X Y) →
  --    Σ (Functor (SliceCat SETOID X) (SliceCat SETOID Y))
  --     (λ Πf → (_＊ {c = X} {d = Y} f) ⊣ Πf)) → ⊥.⊥
  -- ¬BaseChange⊣SetoidΠ isLCCC = Πob-full-rel Πob-full

  --  where

  --  𝕀 : Setoid ℓ ℓ
  --  𝕀 = (Lift Bool , isOfHLevelLift 2 isSetBool) , fullEquivPropRel

  --  𝟚 : Setoid ℓ ℓ
  --  𝟚 = (Lift Bool , isOfHLevelLift 2 isSetBool) ,
  --        ((_ , isOfHLevelLift 2 isSetBool) , isEquivRelIdRel)

  --  𝑨 : SetoidMor (setoidUnit {ℓ} {ℓ}) 𝕀
  --  𝑨 = (λ _ → lift true) , λ _ → _

  --  𝑨＊ = _＊ {c = (setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨

  --  𝟚/ = sliceob {S-ob = 𝟚} ((λ _ → tt*) , λ {x} {x'} _ → tt*) 


  --  open Σ (isLCCC {(setoidUnit {ℓ} {ℓ})} {𝕀} 𝑨) renaming (fst to ΠA ; snd to Π⊣A*)
  --  open _⊣_ Π⊣A* renaming (adjIso to aIso)    

  --  module lem2 where
  --   G = sliceob {S-ob = setoidUnit} ((λ x → lift false) , _)

  --   bcf =  𝑨＊ ⟅ G ⟆

  --   isPropFiberFalse : isProp (fiber (fst (S-arr (ΠA ⟅ 𝟚/ ⟆))) (lift false))
  --   isPropFiberFalse (x , p) (y , q) =
  --     Σ≡Prop (λ _ _ _ → cong (cong lift) (isSetBool _ _ _ _))
  --      ((cong (fst ∘ S-hom) (isoInvInjective (aIso {G} {𝟚/})
  --         (slicehom
  --           ((λ _ → x) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob (F-ob ΠA 𝟚/)))) _)
  --                ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → p)))
  --         ((slicehom
  --           ((λ _ → y) , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob (F-ob ΠA 𝟚/)))) _)
  --                ( SetoidMor≡ (S-ob G) 𝕀 (funExt λ _ → q))))
  --         (SliceHom-≡-intro' _ _
  --            (SetoidMor≡ (bcf .S-ob) (𝟚/ .S-ob)
  --              (funExt λ z → ⊥.rec (true≢false (cong lower (snd z)))
  --              ))))) ≡$ _ )
      
    
  --  module lem3 where
  --   G = sliceob {S-ob = 𝕀} (SETOID .id {𝕀})

  --   aL : Iso
  --          (fst (fst (S-ob 𝟚/)))
  --          (SliceHom SETOID setoidUnit ( 𝑨 ＊ ⟅ G ⟆) 𝟚/)
             
  --   fun aL h =
  --     slicehom ((λ _ → h)
  --       , λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd
  --               (S-ob 𝟚/))) _) refl
  --   inv aL (slicehom (f , _) _) = f (_ , refl)
  --   rightInv aL b =
  --     SliceHom-≡-intro' _ _
  --      (SetoidMor≡
  --     ((𝑨＊ ⟅ G ⟆)  .S-ob)
  --     (𝟚/ .S-ob) (funExt λ x' →
  --        cong (λ (x , y) → fst (S-hom b) ((tt* , x) , y))
  --          (isPropSingl _ _)))
  --   leftInv aL _ = refl

  --   lem3 : Iso (fst (fst (S-ob 𝟚/))) (SliceHom SETOID 𝕀 G (ΠA ⟅ 𝟚/ ⟆))
  --   lem3 = compIso aL (aIso {G} {𝟚/})



  --  module zzz3 = Iso (compIso LiftIso (lem3.lem3))


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
  --    true≢false (isoFunInjective (compIso LiftIso (lem3.lem3)) _ _
  --          $ SliceHom-≡-intro' _ _
  --            $ SetoidMor≡
  --             ((lem3.G) .S-ob)
  --             ((ΠA ⟅ 𝟚/ ⟆) .S-ob)
  --             (funExt (
  --         λ where (lift false) → (congS fst (lem2.isPropFiberFalse
  --                       (_ , ((cong fst (S-comm (fun (lem3.lem3) (lift true))) ≡$ lift false)))
  --                       (_ , (cong fst (S-comm (fun (lem3.lem3) (lift false))) ≡$ lift false))))
  --                 (lift true) → p))) 


  --  Πob-full : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
  --                     (fst (piPt false))
  --                     (fst (piPt true))
      
  --  Πob-full = 
  --     ((transitive' ((snd (S-hom (zzz3.fun false)) {lift true} {lift false} _))
  --           (transitive'
  --             ((BinaryRelation.isRefl→impliedByIdentity
  --                   (fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))) reflexive
  --                     (congS fst (lem2.isPropFiberFalse
  --                       (_ , ((cong fst (S-comm (fun (lem3.lem3) (lift false))) ≡$ lift false)))
  --                       (_ , (cong fst (S-comm (fun (lem3.lem3) (lift true))) ≡$ lift false))))
  --                       ))
  --             (snd (S-hom (zzz3.fun true)) {lift false} {lift true}  _))))

  --  Πob-full-rel : fst (fst (snd (S-ob (ΠA ⟅ 𝟚/ ⟆))))
  --                     (fst (piPt false))
  --                     (fst (piPt true))
  --     → ⊥.⊥
  --  Πob-full-rel rr = elim𝟚<fromIso ((invIso
  --          (compIso aL (aIso {sliceob ((λ _ → lift true) , _)} {𝟚/}))))
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
  --         (S-ob ((𝑨＊)
  --           ⟅ sliceob {S-ob = 𝕀} ((λ _ → lift true) , _) ⟆))  𝟚
  --             (funExt λ x → snd (S-hom b) {(_ , lift true) , refl} {x} _))
  --    leftInv aL _ = refl
 
  --    mB : Bool → (SliceHom SETOID 𝕀
  --                (sliceob {S-ob = 𝕀} ((λ _ → lift true) , (λ {x} {x'} _ → tt*))) (ΠA ⟅ 𝟚/ ⟆))
  --    mB b = slicehom ((λ _ → fst (piPt b)) ,
  --           λ _ → BinaryRelation.isEquivRel.reflexive (snd (snd (S-ob (ΠA ⟅ 𝟚/ ⟆)))) _)
  --         (ΣPathP ((funExt λ _ → snd (piPt b)) , refl) )


  --    mF mT mMix : _
  --    mF = mB false 
  --    mT = mB true 
  --    mMix = slicehom ((fst ∘ piPt) ∘ lower ,
  --        λ where {lift false} {lift false} _ → reflexive _
  --                {lift true} {lift true} _ → reflexive _
  --                {lift false} {lift true} _ → rr
  --                {lift true} {lift false} _ → symmetric _ _ rr)
  --                     ((ΣPathP ((funExt λ b → snd (piPt (lower b))) , refl) ))

