{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Structures.Group.Base
open import Cubical.Structures.Axioms
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
  module G = Group G
  module H = Group H
  
isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → Group.is-set H _ _

record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor grouphom

  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : isGroupHom G H fun

record GroupEquiv (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupequiv

  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun eq)

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom

-- Morphism composition
isGroupHomComp : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (GroupHom.fun g ∘ GroupHom.fun f)
isGroupHomComp (grouphom f morph-f) (grouphom g morph-g) x y =
  cong g (morph-f _ _) ∙ morph-g _ _

compGroupHom : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupHom F G → GroupHom G H → GroupHom F H
compGroupHom {F = F} {G = G} {H = H} f g = grouphom _ (isGroupHomComp f g)

compGroupEquiv : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
compGroupEquiv {F = F} {G = G} {H = H} f g =
  groupequiv (compEquiv f.eq g.eq) (isGroupHomComp f.hom g.hom) where
  module f = GroupEquiv f
  module g = GroupEquiv g

idGroupEquiv : (G : Group {ℓ}) → GroupEquiv G G
idGroupEquiv G = groupequiv (idEquiv (Group.Carrier G)) (λ _ _ → refl)

-- Isomorphism inversion
isGroupHomInv : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupEquiv G H) → isGroupHom H G (invEq (GroupEquiv.eq f))
isGroupHomInv G H  (groupequiv (f , eq) morph) h h' = isInj-f _ _ (
  f (g (h ⋆² h') )
    ≡⟨ retEq (f , eq) _ ⟩
  h ⋆² h'
    ≡⟨ sym (λ i → retEq (f , eq) h i ⋆² retEq (f , eq) h' i) ⟩
  f (g h) ⋆² f (g h')
    ≡⟨ sym (morph _ _) ⟩
  f (g h ⋆¹ g h') ∎)
  where
  _⋆¹_ = Group._+_ G
  _⋆²_ = Group._+_ H
  g = invEq (f , eq)
  isEmbedding-f : isEmbedding f
  isEmbedding-f = isEquiv→isEmbedding eq
  isInj-f : (x y : ⟨ G ⟩) → f x ≡ f y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding eq x y)

invGroupEquiv : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupEquiv G H → GroupEquiv H G
invGroupEquiv G H (groupequiv f morph) = groupequiv (invEquiv f) (isGroupHomInv G H (groupequiv f morph))

groupHomEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupHom G H) → (GroupHom.fun f ≡ GroupHom.fun g) → f ≡ g
groupHomEq G H (grouphom f fm) (grouphom g gm) p i = grouphom (p i) (p-hom i) where
  p-hom : PathP (λ i → isGroupHom G H (p i)) fm gm
  p-hom = toPathP (isPropIsGroupHom G H _ _)

groupEquivEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupEquiv G H) → (GroupEquiv.eq f ≡ GroupEquiv.eq g) → f ≡ g
groupEquivEq G H (groupequiv f fm) (groupequiv g gm) p i = groupequiv (p i) (p-hom i) where
  p-hom : PathP (λ i → isGroupHom G H (p i .fst)) fm gm
  p-hom = toPathP (isPropIsGroupHom G H _ _)

module GroupΣTheory {ℓ} where

  RawGroupStructure : Type ℓ → Type ℓ
  RawGroupStructure = SemigroupΣTheory.RawSemigroupStructure

  rawGroupUnivalentStr : UnivalentStr RawGroupStructure _
  rawGroupUnivalentStr = SemigroupΣTheory.rawSemigroupUnivalentStr

  -- The neutral element and the inverse function will be derived from the
  -- axioms, instead of being defined in the RawGroupStructure in order
  -- to have that group equivalences are equivalences that preserves
  -- multiplication (so we don't have to show that they also preserve inversion
  -- and neutral element, although they will preserve them).
  GroupAxioms : (G : Type ℓ) → RawGroupStructure G → Type ℓ
  GroupAxioms G _·_ =
      IsSemigroup _·_
    × (Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x))
                × ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e)))

  GroupStructure : Type ℓ → Type ℓ
  GroupStructure = AxiomsStructure RawGroupStructure GroupAxioms

  GroupΣ : Type (ℓ-suc ℓ)
  GroupΣ = TypeWithStr ℓ GroupStructure

  -- Structured equivalences for groups are those for monoids (but different axioms)
  GroupEquivStr : StrEquiv GroupStructure ℓ
  GroupEquivStr = AxiomsEquivStr (BinaryFunEquivStr PointedEquivStr) GroupAxioms

  open MonoidTheory

  isPropGroupAxioms : (G : Type ℓ)
                      → (s : RawGroupStructure G)
                      → isProp (GroupAxioms G s)
  isPropGroupAxioms G _+_ = isPropΣ (isPropIsSemigroup _) γ
    where
    γ : (h : IsSemigroup _+_) →
        isProp (Σ[ e ∈ G ] ((x : G) → (x + e ≡ x) × (e + x ≡ x))
                         × ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e)))
    γ h (e , P , _) (e' , Q , _) =
      Σ≡Prop (λ x → isPropΣ (isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)) (β x))
             (sym (fst (Q e)) ∙ snd (P e'))
      where
      isSetG : isSet G
      isSetG = IsSemigroup.is-set h

      β : (e : G) → ((x : G) → (x + e ≡ x) × (e + x ≡ x))
        → isProp ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e))
      β e He =
        isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
                Σ≡Prop (λ _ → isProp× (isSetG _ _) (isSetG _ _))
                       (inv-lemma ℳ x x' x'' P Q) }
        where
        ℳ : Monoid
        ℳ = makeMonoid e _+_ isSetG (IsSemigroup.assoc h) (λ x → He x .fst) (λ x → He x .snd)

  Group→GroupΣ : Group → GroupΣ
  Group→GroupΣ (group _ _ _ -_ isGroup) =
   _ , _ , IsMonoid.isSemigroup (IsGroup.isMonoid isGroup) ,
   _ , IsMonoid.identity (IsGroup.isMonoid isGroup) ,
   λ x → (- x) , IsGroup.inverse isGroup x

  GroupΣ→Group : GroupΣ → Group
  GroupΣ→Group (_ , _ , SG , _ , H0g , w ) =
     group _ _ _ (λ x → w x .fst) (isgroup (ismonoid SG H0g) λ x → w x .snd)

  GroupIsoGroupΣ : Iso Group GroupΣ
  GroupIsoGroupΣ = iso Group→GroupΣ GroupΣ→Group (λ _ → refl) (λ _ → refl)

  groupUnivalentStr : UnivalentStr GroupStructure GroupEquivStr
  groupUnivalentStr = axiomsUnivalentStr _ isPropGroupAxioms rawGroupUnivalentStr

  GroupΣPath : (G H : GroupΣ) → (G ≃[ GroupEquivStr ] H) ≃ (G ≡ H)
  GroupΣPath = SIP groupUnivalentStr

  GroupEquivΣ : (G H : Group) → Type ℓ
  GroupEquivΣ G H = Group→GroupΣ G ≃[ GroupEquivStr ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group} → Iso (GroupEquiv G H) (GroupEquivΣ G H)
  fun GroupIsoΣPath (groupequiv e h) = (e , h)
  inv GroupIsoΣPath (e , h)        = groupequiv e h
  rightInv GroupIsoΣPath _         = refl
  leftInv GroupIsoΣPath _          = refl

  GroupPath : (G H : Group) → (GroupEquiv G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupEquiv G H                    ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupEquivΣ G H                   ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H ■

-- Extract the characterization of equality of groups
GroupPath : (G H : Group {ℓ}) → (GroupEquiv G H) ≃ (G ≡ H)
GroupPath = GroupΣTheory.GroupPath

uaGroup : {G H : Group {ℓ}} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

carac-uaGroup : {G H : Group {ℓ}} (f : GroupEquiv G H) → cong Group.Carrier (uaGroup f) ≡ ua (GroupEquiv.eq f)
carac-uaGroup (groupequiv f m) =
  (refl ∙∙ ua f ∙∙ refl)
    ≡⟨ sym (rUnit (ua f)) ⟩
  ua f ∎

-- Group-ua functoriality
open Group

Group≡ : (G H : Group {ℓ}) → (
  Σ[ p ∈ Carrier G ≡ Carrier H ]
  Σ[ q ∈ PathP (λ i → p i) (0g G) (0g H) ]
  Σ[ r ∈ PathP (λ i → p i → p i → p i) (_+_ G) (_+_ H) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (-_ G) (-_ H) ]
  PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup G) (isGroup H))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv (iso
  (λ (p , q , r , s , t) i → group (p i) (q i) (r i) (s i) (t i))
  (λ p → cong Carrier p , cong 0g p , cong _+_ p , cong -_ p , cong isGroup p)
  (λ _ → refl) (λ _ → refl))

caracGroup≡ : {G H : Group {ℓ}} (p q : G ≡ H) → cong Group.Carrier p ≡ cong Group.Carrier q → p ≡ q
caracGroup≡ {G = G} {H = H} p q t = cong (fst (Group≡ G H)) (Σ≡Prop (λ t →
  isPropΣ
    (isOfHLevelPathP' 1 (is-set H) _ _) λ t₁ → isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set H) _ _) λ t₂ → isPropΣ
    (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set H) _ _) λ t₃ →
    isOfHLevelPathP 1 (isPropIsGroup _ _ _) _ _)
  t)

Group-ua-id : (G : Group {ℓ}) → uaGroup (idGroupEquiv G) ≡ refl
Group-ua-id G = caracGroup≡ _ _ (carac-uaGroup (idGroupEquiv G) ∙ uaIdEquiv)

uaCompGroupEquiv : {F G H : Group {ℓ}} (f : GroupEquiv F G) (g : GroupEquiv G H) → uaGroup (compGroupEquiv f g) ≡ uaGroup f ∙ uaGroup g
uaCompGroupEquiv f g = caracGroup≡ _ _ (
  cong Carrier (uaGroup (compGroupEquiv f g))
    ≡⟨ carac-uaGroup (compGroupEquiv f g) ⟩
  ua (eq (compGroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡⟨ cong (_∙ ua (eq g)) (sym (carac-uaGroup f)) ⟩
  cong Carrier (uaGroup f) ∙ ua (eq g)
    ≡⟨ cong (cong Carrier (uaGroup f) ∙_) (sym (carac-uaGroup g)) ⟩
  cong Carrier (uaGroup f) ∙ cong Carrier (uaGroup g)
    ≡⟨ sym (cong-∙ Carrier (uaGroup f) (uaGroup g)) ⟩
  cong Carrier (uaGroup f ∙ uaGroup g) ∎) where
  open GroupEquiv

