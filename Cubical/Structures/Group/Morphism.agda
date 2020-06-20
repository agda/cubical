{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Structures.Group.Base
open import Cubical.Structures.Macro
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

-- The following definition of GroupHom and GroupIso are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
  module G = Group G
  module H = Group H
  
isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → Group.is-set H _ _

GroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
GroupHom G H = Σ (⟨ G ⟩ → ⟨ H ⟩) (isGroupHom G H)

record GroupIso (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupiso

  field
    fun : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun fun)

-- Morphism composition
isGroupHomComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (fst g ∘ fst f)
isGroupHomComp F G H (f , morph-f) (g , morph-g) x y =
  cong g (morph-f _ _) ∙ morph-g _ _
  
compGroupHom : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → GroupHom F G → GroupHom G H → GroupHom F H
compGroupHom F G H (f , morph-f) (g , morph-g) =
  g ∘ f , isGroupHomComp F G H (f , morph-f) (g , morph-g)

compGroupIso : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupIso F G → GroupIso G H → GroupIso F H
compGroupIso {F = F} {G = G} {H = H} (groupiso f morph-f) (groupiso g morph-g) =
  groupiso (compEquiv f g) (isGroupHomComp F G H (fst f , morph-f) (fst g , morph-g))

idGroupIso : (G : Group {ℓ}) → GroupIso G G
idGroupIso G = groupiso (idEquiv (Group.Carrier G)) (λ _ _ → refl)

-- Isomorphism inversion
isGroupHomInv : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupIso G H) → isGroupHom H G (invEq (GroupIso.fun f))
isGroupHomInv G H  (groupiso (f , eq) morph) h h' = isInj-f _ _ (
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

invGroupIso : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupIso G H → GroupIso H G
invGroupIso G H (groupiso f morph) = groupiso (invEquiv f) (isGroupHomInv G H (groupiso f morph))

groupHomEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupHom G H) → (fst f ≡ fst g) → f ≡ g
groupHomEq G H f g p = Σ≡Prop (λ _ → isPropIsGroupHom G H) p

groupIsoEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupIso G H) → (GroupIso.fun f ≡ GroupIso.fun g) → f ≡ g
-- This proof would take one line with Σ≡Prop using Σ-types
groupIsoEq G H (groupiso f fm) (groupiso g gm) p i =
  groupiso (p i)
  (isOfHLevel→isOfHLevelDep 1 (λ f → isPropIsGroupHom G H {f}) fm gm (cong equivFun p) i)

module GroupΣ-theory {ℓ} where

  raw-group-structure : Type ℓ → Type ℓ
  raw-group-structure = SemigroupΣ-theory.raw-semigroup-structure

  raw-group-is-SNS : SNS raw-group-structure _
  raw-group-is-SNS = SemigroupΣ-theory.raw-semigroup-is-SNS

  -- The neutral element and the inverse function will be derived from the
  -- axioms, instead of being defined in the raw-group-structure in order
  -- to have that isomorphisms between groups are equivalences that preserves
  -- multiplication (so we don't have to show that they also preserve inversion
  -- and neutral element, although they will preserve them).
  group-axioms : (G : Type ℓ) → raw-group-structure G → Type ℓ
  group-axioms G _·_ =
      IsSemigroup _·_
    × (Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x))
                × ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e)))

  group-structure : Type ℓ → Type ℓ
  group-structure = add-to-structure raw-group-structure group-axioms

  GroupΣ : Type (ℓ-suc ℓ)
  GroupΣ = TypeWithStr ℓ group-structure

  -- Iso for groups are those for monoids (but different axioms)
  group-iso : StrIso group-structure ℓ
  group-iso = add-to-iso (binaryFunIso pointed-iso) group-axioms

  open monoid-theory

  isProp-group-axioms : (G : Type ℓ)
                      → (s : raw-group-structure G)
                      → isProp (group-axioms G s)
  isProp-group-axioms G _+_ = isPropΣ (isPropIsSemigroup _) γ
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

  group-is-SNS : SNS group-structure group-iso
  group-is-SNS = add-axioms-SNS _ isProp-group-axioms raw-group-is-SNS

  GroupΣPath : (G H : GroupΣ) → (G ≃[ group-iso ] H) ≃ (G ≡ H)
  GroupΣPath = SIP group-is-SNS

  GroupIsoΣ : (G H : Group) → Type ℓ
  GroupIsoΣ G H = Group→GroupΣ G ≃[ group-iso ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group} → Iso (GroupIso G H) (GroupIsoΣ G H)
  fun GroupIsoΣPath (groupiso e h) = (e , h)
  inv GroupIsoΣPath (e , h)        = groupiso e h
  rightInv GroupIsoΣPath _         = refl
  leftInv GroupIsoΣPath _          = refl

  GroupPath : (G H : Group) → (GroupIso G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupIso G H                    ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupIsoΣ G H                   ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H ■

-- Extract the characterization of equality of groups
GroupPath : (G H : Group {ℓ}) → (GroupIso G H) ≃ (G ≡ H)
GroupPath = GroupΣ-theory.GroupPath

Group-ua : {G H : Group {ℓ}} → (GroupIso G H) → (G ≡ H)
Group-ua {G = G} {H = H} = equivFun (GroupPath G H)

caracGroup-ua : {G H : Group {ℓ}} (f : GroupIso G H) → cong Group.Carrier (Group-ua f) ≡ ua (GroupIso.fun f)
caracGroup-ua (groupiso f m) =
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
    (isOfHLevelPathP' 1 (λ i → transport (cong isSet λ j → t (i ∧ j)) (is-set G)) (0g G) (0g H)) λ t₁ → isPropΣ
    (isOfHLevelPathP' 1 (λ i → transport (cong isSet λ j → t (i ∧ j) → t (i ∧ j) → t (i ∧ j)) (isSetΠ2 λ _ _ → is-set G)) (_+_ G) (_+_ H)) λ t₂ → isPropΣ
    (isOfHLevelPathP' 1 (λ i → transport (cong isSet λ j → t (i ∧ j) → t (i ∧ j)) (isSetΠ λ _ → is-set G)) (-_ G) (-_ H))
    (λ t₃ → isOfHLevelPathP 1 (λ i → transport (cong isProp λ j → IsGroup (t₁ (i ∧ j)) (t₂ (i ∧ j)) (t₃ (i ∧ j))) (isPropIsGroup _ _ _)) (isGroup G) (isGroup H)))
  t)

Group-ua-id : (G : Group {ℓ}) → Group-ua (idGroupIso G) ≡ refl
Group-ua-id G = caracGroup≡ _ _ (caracGroup-ua (idGroupIso G) ∙ uaIdEquiv)

Group-uaCompIso : {F G H : Group {ℓ}} (f : GroupIso F G) (g : GroupIso G H) → Group-ua (compGroupIso f g) ≡ Group-ua f ∙ Group-ua g
Group-uaCompIso f g = caracGroup≡ _ _ (
  cong Carrier (Group-ua (compGroupIso f g))
    ≡⟨ caracGroup-ua (compGroupIso f g) ⟩
  ua (fun (compGroupIso f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (fun f) ∙ ua (fun g)
    ≡⟨ cong (_∙ ua (fun g)) (sym (caracGroup-ua f)) ⟩
  cong Carrier (Group-ua f) ∙ ua (fun g)
    ≡⟨ cong (cong Carrier (Group-ua f) ∙_) (sym (caracGroup-ua g)) ⟩
  cong Carrier (Group-ua f) ∙ cong Carrier (Group-ua g)
    ≡⟨ sym (cong-∙ Carrier (Group-ua f) (Group-ua g)) ⟩
  cong Carrier (Group-ua f ∙ Group-ua g) ∎) where
  open GroupIso
