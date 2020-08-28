{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Pointed
open import Cubical.Algebra.Semigroup hiding (⟨_⟩)
open import Cubical.Algebra.Monoid    hiding (⟨_⟩)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphism

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso
open Group
open GroupHom

isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → Group.is-set H _ _

isSetGroupHom : {G : Group {ℓ}} {H : Group {ℓ'}} → isSet (GroupHom G H)
isSetGroupHom {G = G} {H = H} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set H) λ _ → isProp→isSet (isPropIsGroupHom G H)) where
  equiv : (Σ[ g ∈ (Carrier G → Carrier H) ] (isGroupHom G H g)) ≃ (GroupHom G H)
  equiv =  isoToEquiv (iso (λ (g , m) → grouphom g m) (λ hom → fun hom , isHom hom) (λ a → η-hom _) λ _ → refl)

-- Morphism composition
isGroupHomComp : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (fun g ∘ fun f)
isGroupHomComp f g x y = cong (fun g) (isHom f _ _) ∙ isHom g _ _


compGroupHom : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupHom F G → GroupHom G H → GroupHom F H
fun (compGroupHom f g) = fun g ∘ fun f
isHom (compGroupHom f g) = isGroupHomComp f g

open GroupEquiv
compGroupEquiv : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
eq (compGroupEquiv f g) = compEquiv (eq f) (eq g)
isHom (compGroupEquiv f g) = isHom (compGroupHom (hom f) (hom g))

idGroupEquiv : (G : Group {ℓ}) → GroupEquiv G G
eq (idGroupEquiv G) = idEquiv ⟨ G ⟩
isHom (idGroupEquiv G) = λ _ _ → refl

-- Isomorphism inversion
isGroupHomInv : {G : Group {ℓ}} {H : Group {ℓ'}} (f : GroupEquiv G H) → isGroupHom H G (invEq (GroupEquiv.eq f))
isGroupHomInv {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ retEq (eq f) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (retEq (eq f) h) (retEq (eq f) h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (hom f) _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fst (eq f)
  _⋆¹_ = _+_ G
  _⋆²_ = _+_ H
  g = invEq (eq f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (eq f)) x y)

invGroupEquiv : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupEquiv G H → GroupEquiv H G
eq (invGroupEquiv f) = invEquiv (eq f)
isHom (invGroupEquiv f) = isGroupHomInv f

dirProdEquiv : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
           → GroupEquiv A C → GroupEquiv B D
           → GroupEquiv (dirProd A B) (dirProd C D)
eq (dirProdEquiv eq1 eq2) = ≃-× (eq eq1) (eq eq2)
isHom (dirProdEquiv eq1 eq2) = isHom (×hom (GroupEquiv.hom eq1) (GroupEquiv.hom eq2))

groupHomEq : {G : Group {ℓ}} {H : Group {ℓ'}} {f g : GroupHom G H} → (fun f ≡ fun g) → f ≡ g
fun (groupHomEq p i) = p i
isHom (groupHomEq {G = G} {H = H} {f = f} {g = g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)


groupEquivEq : {G : Group {ℓ}} {H : Group {ℓ'}} {f g : GroupEquiv G H} → (eq f ≡ eq g) → f ≡ g
eq (groupEquivEq {G = G} {H = H} {f} {g} p i) = p i
isHom (groupEquivEq {G = G} {H = H} {f} {g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i .fst)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)

module GroupΣTheory {ℓ} where

  RawGroupStructure : Type ℓ → Type ℓ
  RawGroupStructure = SemigroupΣTheory.RawSemigroupStructure

  RawGroupEquivStr : StrEquiv RawGroupStructure _
  RawGroupEquivStr = SemigroupΣTheory.RawSemigroupEquivStr

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
  GroupEquivStr = AxiomsEquivStr RawGroupEquivStr GroupAxioms

  open MonoidTheory

  isSetGroupΣ : (G : GroupΣ)
               → isSet _
  isSetGroupΣ (_ , _ , (isSemigroup-G , _ , _)) = IsSemigroup.is-set isSemigroup-G

  isPropGroupAxioms : (G : Type ℓ)
                      → (s : RawGroupStructure G)
                      → isProp (GroupAxioms G s)
  isPropGroupAxioms G _+_ = isPropΣ (isPropIsSemigroup _) γ
    where
    γ : (h : IsSemigroup _+_) →
        isProp (Σ[ e ∈ G ] ((x : G) → (x + e ≡ x) × (e + x ≡ x))
                         × ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e)))
    γ h (e , P , _) (e' , Q , _) =
      Σ≡Prop (λ x → isPropΣ (isPropΠ λ _ → isProp× ((IsSemigroup.is-set h) _ _) ((IsSemigroup.is-set h) _ _)) (β x))
             (sym (fst (Q e)) ∙ snd (P e'))
      where
      β : (e : G) → ((x : G) → (x + e ≡ x) × (e + x ≡ x))
        → isProp ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e))
      β e He =
        isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
                Σ≡Prop (λ _ → isProp× ((IsSemigroup.is-set h) _ _) ((IsSemigroup.is-set h) _ _))
                       (inv-lemma ℳ x x' x'' P Q) }
        where
        ℳ : Monoid
        ℳ = makeMonoid e _+_ (IsSemigroup.is-set h) (IsSemigroup.assoc h) (λ x → He x .fst) (λ x → He x .snd)

  Group→GroupΣ : Group → GroupΣ
  Group→GroupΣ G = _ , _ ,
                  ((isSemigroup G)
                  , _
                  , (identity G)
                  , λ x → (- G) x
                    , inverse G x)

  GroupΣ→Group : GroupΣ → Group
  GroupΣ→Group (G , _ , SG , _ , H0g , invertible ) =
     group _ _ _ (λ x → invertible x .fst) (isgroup (ismonoid SG H0g) λ x → invertible x .snd)

  GroupIsoGroupΣ : Iso Group GroupΣ
  GroupIsoGroupΣ = iso Group→GroupΣ GroupΣ→Group (λ _ → refl) helper
    where
    open MonoidΣTheory
    monoid-helper : retract (Monoid→MonoidΣ {ℓ}) MonoidΣ→Monoid
    monoid-helper = Iso.leftInv MonoidIsoMonoidΣ

    helper : retract (λ z → Group→GroupΣ z) GroupΣ→Group
    Carrier (helper a i) = ⟨ a ⟩
    0g (helper a i) = 0g a
    _+_ (helper a i) = (_+_) a
    - helper a i = - a
    IsGroup.isMonoid (isGroup (helper a i)) =
      Monoid.isMonoid (monoid-helper (monoid (Carrier a) (0g a) (_+_ a) (isMonoid a)) i)
    IsGroup.inverse (isGroup (helper a i)) = inverse a

  groupUnivalentStr : UnivalentStr GroupStructure GroupEquivStr
  groupUnivalentStr = axiomsUnivalentStr _ isPropGroupAxioms rawGroupUnivalentStr

  GroupΣPath : (G H : GroupΣ) → (G ≃[ GroupEquivStr ] H) ≃ (G ≡ H)
  GroupΣPath = SIP groupUnivalentStr

  GroupEquivΣ : (G H : Group) → Type ℓ
  GroupEquivΣ G H = Group→GroupΣ G ≃[ GroupEquivStr ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group} → Iso (GroupEquiv G H) (GroupEquivΣ G H)
  fun GroupIsoΣPath f = (eq f) , isHom f
  inv GroupIsoΣPath (e , h) = groupequiv e h
  rightInv GroupIsoΣPath _ = refl
  leftInv GroupIsoΣPath _ = η-equiv _


  GroupPath : (G H : Group) → (GroupEquiv G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupEquiv G H                    ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupEquivΣ G H                   ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H ■

  RawGroupΣ : Type (ℓ-suc ℓ)
  RawGroupΣ = TypeWithStr ℓ RawGroupStructure

  open Group
  Group→RawGroupΣ : Group → RawGroupΣ
  Group→RawGroupΣ G = ⟨ G ⟩ , (_+_ G)

  InducedGroup : (G : Group) (H : RawGroupΣ) (e : G .Carrier ≃ H .fst)
               → RawGroupEquivStr (Group→RawGroupΣ G) H e → Group
  InducedGroup G H e r =
    GroupΣ→Group (transferAxioms rawGroupUnivalentStr (Group→GroupΣ G) H (e , r))

  InducedGroupPath : (G : Group {ℓ}) (H : RawGroupΣ) (e : G .Carrier ≃ H .fst)
                     (E : RawGroupEquivStr (Group→RawGroupΣ G) H e)
                   → G ≡ InducedGroup G H e E
  InducedGroupPath G H e E =
    GroupPath G (InducedGroup G H e E) .fst (groupequiv e E)


-- Extract the characterization of equality of groups
GroupPath : (G H : Group {ℓ}) → (GroupEquiv G H) ≃ (G ≡ H)
GroupPath = GroupΣTheory.GroupPath

InducedGroup : (G : Group {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : G .Carrier ≃ H .fst)
             → GroupΣTheory.RawGroupEquivStr (GroupΣTheory.Group→RawGroupΣ G) H e
             → Group
InducedGroup = GroupΣTheory.InducedGroup

InducedGroupPath : (G : Group {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : G .Carrier ≃ H .fst)
                   (E : GroupΣTheory.RawGroupEquivStr (GroupΣTheory.Group→RawGroupΣ G) H e)
                 → G ≡ InducedGroup G H e E
InducedGroupPath = GroupΣTheory.InducedGroupPath


uaGroup : {G H : Group {ℓ}} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

carac-uaGroup : {G H : Group {ℓ}} (f : GroupEquiv G H) → cong Carrier (uaGroup f) ≡ ua (GroupEquiv.eq f)
carac-uaGroup f = ua (eq f) ∙ refl ≡⟨ sym (rUnit _)  ⟩
                  ua (eq f) ∎

-- Group-ua functoriality

Group≡ : (G H : Group {ℓ}) → (
  Σ[ p ∈ Carrier G ≡ Carrier H ]
  Σ[ q ∈ PathP (λ i → p i) (0g G) (0g H) ]
  Σ[ r ∈ PathP (λ i → p i → p i → p i) (_+_ G) (_+_ H) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (-_ G) (-_ H) ]
  PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup G) (isGroup H))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv theIso
  where
  theIso : Iso _ _
  Carrier (fun theIso (p , q , r , s , t) i) = p i
  0g (fun theIso (p , q , r , s , t) i) = q i
  _+_ (fun theIso (p , q , r , s , t) i) = r i
  - fun theIso (p , q , r , s , t) i = s i
  isGroup (fun theIso (p , q , r , s , t) i) = t i
  inv theIso p = cong ⟨_⟩ p , cong 0g p , cong _+_ p , cong -_ p , cong isGroup p
  Carrier (rightInv theIso a i i₁) = ⟨ a i₁ ⟩
  0g (rightInv theIso a i i₁) = 0g (a i₁)
  _+_ (rightInv theIso a i i₁) = _+_ (a i₁)
  - rightInv theIso a i i₁ = -_ (a i₁)
  isGroup (rightInv theIso a i i₁) = isGroup (a i₁)
  leftInv theIso _ = refl

caracGroup≡ : {G H : Group {ℓ}} (p q : G ≡ H) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
caracGroup≡ {G = G} {H = H} p q P = sym (transportTransport⁻ (ua (Group≡ G H)) p)
                                 ∙∙ cong (transport (ua (Group≡ G H))) helper
                                 ∙∙ transportTransport⁻ (ua (Group≡ G H)) q
  where
  helper : transport (sym (ua (Group≡ G H))) p ≡ transport (sym (ua (Group≡ G H))) q
  helper = Σ≡Prop
             (λ _ → isPropΣ
                       (isOfHLevelPathP' 1 (is-set H) _ _)
                       λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set H) _ _)
                       λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set H) _ _)
                       λ _ → isOfHLevelPathP 1 (isPropIsGroup _ _ _) _ _)
             (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

uaGroupId : (G : Group {ℓ}) → uaGroup (idGroupEquiv G) ≡ refl
uaGroupId G = caracGroup≡ _ _ (carac-uaGroup (idGroupEquiv G) ∙ uaIdEquiv)

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
