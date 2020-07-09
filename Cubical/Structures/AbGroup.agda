{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.AbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Macro
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Group hiding (⟨_⟩)

open Iso

private
  variable
    ℓ ℓ' : Level

record IsAbGroup {G : Type ℓ}
                 (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

  constructor isabgroup

  field
    isGroup : IsGroup 0g _+_ -_
    comm    : (x y : G) → x + y ≡ y + x

  open IsGroup isGroup public

record AbGroup : Type (ℓ-suc ℓ) where

  constructor abgroup

  field
    Carrier   : Type ℓ
    0g        : Carrier
    _+_       : Carrier → Carrier → Carrier
    -_        : Carrier → Carrier
    isAbGroup : IsAbGroup 0g _+_ -_

  infix  8 -_
  infixr 7 _+_

  open IsAbGroup isAbGroup public

-- Extractor for the carrier type
⟨_⟩ : AbGroup → Type ℓ
⟨_⟩ = AbGroup.Carrier

makeIsAbGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc   : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid     : (x : G) → x + 0g ≡ x)
              (rinv    : (x : G) → x + (- x) ≡ 0g)
              (comm    : (x y : G) → x + y ≡ y + x)
            → IsAbGroup 0g _+_ -_
makeIsAbGroup is-setG assoc rid rinv comm =
  isabgroup (makeIsGroup is-setG assoc rid (λ x → comm _ _ ∙ rid x) rinv (λ x → comm _ _ ∙ rinv x)) comm

makeAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (comm    : (x y : G) → x + y ≡ y + x)
          → AbGroup
makeAbGroup 0g _+_ -_ is-setG assoc rid rinv comm =
  abgroup _ 0g _+_ -_ (makeIsAbGroup is-setG assoc rid rinv comm)


AbGroup→Group : AbGroup {ℓ} → Group
AbGroup→Group (abgroup _ _ _ _ H) = group _ _ _ _ (IsAbGroup.isGroup H)

AbGroupHom : (G : AbGroup {ℓ}) (H : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
AbGroupHom G H = GroupHom (AbGroup→Group G) (AbGroup→Group H)

AbGroupEquiv : (G : AbGroup {ℓ}) (H : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
AbGroupEquiv G H = GroupEquiv (AbGroup→Group G) (AbGroup→Group H)

module AbGroupΣTheory {ℓ} where

  open GroupΣTheory

  AbGroupAxioms : (G : Type ℓ) → RawGroupStructure G → Type ℓ
  AbGroupAxioms G _+_ = GroupAxioms G _+_ × ((x y : G) → x + y ≡ y + x)

  AbGroupStructure : Type ℓ → Type ℓ
  AbGroupStructure = AxiomsStructure RawGroupStructure AbGroupAxioms

  AbGroupΣ : Type (ℓ-suc ℓ)
  AbGroupΣ = TypeWithStr ℓ AbGroupStructure

  AbGroupEquivStr : StrEquiv AbGroupStructure ℓ
  AbGroupEquivStr = AxiomsEquivStr RawGroupEquivStr AbGroupAxioms

  isPropAbGroupAxioms : (G : Type ℓ) (s : RawGroupStructure G)
                      → isProp (AbGroupAxioms G s)
  isPropAbGroupAxioms G _+_ =
    isPropΣ (isPropGroupAxioms G _+_)
            λ { (H , _) → isPropΠ2 λ _ _ → IsSemigroup.is-set H _ _}

  AbGroup→AbGroupΣ : AbGroup → AbGroupΣ
  AbGroup→AbGroupΣ (abgroup _ _ _ _ (isabgroup G C)) =
    _ , _ , Group→GroupΣ (group _ _ _ _ G) .snd .snd , C

  AbGroupΣ→AbGroup : AbGroupΣ → AbGroup
  AbGroupΣ→AbGroup (_ , _ , G , C) =
    abgroup _ _ _ _ (isabgroup (GroupΣ→Group (_ , _ , G) .Group.isGroup) C)

  AbGroupIsoAbGroupΣ : Iso AbGroup AbGroupΣ
  AbGroupIsoAbGroupΣ = iso AbGroup→AbGroupΣ AbGroupΣ→AbGroup helper helper2 -- iso AbGroup→AbGroupΣ AbGroupΣ→AbGroup (λ _ → ?)
    where
    helper : _
    fst (helper b i) = fst b
    snd (helper b i) = snd b

    helper2 : _
    AbGroup.Carrier (helper2 a i) = ⟨ a ⟩
    AbGroup.0g (helper2 a i) = AbGroup.0g a
    AbGroup._+_ (helper2 a i) = AbGroup._+_ a
    AbGroup.- helper2 a i = AbGroup.- a
    IsGroup.isMonoid (IsAbGroup.isGroup (AbGroup.isAbGroup (helper2 a i))) = η-isMonoid (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroup.isAbGroup a))) i
    IsGroup.inverse (IsAbGroup.isGroup (AbGroup.isAbGroup (helper2 a i))) = IsGroup.inverse (IsAbGroup.isGroup (AbGroup.isAbGroup a))
    IsAbGroup.comm (AbGroup.isAbGroup (helper2 a i)) = IsAbGroup.comm (AbGroup.isAbGroup a)

  abGroupUnivalentStr : UnivalentStr AbGroupStructure AbGroupEquivStr
  abGroupUnivalentStr = axiomsUnivalentStr _ isPropAbGroupAxioms rawGroupUnivalentStr

  AbGroupΣPath : (G H : AbGroupΣ) → (G ≃[ AbGroupEquivStr ] H) ≃ (G ≡ H)
  AbGroupΣPath = SIP abGroupUnivalentStr

  AbGroupEquivΣ : (G H : AbGroup) → Type ℓ
  AbGroupEquivΣ G H = AbGroup→AbGroupΣ G ≃[ AbGroupEquivStr ] AbGroup→AbGroupΣ H

  AbGroupPath : (G H : AbGroup) → (AbGroupEquiv G H) ≃ (G ≡ H)
  AbGroupPath G H =
    AbGroupEquiv G H                        ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    AbGroupEquivΣ G H                       ≃⟨ AbGroupΣPath _ _ ⟩
    AbGroup→AbGroupΣ G ≡ AbGroup→AbGroupΣ H ≃⟨ isoToEquiv (invIso (congIso AbGroupIsoAbGroupΣ)) ⟩
    G ≡ H ■

  AbGroup→RawGroupΣ : AbGroup {ℓ} → RawGroupΣ
  AbGroup→RawGroupΣ (abgroup G _ _+_ _ _) = G , _+_

  InducedAbGroup : (G : AbGroup) (H : RawGroupΣ) (e : G .AbGroup.Carrier ≃ H .fst)
                 → RawGroupEquivStr (AbGroup→RawGroupΣ G) H e → AbGroup
  InducedAbGroup G H e r =
    AbGroupΣ→AbGroup (transferAxioms rawGroupUnivalentStr (AbGroup→AbGroupΣ G) H (e , r))

  InducedAbGroupPath : (G : AbGroup {ℓ}) (H : RawGroupΣ) (e : G .AbGroup.Carrier ≃ H .fst)
                       (E : RawGroupEquivStr (AbGroup→RawGroupΣ G) H e)
                     → G ≡ InducedAbGroup G H e E
  InducedAbGroupPath G H e E =
    AbGroupPath G (InducedAbGroup G H e E) .fst (groupequiv e E)


-- Extract the characterization of equality of groups
AbGroupPath : (G H : AbGroup {ℓ}) → (AbGroupEquiv G H) ≃ (G ≡ H)
AbGroupPath = AbGroupΣTheory.AbGroupPath

isPropIsAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
                → isProp (IsAbGroup 0g _+_ -_)
isPropIsAbGroup 0g _+_ -_ (isabgroup GG GC) (isabgroup HG HC) =
  λ i → isabgroup (isPropIsGroup _ _ _ GG HG i) (isPropComm GC HC i)
  where
  isSetG : isSet _
  isSetG = GG .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x + y ≡ y + x)
  isPropComm = isPropΠ2 λ _ _ → isSetG _ _

InducedAbGroup : (G : AbGroup {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : G .AbGroup.Carrier ≃ H .fst)
               → GroupΣTheory.RawGroupEquivStr (AbGroupΣTheory.AbGroup→RawGroupΣ G) H e
               → AbGroup
InducedAbGroup = AbGroupΣTheory.InducedAbGroup

InducedAbGroupPath : (G : AbGroup {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : G .AbGroup.Carrier ≃ H .fst)
                     (E : GroupΣTheory.RawGroupEquivStr (AbGroupΣTheory.AbGroup→RawGroupΣ G) H e)
                   → G ≡ InducedAbGroup G H e E
InducedAbGroupPath = AbGroupΣTheory.InducedAbGroupPath
