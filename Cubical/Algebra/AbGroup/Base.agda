{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.AbGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Reflection.StrictEquiv
open import Cubical.Structures.Axioms
open import Cubical.Structures.Macro
open import Cubical.Structures.Pointed
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group

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

record AbGroupStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor abgroupstr

  field
    0g        : A
    _+_       : A → A → A
    -_        : A → A
    isAbGroup : IsAbGroup 0g _+_ -_

  infix  8 -_
  infixr 7 _+_

  open IsAbGroup isAbGroup public

AbGroup : Type (ℓ-suc ℓ)
AbGroup = TypeWithStr _ AbGroupStr

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
  _ , abgroupstr 0g _+_ -_ (makeIsAbGroup is-setG assoc rid rinv comm)

open GroupStr
AbGroup→Group : AbGroup {ℓ} → Group
fst (AbGroup→Group A) = fst A
0g (snd (AbGroup→Group A)) = AbGroupStr.0g (snd A)
_+_ (snd (AbGroup→Group A)) = AbGroupStr._+_ (snd A)
- snd (AbGroup→Group A) = AbGroupStr.- (snd A)
isGroup (snd (AbGroup→Group A)) = IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd A))

Group→AbGroup : (G : Group {ℓ}) → ((x y : fst G) → _+_ (snd G) x y ≡ _+_ (snd G) y x) → AbGroup
fst (Group→AbGroup G comm) = fst G
AbGroupStr.0g (snd (Group→AbGroup G comm)) = 0g (snd G)
AbGroupStr._+_ (snd (Group→AbGroup G comm)) = _+_ (snd G)
AbGroupStr.- snd (Group→AbGroup G comm) = - (snd G)
IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd (Group→AbGroup G comm))) = isGroup (snd G)
IsAbGroup.comm (AbGroupStr.isAbGroup (snd (Group→AbGroup G comm))) = comm

isSetAbGroup : (A : AbGroup {ℓ}) → isSet ⟨ A ⟩
isSetAbGroup A = isSetGroup (AbGroup→Group A)

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

  isSetAbGroupΣ : (A : AbGroupΣ) → isSet _
  isSetAbGroupΣ (A , _+_ , (isGroup-A , _)) = isSetGroupΣ (A , _+_ , isGroup-A)

  AbGroupEquivStr : StrEquiv AbGroupStructure ℓ
  AbGroupEquivStr = AxiomsEquivStr RawGroupEquivStr AbGroupAxioms

  isPropAbGroupAxioms : (G : Type ℓ) (s : RawGroupStructure G)
                      → isProp (AbGroupAxioms G s)
  isPropAbGroupAxioms G _+_ =
    isPropΣ (isPropGroupAxioms G _+_)
            λ { (H , _) → isPropΠ2 λ _ _ → IsSemigroup.is-set H _ _}

  AbGroup→AbGroupΣ : AbGroup → AbGroupΣ
  AbGroup→AbGroupΣ (_ , abgroupstr _ _ _ (isabgroup G C)) =
    _ , _ , Group→GroupΣ (group _ _ _ _ G) .snd .snd , C

  AbGroupΣ→AbGroup : AbGroupΣ → AbGroup
  AbGroupΣ→AbGroup (_ , _ , G , C) =
    _ , abgroupstr _ _ _ (isabgroup (GroupΣ→Group (_ , _ , G) .snd .GroupStr.isGroup) C)

  open AbGroupStr

  AbGroupIsoAbGroupΣ : Iso AbGroup AbGroupΣ
  AbGroupIsoAbGroupΣ = iso AbGroup→AbGroupΣ AbGroupΣ→AbGroup (λ _ → refl) (λ _ → refl)

  abGroupUnivalentStr : UnivalentStr AbGroupStructure AbGroupEquivStr
  abGroupUnivalentStr = axiomsUnivalentStr _ isPropAbGroupAxioms rawGroupUnivalentStr

  AbGroupΣPath : (G H : AbGroupΣ) → (G ≃[ AbGroupEquivStr ] H) ≃ (G ≡ H)
  AbGroupΣPath = SIP abGroupUnivalentStr

  AbGroupEquivΣ : (G H : AbGroup) → Type ℓ
  AbGroupEquivΣ G H = AbGroup→AbGroupΣ G ≃[ AbGroupEquivStr ] AbGroup→AbGroupΣ H

  AbGroupPath : (G H : AbGroup) → (AbGroupEquiv G H) ≃ (G ≡ H)
  AbGroupPath G H =
    AbGroupEquiv G H                        ≃⟨ strictIsoToEquiv GroupIsoΣPath ⟩
    AbGroupEquivΣ G H                       ≃⟨ AbGroupΣPath _ _ ⟩
    AbGroup→AbGroupΣ G ≡ AbGroup→AbGroupΣ H ≃⟨ isoToEquiv (invIso (congIso AbGroupIsoAbGroupΣ)) ⟩
    G ≡ H ■

  AbGroup→RawGroupΣ : AbGroup {ℓ} → RawGroupΣ
  AbGroup→RawGroupΣ (G , abgroupstr _ _+_ _ _) = G , _+_

  InducedAbGroup : (G : AbGroup) (H : RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
                 → RawGroupEquivStr (AbGroup→RawGroupΣ G) H e → AbGroup
  InducedAbGroup G H e r =
    AbGroupΣ→AbGroup (inducedStructure rawGroupUnivalentStr (AbGroup→AbGroupΣ G) H (e , r))

  InducedAbGroupPath : (G : AbGroup {ℓ}) (H : RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
                       (E : RawGroupEquivStr (AbGroup→RawGroupΣ G) H e)
                     → G ≡ InducedAbGroup G H e E
  InducedAbGroupPath G H e E =
    AbGroupPath G (InducedAbGroup G H e E) .fst (groupequiv e E)


-- Extract the characterization of equality of groups
AbGroupPath : (G H : AbGroup {ℓ}) → (AbGroupEquiv G H) ≃ (G ≡ H)
AbGroupPath = AbGroupΣTheory.AbGroupPath

isPropIsAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (- : G → G)
                → isProp (IsAbGroup 0g _+_ -)
isPropIsAbGroup 0g _+_ -_ (isabgroup GG GC) (isabgroup HG HC) =
  λ i → isabgroup (isPropIsGroup _ _ _ GG HG i) (isPropComm GC HC i)
  where
  isSetG : isSet _
  isSetG = GG .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x + y ≡ y + x)
  isPropComm = isPropΠ2 λ _ _ → isSetG _ _

InducedAbGroup : (G : AbGroup {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
               → GroupΣTheory.RawGroupEquivStr (AbGroupΣTheory.AbGroup→RawGroupΣ G) H e
               → AbGroup
InducedAbGroup = AbGroupΣTheory.InducedAbGroup

InducedAbGroupPath : (G : AbGroup {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
                     (E : GroupΣTheory.RawGroupEquivStr (AbGroupΣTheory.AbGroup→RawGroupΣ G) H e)
                   → G ≡ InducedAbGroup G H e E
InducedAbGroupPath = AbGroupΣTheory.InducedAbGroupPath

open IsMonoid
open IsSemigroup
open IsGroup
open AbGroupStr
open IsAbGroup

dirProdAb : AbGroup {ℓ} → AbGroup {ℓ'} → AbGroup
dirProdAb A B =
  Group→AbGroup (dirProd (AbGroup→Group A) (AbGroup→Group B))
                 λ p q → ΣPathP (comm (isAbGroup (snd A)) _ _
                                , comm (isAbGroup (snd B)) _ _)

trivialAbGroup : ∀ {ℓ} → AbGroup {ℓ}
fst trivialAbGroup = Unit*
0g (snd trivialAbGroup) = tt*
_+_ (snd trivialAbGroup) _ _ = tt*
(- snd trivialAbGroup) _ = tt*
is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd trivialAbGroup))))) =
  isProp→isSet isPropUnit*
assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd trivialAbGroup))))) _ _ _ = refl
identity (isMonoid (isGroup (isAbGroup (snd trivialAbGroup)))) _ = refl , refl
inverse (isGroup (isAbGroup (snd trivialAbGroup))) _ = refl , refl
comm (isAbGroup (snd trivialAbGroup)) _ _ = refl
