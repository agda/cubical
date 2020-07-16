{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Structures.Module where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Structures.Ring      renaming (⟨_⟩ to ⟨_⟩r)
open import Cubical.Structures.AbGroup   hiding (⟨_⟩)
open import Cubical.Structures.Group     hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsLeftModule (R : Ring {ℓ}) {M : Type ℓ}
              (0m : M)
              (_+_ : M → M → M)
              (-_ : M → M)
              (_⋆_ : ⟨ R ⟩r → M → M) : Type ℓ where

  constructor ismodule

  open Ring R using (_·_; 1r) renaming (_+_ to _+r_)

  field
    +-isAbGroup : IsAbGroup 0m _+_ -_
    ⋆-assoc : (r s : ⟨ R ⟩r) (x : M) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x)
    ⋆-ldist : (r s : ⟨ R ⟩r) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
    ⋆-rdist : (r : ⟨ R ⟩r) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
    ⋆-lid   : (x : M) → 1r ⋆ x ≡ x

  open IsAbGroup +-isAbGroup public
    renaming
    ( assoc       to +-assoc
    ; identity    to +-identity
    ; lid         to +-lid
    ; rid         to +-rid
    ; inverse     to +-inv
    ; invl        to +-linv
    ; invr        to +-rinv
    ; comm        to +-comm
    ; isSemigroup to +-isSemigroup
    ; isMonoid    to +-isMonoid
    ; isGroup     to +-isGroup
    )

record LeftModule (R : Ring {ℓ}) : Type (ℓ-suc ℓ) where

  constructor leftmodule

  field
    Carrier        : Type ℓ
    0m             : Carrier
    _+_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩r → Carrier → Carrier
    isLeftModule   : IsLeftModule R 0m _+_ -_ _⋆_

  open IsLeftModule isLeftModule public

module _ {R : Ring {ℓ}} where
  ⟨_⟩ : LeftModule R → Type ℓ
  ⟨_⟩ = LeftModule.Carrier

  LeftModule→AbGroup : (M : LeftModule R) → AbGroup {ℓ}
  LeftModule→AbGroup (leftmodule _ _ _ _ _ isLeftModule) =
                     abgroup _ _ _ _ (IsLeftModule.+-isAbGroup isLeftModule)

  isSetLeftModule : (M : LeftModule R) → isSet ⟨ M ⟩
  isSetLeftModule M = isSetAbGroup (LeftModule→AbGroup M)

  open Ring R using (1r) renaming (_+_ to _+r_; _·_ to _·s_)

  makeIsLeftModule : {M : Type ℓ} {0m : M}
                  {_+_ : M → M → M} { -_ : M → M} {_⋆_ : ⟨ R ⟩r → M → M}
                  (isSet-M : isSet M)
                  (+-assoc :  (x y z : M) → x + (y + z) ≡ (x + y) + z)
                  (+-rid : (x : M) → x + 0m ≡ x)
                  (+-rinv : (x : M) → x + (- x) ≡ 0m)
                  (+-comm : (x y : M) → x + y ≡ y + x)
                  (⋆-assoc : (r s : ⟨ R ⟩r) (x : M) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                  (⋆-ldist : (r s : ⟨ R ⟩r) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                  (⋆-rdist : (r : ⟨ R ⟩r) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                  (⋆-lid   : (x : M) → 1r ⋆ x ≡ x)
                → IsLeftModule R 0m _+_ -_ _⋆_
  makeIsLeftModule isSet-M
                +-assoc +-rid +-rinv +-comm
                ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid =
                ismodule (makeIsAbGroup isSet-M +-assoc +-rid +-rinv +-comm)
                         ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid

record LeftModuleEquiv {R : Ring {ℓ}} (M N : LeftModule R) : Type ℓ where

  constructor moduleiso

  instance
    _ : LeftModule R
    _ = M
    _ : LeftModule R
    _ = N

  open LeftModule {{...}}

  field
    e : ⟨ M ⟩ ≃ ⟨ N ⟩
    isHom+ : (x y : ⟨ M ⟩) → equivFun e (x + y) ≡ equivFun e x + equivFun e y
    comm⋆ : (r : ⟨ R ⟩r) (x : ⟨ M ⟩) → equivFun e (r ⋆ x) ≡ r ⋆ equivFun e x

module LeftModuleΣTheory (R : Ring {ℓ}) where

  RawLeftModuleStructure = λ (M : Type ℓ) → (M → M → M) × (⟨ R ⟩r → M → M)

  RawLeftModuleEquivStr = AutoEquivStr RawLeftModuleStructure

  RawLeftModuleUnivalentStr : UnivalentStr _ RawLeftModuleEquivStr
  RawLeftModuleUnivalentStr = autoUnivalentStr RawLeftModuleStructure

  open Ring R using (_·_; 1r) renaming (_+_ to _+r_)

  LeftModuleAxioms : (M : Type ℓ) (s : RawLeftModuleStructure M) → Type ℓ
  LeftModuleAxioms M (_+_ , _⋆_) = AbGroupΣTheory.AbGroupAxioms M _+_
                                    × ((r s : ⟨ R ⟩r) (x : M) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x))
                                    × ((r s : ⟨ R ⟩r) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                                    × ((r : ⟨ R ⟩r) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                                    × ((x : M) → 1r ⋆ x ≡ x)

  LeftModuleStructure : Type ℓ → Type ℓ
  LeftModuleStructure = AxiomsStructure RawLeftModuleStructure LeftModuleAxioms

  LeftModuleΣ : Type (ℓ-suc ℓ)
  LeftModuleΣ = TypeWithStr ℓ LeftModuleStructure

  LeftModuleEquivStr : StrEquiv LeftModuleStructure ℓ
  LeftModuleEquivStr = AxiomsEquivStr RawLeftModuleEquivStr LeftModuleAxioms

  open AbGroupΣTheory using (isSetAbGroupΣ)

  isSetLeftModuleΣ : (M : LeftModuleΣ)  → isSet _
  isSetLeftModuleΣ (M , (_+_ , _) , (isAbGroup-M , _)) = isSetAbGroupΣ (M , _+_ , isAbGroup-M)

  isPropLeftModuleAxioms : (M : Type ℓ) (s : RawLeftModuleStructure M)
                             → isProp (LeftModuleAxioms M s)
  isPropLeftModuleAxioms M (_+_ , _⋆_) =
     isPropΣ (AbGroupΣTheory.isPropAbGroupAxioms M _+_)
             λ isAbGroup-M →
             isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
            (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
            (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
                     (isPropΠ  λ _     → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)))

  LeftModule→LeftModuleΣ : LeftModule R → LeftModuleΣ
  LeftModule→LeftModuleΣ
    (leftmodule M 0m _+_ -_ _⋆_ (ismodule +-isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)) =
    M , (_+_ , _⋆_) ,
    AbGroupΣTheory.AbGroup→AbGroupΣ (abgroup _ _ _ _ +-isAbGroup) .snd .snd ,
    ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid

  LeftModuleΣ→LeftModule : LeftModuleΣ → LeftModule R
  LeftModuleΣ→LeftModule (M , (_+_ , _⋆_) , isAbGroup-M , ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid) =
    let isAbGroup = AbGroupΣTheory.AbGroupΣ→AbGroup (_ , _ , isAbGroup-M ) .AbGroup.isAbGroup
    in leftmodule M _ _+_ _ _⋆_
       (ismodule isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)

  LeftModuleEquivStrLeftModuleΣ : Iso (LeftModule R) LeftModuleΣ
  LeftModuleEquivStrLeftModuleΣ = iso LeftModule→LeftModuleΣ LeftModuleΣ→LeftModule
                                 (λ _ → refl) (λ _ → refl)


  leftModuleUnivalentStr : UnivalentStr LeftModuleStructure LeftModuleEquivStr
  leftModuleUnivalentStr = axiomsUnivalentStr _ isPropLeftModuleAxioms RawLeftModuleUnivalentStr

  LeftModuleΣPath : (M N : LeftModuleΣ) → (M ≃[ LeftModuleEquivStr ] N) ≃ (M ≡ N)
  LeftModuleΣPath = SIP leftModuleUnivalentStr

  LeftModuleEquivStrΣ : (M N : LeftModule R) → Type ℓ
  LeftModuleEquivStrΣ M N = LeftModule→LeftModuleΣ M ≃[ LeftModuleEquivStr ] LeftModule→LeftModuleΣ N

  LeftModuleEquivStrΣPath : {M N : LeftModule R} → Iso (LeftModuleEquiv M N) (LeftModuleEquivStrΣ M N)
  fun LeftModuleEquivStrΣPath (moduleiso e isHom+ comm⋆) = e , isHom+ , comm⋆
  inv LeftModuleEquivStrΣPath (e , isHom+ , comm⋆) = moduleiso e isHom+ comm⋆
  rightInv LeftModuleEquivStrΣPath _ = refl
  leftInv LeftModuleEquivStrΣPath _ = refl

  LeftModulePath : (M N : LeftModule R) → (LeftModuleEquiv M N) ≃ (M ≡ N)
  LeftModulePath M N =
    LeftModuleEquiv M N                                    ≃⟨ isoToEquiv LeftModuleEquivStrΣPath ⟩
    LeftModuleEquivStrΣ M N                                   ≃⟨ LeftModuleΣPath _ _ ⟩
    LeftModule→LeftModuleΣ M ≡ LeftModule→LeftModuleΣ N  ≃⟨ isoToEquiv
                                                             (invIso
                                                             (congIso
                                                             LeftModuleEquivStrLeftModuleΣ))
                                                           ⟩
    M ≡ N ■

LeftModulePath : {R : Ring {ℓ}} (M N : LeftModule R) → (LeftModuleEquiv M N) ≃ (M ≡ N)
LeftModulePath {ℓ} {R} = LeftModuleΣTheory.LeftModulePath R

