{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Module where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

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

record LeftModuleIso {R : Ring {ℓ}} (M N : LeftModule R) : Type ℓ where

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

module LeftModuleΣ-theory (R : Ring {ℓ}) where

  open Macro ℓ (recvar (recvar var) , param ⟨ R ⟩r (recvar var)) public renaming
    ( structure to raw-leftModule-structure
    ; iso       to raw-leftModule-iso
    ; isSNS     to raw-leftModule-is-SNS )

  open Ring R using (_·_; 1r) renaming (_+_ to _+r_)

  leftModule-axioms : (M : Type ℓ) (s : raw-leftModule-structure M) → Type ℓ
  leftModule-axioms M (_+_ , _⋆_) = AbGroupΣ-theory.abgroup-axioms M _+_
                                    × ((r s : ⟨ R ⟩r) (x : M) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x))
                                    × ((r s : ⟨ R ⟩r) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                                    × ((r : ⟨ R ⟩r) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                                    × ((x : M) → 1r ⋆ x ≡ x)

  leftModule-structure : Type ℓ → Type ℓ
  leftModule-structure = add-to-structure raw-leftModule-structure leftModule-axioms

  LeftModuleΣ : Type (ℓ-suc ℓ)
  LeftModuleΣ = TypeWithStr ℓ leftModule-structure

  leftModule-iso : StrIso leftModule-structure ℓ
  leftModule-iso = add-to-iso raw-leftModule-iso leftModule-axioms

  open AbGroupΣ-theory using (isSetAbGroupΣ)

  isSetLeftModuleΣ : (M : LeftModuleΣ)  → isSet _
  isSetLeftModuleΣ (M , (_+_ , _) , (isAbGroup-M , _)) = isSetAbGroupΣ (M , _+_ , isAbGroup-M)

  isProp-leftModule-axioms : (M : Type ℓ) (s : raw-leftModule-structure M)
                             → isProp (leftModule-axioms M s)
  isProp-leftModule-axioms M (_+_ , _⋆_) =
     isPropΣ (AbGroupΣ-theory.isProp-abgroup-axioms M _+_)
             λ isAbGroup-M →
             isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
            (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
            (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
                     (isPropΠ  λ _     → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)))

  LeftModule→LeftModuleΣ : LeftModule R → LeftModuleΣ
  LeftModule→LeftModuleΣ
    (leftmodule M 0m _+_ -_ _⋆_ (ismodule +-isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)) =
    M , (_+_ , _⋆_) ,
    AbGroupΣ-theory.AbGroup→AbGroupΣ (abgroup _ _ _ _ +-isAbGroup) .snd .snd ,
    ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid

  LeftModuleΣ→LeftModule : LeftModuleΣ → LeftModule R
  LeftModuleΣ→LeftModule (M , (_+_ , _⋆_) , isAbGroup-M , ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid) =
    let isAbGroup = AbGroupΣ-theory.AbGroupΣ→AbGroup (_ , _ , isAbGroup-M ) .AbGroup.isAbGroup
    in leftmodule M _ _+_ _ _⋆_
       (ismodule isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)

  LeftModuleIsoLeftModuleΣ : Iso (LeftModule R) LeftModuleΣ
  LeftModuleIsoLeftModuleΣ = iso LeftModule→LeftModuleΣ LeftModuleΣ→LeftModule
                                 (λ _ → refl) (λ _ → refl)

  leftModule-is-SNS : SNS leftModule-structure leftModule-iso
  leftModule-is-SNS = add-axioms-SNS _ isProp-leftModule-axioms raw-leftModule-is-SNS

  LeftModuleΣPath : (M N : LeftModuleΣ) → (M ≃[ leftModule-iso ] N) ≃ (M ≡ N)
  LeftModuleΣPath = SIP leftModule-is-SNS

  LeftModuleIsoΣ : (M N : LeftModule R) → Type ℓ
  LeftModuleIsoΣ M N = LeftModule→LeftModuleΣ M ≃[ leftModule-iso ] LeftModule→LeftModuleΣ N

  LeftModuleIsoΣPath : {M N : LeftModule R} → Iso (LeftModuleIso M N) (LeftModuleIsoΣ M N)
  fun LeftModuleIsoΣPath (moduleiso e isHom+ comm⋆) = e , isHom+ , comm⋆
  inv LeftModuleIsoΣPath (e , isHom+ , comm⋆) = moduleiso e isHom+ comm⋆
  rightInv LeftModuleIsoΣPath _ = refl
  leftInv LeftModuleIsoΣPath _ = refl

  LeftModulePath : (M N : LeftModule R) → (LeftModuleIso M N) ≃ (M ≡ N)
  LeftModulePath M N =
    LeftModuleIso M N                                    ≃⟨ isoToEquiv LeftModuleIsoΣPath ⟩
    LeftModuleIsoΣ M N                                   ≃⟨ LeftModuleΣPath _ _ ⟩
    LeftModule→LeftModuleΣ M ≡ LeftModule→LeftModuleΣ N  ≃⟨ isoToEquiv
                                                             (invIso
                                                             (congIso
                                                             LeftModuleIsoLeftModuleΣ))
                                                           ⟩
    M ≡ N ■

LeftModulePath : {R : Ring {ℓ}} (M N : LeftModule R) → (LeftModuleIso M N) ≃ (M ≡ N)
LeftModulePath {ℓ} {R} = LeftModuleΣ-theory.LeftModulePath R
