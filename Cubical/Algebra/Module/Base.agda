{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group

open Iso

private
  variable
    ℓ ℓ' : Level

record IsLeftModule (R : Ring ℓ) {M : Type ℓ'}
  (0m : M)
  (_+_ : M → M → M)
  (-_ : M → M)
  (_⋆_ : ⟨ R ⟩ → M → M) : Type (ℓ-max ℓ ℓ') where

  constructor ismodule

  open RingStr (snd R) using (_·_; 1r) renaming (_+_ to _+r_)

  field
    +-isAbGroup : IsAbGroup 0m _+_ -_
    ⋆-assoc : (r s : ⟨ R ⟩) (x : M) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x)
    ⋆-ldist : (r s : ⟨ R ⟩) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
    ⋆-rdist : (r : ⟨ R ⟩) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
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

unquoteDecl IsLeftModuleIsoΣ = declareRecordIsoΣ IsLeftModuleIsoΣ (quote IsLeftModule)

record LeftModuleStr (R : Ring ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor leftmodulestr

  field
    0m             : A
    _+_            : A → A → A
    -_             : A → A
    _⋆_            : ⟨ R ⟩ → A → A
    isLeftModule   : IsLeftModule R 0m _+_ -_ _⋆_

  open IsLeftModule isLeftModule public

LeftModule : (R : Ring ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
LeftModule R ℓ' = Σ[ A ∈ Type ℓ' ] LeftModuleStr R A

module _ {R : Ring ℓ} where

  LeftModule→AbGroup : (M : LeftModule R ℓ') → AbGroup ℓ'
  LeftModule→AbGroup (_ , leftmodulestr _ _ _ _ isLeftModule) =
                     _ , abgroupstr _ _ _ (IsLeftModule.+-isAbGroup isLeftModule)

  isSetLeftModule : (M : LeftModule R ℓ') → isSet ⟨ M ⟩
  isSetLeftModule M = isSetAbGroup (LeftModule→AbGroup M)

  open RingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·s_)

  makeIsLeftModule : {M : Type ℓ'} {0m : M}
                  {_+_ : M → M → M} { -_ : M → M} {_⋆_ : ⟨ R ⟩ → M → M}
                  (isSet-M : isSet M)
                  (+-assoc :  (x y z : M) → x + (y + z) ≡ (x + y) + z)
                  (+-rid : (x : M) → x + 0m ≡ x)
                  (+-rinv : (x : M) → x + (- x) ≡ 0m)
                  (+-comm : (x y : M) → x + y ≡ y + x)
                  (⋆-assoc : (r s : ⟨ R ⟩) (x : M) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                  (⋆-ldist : (r s : ⟨ R ⟩) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                  (⋆-rdist : (r : ⟨ R ⟩) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                  (⋆-lid   : (x : M) → 1r ⋆ x ≡ x)
                → IsLeftModule R 0m _+_ -_ _⋆_
  makeIsLeftModule isSet-M +-assoc +-rid +-rinv +-comm ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid =
    ismodule (makeIsAbGroup isSet-M +-assoc +-rid +-rinv +-comm) ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid

record IsLeftModuleHom {R : Ring ℓ} {A B : Type ℓ'}
  (M : LeftModuleStr R A) (f : A → B) (N : LeftModuleStr R B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module M = LeftModuleStr M
    module N = LeftModuleStr N

  field
    pres0 : f M.0m ≡ N.0m
    pres+ : (x y : A) → f (x M.+ y) ≡ f x N.+ f y
    pres- : (x : A) → f (M.- x) ≡ N.- (f x)
    pres⋆ : (r : ⟨ R ⟩) (y : A) → f (r M.⋆ y) ≡ r N.⋆ f y

LeftModuleHom : {R : Ring ℓ} (M N : LeftModule R ℓ') → Type (ℓ-max ℓ ℓ')
LeftModuleHom M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsLeftModuleHom (M .snd) f (N .snd)

IsLeftModuleEquiv : {R : Ring ℓ} {A B : Type ℓ'}
  (M : LeftModuleStr R A) (e : A ≃ B) (N : LeftModuleStr R B)
  → Type (ℓ-max ℓ ℓ')
IsLeftModuleEquiv M e N = IsLeftModuleHom M (e .fst) N

LeftModuleEquiv : {R : Ring ℓ} (M N : LeftModule R ℓ') → Type (ℓ-max ℓ ℓ')
LeftModuleEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsLeftModuleEquiv (M .snd) e (N .snd)

isPropIsLeftModule : (R : Ring ℓ) {M : Type ℓ'}
  (0m : M)
  (_+_ : M → M → M)
  (-_ : M → M)
  (_⋆_ : ⟨ R ⟩ → M → M)
  → isProp (IsLeftModule R 0m _+_ -_ _⋆_)
isPropIsLeftModule R _ _ _ _ =
  isOfHLevelRetractFromIso 1 IsLeftModuleIsoΣ
    (isPropΣ (isPropIsAbGroup _ _ _)
      (λ ab →
        isProp× (isPropΠ3 λ _ _ _ → ab .is-set _ _)
          (isProp× (isPropΠ3 λ _ _ _ → ab .is-set _ _)
            (isProp× (isPropΠ3 λ _ _ _ → ab .is-set _ _)
              (isPropΠ λ _ → ab .is-set _ _)))))
  where
  open IsAbGroup

𝒮ᴰ-LeftModule : (R : Ring ℓ) → DUARel (𝒮-Univ ℓ') (LeftModuleStr R) (ℓ-max ℓ ℓ')
𝒮ᴰ-LeftModule R =
  𝒮ᴰ-Record (𝒮-Univ _) (IsLeftModuleEquiv {R = R})
    (fields:
      data[ 0m ∣ autoDUARel _ _ ∣ pres0 ]
      data[ _+_ ∣ autoDUARel _ _ ∣ pres+ ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isLeftModule ∣ (λ _ _ → isPropIsLeftModule _ _ _ _ _) ])
  where
  open LeftModuleStr
  open IsLeftModuleHom

LeftModulePath : {R : Ring ℓ} (M N : LeftModule R ℓ') → (LeftModuleEquiv M N) ≃ (M ≡ N)
LeftModulePath {R = R} = ∫ (𝒮ᴰ-LeftModule R) .UARel.ua

