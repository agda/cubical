-- The category Grp of groups
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Categories.Category.Base renaming (isIso to isCatIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor.Base

open import Cubical.Data.Sigma

module _ {ℓ : Level} where
  open Category hiding (_∘_)

  GroupCategory : Category (ℓ-suc ℓ) ℓ
  GroupCategory .ob = Group ℓ
  GroupCategory .Hom[_,_] = GroupHom
  GroupCategory .id = idGroupHom
  GroupCategory ._⋆_ = compGroupHom
  GroupCategory .⋆IdL f = GroupHom≡ refl
  GroupCategory .⋆IdR f = GroupHom≡ refl
  GroupCategory .⋆Assoc f g h = GroupHom≡ refl
  GroupCategory .isSetHom = isSetGroupHom

  Forget : Functor GroupCategory (SET ℓ)
  Functor.F-ob Forget G = fst G , GroupStr.is-set (snd G)
  Functor.F-hom Forget = fst
  Functor.F-id Forget = refl
  Functor.F-seq Forget _ _ = refl

  GroupsCatIso≃GroupEquiv : ∀ G G' →
    CatIso GroupCategory G G' ≃
     GroupEquiv G G'
  GroupsCatIso≃GroupEquiv G G' =
      Σ-cong-equiv-snd
        (λ _ → propBiimpl→Equiv
          (isPropIsIso _) (isPropIsEquiv _)
           (isoToIsEquiv ∘ →iso) →ciso)
       ∙ₑ Σ-assoc-swap-≃
   where
    open Iso
    open isCatIso
    →iso : ∀ {x} → isCatIso GroupCategory x → Iso _ _
    fun (→iso ici) = _
    inv (→iso ici) = fst (inv ici)
    rightInv (→iso ici) b i = fst (sec ici i) b
    leftInv (→iso ici) a i = fst (ret ici i) a

    →ciso : ∀ {x} → isEquiv (fst x) → isCatIso GroupCategory x
    fst (inv (→ciso is≃)) = _
    snd (inv (→ciso {x} is≃)) =
      isGroupHomInv ((_ , is≃) , (snd x))
    sec (→ciso is≃) =
     Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (secEq (_ , is≃)))
    ret (→ciso is≃) =
     Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (retEq (_ , is≃)))


  isUnivalentGrp : isUnivalent {ℓ' = ℓ} GroupCategory
  isUnivalent.univ isUnivalentGrp _ _ =
   precomposesToId→Equiv _ _ (funExt
               (Σ≡Prop isPropIsIso
              ∘ Σ≡Prop (λ _ → isPropIsGroupHom _ _)
              ∘ λ _ → transportRefl _))
              (snd (GroupsCatIso≃GroupEquiv _ _ ∙ₑ GroupPath _ _))
