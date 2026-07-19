{-# OPTIONS --cubical #-}

-- The posetal reflection is the universal way to turn a preorder into a poset
-- In abstract-nonsense terms, the posetal reflection exhibits Pos as a reflective subcategory of preorders.
-- https://ncatlab.org/nlab/show/posetal+reflection
-- When a preorder is viewed as a category, posets are univalent categories
-- and the posetal reflection is a special case of the Rezk completion.

module Cubical.Relation.Binary.Order.Poset.Instances.PosetalReflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic
open import Cubical.Functions.Embedding
open import Cubical.HITs.SetQuotients as SetQuot using (_/_; [_]; eq/; squash/)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties
open import Cubical.Relation.Binary.Order.Proset

private variable
  ℓ ℓ' ℓ'' : Level

module _ (P : Proset ℓ ℓ') where
  open module P = ProsetStr (P .snd) using (_≲_)
  open ProsetReasoning P renaming (_◾ to _≲∎)
  open BinaryRelation

  private variable
    a b c : ⟨ P ⟩

  _~_ : Rel ⟨ P ⟩ ⟨ P ⟩ ℓ'
  _~_ = SymKernel _≲_

  isEquivRel~ : isEquivRel _~_
  isEquivRel~ = isProset→isEquivRelSymKernel P.isProset

  Reflection : Type (ℓ-max ℓ ℓ')
  Reflection = ⟨ P ⟩ / _~_

  _≤'_ : Reflection → Reflection → hProp ℓ'
  _≤'_ = SetQuot.rec2 isSetHProp (λ a b → a ≲ b , P.is-prop-valued a b)
    (λ a b c (a≲b , b≲a) → ⇔toPath (λ a≲c → b ≲⟨ b≲a ⟩ a ≲⟨ a≲c ⟩ c ≲∎) (λ b≲c → a ≲⟨ a≲b ⟩ b ≲⟨ b≲c ⟩ c ≲∎))
    (λ a b c (b≲c , c≲b) → ⇔toPath (λ a≲b → a ≲⟨ a≲b ⟩ b ≲⟨ b≲c ⟩ c ≲∎) (λ a≲c → a ≲⟨ a≲c ⟩ c ≲⟨ c≲b ⟩ b ≲∎))

  _≤_ : Reflection → Reflection → Type ℓ'
  a ≤ b = ⟨ a ≤' b ⟩

  isPropValued≤ : isPropValued _≤_
  isPropValued≤ a b = snd (a ≤' b)

  isRefl≤ : isRefl _≤_
  isRefl≤ = SetQuot.elimProp (λ a → isPropValued≤ a a) P.is-refl

  isTrans≤ : isTrans _≤_
  isTrans≤ = SetQuot.elimProp3 (λ a b c → isPropΠ2 λ _ _ → isPropValued≤ a c) P.is-trans

  isAntisym≤ : isAntisym _≤_
  isAntisym≤ = SetQuot.elimProp2 (λ a b → isPropΠ2 λ _ _ → squash/ a b) λ a b a≲b b≲a → eq/ a b (a≲b , b≲a)

  isPoset≤ : IsPoset _≤_
  isPoset≤ .IsPoset.is-set = squash/
  isPoset≤ .IsPoset.is-prop-valued = isPropValued≤
  isPoset≤ .IsPoset.is-refl = isRefl≤
  isPoset≤ .IsPoset.is-trans = isTrans≤
  isPoset≤ .IsPoset.is-antisym = isAntisym≤

  ReflectionPoset : Poset (ℓ-max ℓ ℓ') ℓ'
  ReflectionPoset = Reflection , posetstr _≤_ isPoset≤

  isProset≤ : IsProset _≤_
  isProset≤ = isPoset→isProset isPoset≤

  private
    idEmb : {A : Type ℓ''} → Embedding A ℓ''
    idEmb = _ , id↪ _

  -- if a preorder is bounded, then so is its posetal reflection

  []presLeast : ∀ least → isLeast P.isProset idEmb least → isLeast isProset≤ idEmb [ least ]
  []presLeast least is-least = SetQuot.elimProp (λ x → isPropValued≤ [ least ] x) is-least

  hasLeast : Least P.isProset idEmb → Least isProset≤ idEmb
  hasLeast least = [ least .fst ] , []presLeast (least .fst) (least .snd)

  []presGreatest : ∀ greatest → isGreatest P.isProset idEmb greatest → isGreatest isProset≤ idEmb [ greatest ]
  []presGreatest greatest is-greatest = SetQuot.elimProp (λ x → isPropValued≤ x [ greatest ]) is-greatest

  hasGreatest : Greatest P.isProset idEmb → Greatest isProset≤ idEmb
  hasGreatest greatest = [ greatest .fst ] , []presGreatest (greatest .fst) (greatest .snd)

  -- if a preorder has binary meets, then so does its posetal reflection

  []presMeets : ∀ meet → isMeet P.isProset a b meet → isMeet isProset≤ [ a ] [ b ] [ meet ]
  []presMeets meet is-meet = SetQuot.elimProp (λ x → isOfHLevel⁺≃ₗ 0 (isPropValued≤ x [ meet ])) is-meet

  []presHasMeet : Meet P.isProset a b → Meet isProset≤ [ a ] [ b ]
  []presHasMeet meet = [ meet .fst ] , []presMeets (meet .fst) (meet .snd)

  hasBinMeets : (∀ a b → Meet P.isProset a b) → isMeetSemipseudolattice ReflectionPoset
  hasBinMeets bin-meets = SetQuot.elimProp2 (MeetUnique isPoset≤) λ a b → []presHasMeet (bin-meets a b)

  -- if a preorder has binary joins, then so does its posetal reflection

  []presJoins : ∀ join → isJoin P.isProset a b join → isJoin isProset≤ [ a ] [ b ] [ join ]
  []presJoins join is-join = SetQuot.elimProp (λ x → isOfHLevel⁺≃ₗ 0 (isPropValued≤ [ join ] x)) is-join

  []presHasJoin : Join P.isProset a b → Join isProset≤ [ a ] [ b ]
  []presHasJoin join = [ join .fst ] , []presJoins (join .fst) (join .snd)

  hasBinJoins : (∀ a b → Join P.isProset a b) → isJoinSemipseudolattice ReflectionPoset
  hasBinJoins bin-joins = SetQuot.elimProp2 (JoinUnique isPoset≤) λ a b → []presHasJoin (bin-joins a b)

