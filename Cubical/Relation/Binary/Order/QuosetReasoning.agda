-- Example of usage:
--
--    open <-syntax
--    open ≤-syntax
--    open ≡-syntax
--
--    example : ∀ (x y z u v w α γ δ : P)
--            → x < y
--            → y ≤ z
--            → z ≡ u
--            → u < v
--            → v ≤ w
--            → w ≡ α
--            → α ≡ γ
--            → γ ≡ δ
--            → x < δ
--    example x y z u v w α γ δ x<y y≤z z≡u u<v v≤w w≡α α≡γ γ≡δ = begin
--      x   <⟨   x<y      ⟩
--      y   ≤⟨   y≤z      ⟩
--      z   ≡→≤⟨ z ≡⟨ z≡u        ⟩
--               u ≡⟨ sym z≡u    ⟩
--               z ≡[ i ]⟨ z≡u i ⟩
--               u ∎     ⟩
--      u   <⟨   u<v      ⟩
--      v   ≤⟨   v≤w      ⟩
--      w   ≡→≤⟨
--              w   ≡⟨ w≡α ⟩
--              α   ≡⟨ α≡γ ⟩
--              γ   ≡[ i ]⟨ γ≡δ i ⟩
--              δ   ∎
--            ⟩
--      δ ◾

{-# OPTIONS --safe #-}
{-
  Equational reasoning in a Quoset that is also a Poset, i.e.
  for writing a chain of <,≤,≡ with at least a <
-}
module Cubical.Relation.Binary.Order.QuosetReasoning where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty.Base as ⊥

open import Cubical.Relation.Nullary.Base

open import Cubical.Relation.Binary.Base
open BinaryRelation
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base

private
  variable
    ℓ ℓ≤ ℓ< : Level

-- Record with all the parts needed to extract a subrelation from a relation
-- (e.g. from a chain of <,≤,=, with at least a <, to a <)
-- Note:
-- It could be better to move this record in Relation.Binary.Base,
-- but there isn't yet a proper module for subrelations.
record SubRelation
  {ℓR}
  {P : Type ℓ}
  (_R_ : Rel P P ℓR ) ℓS ℓIsS : Type (ℓ-max ℓ (ℓ-max ℓR (ℓ-max (ℓ-suc ℓS) (ℓ-suc ℓIsS)))) where
    no-eta-equality
    field
      _S_ : Rel P P ℓS
      IsS : ∀ {x y} → x R y → Type ℓIsS
      IsS? : ∀ {x y} → (xRy : x R y) → Dec (IsS xRy)
      extract : ∀ {x y} → {xRy : x R y} → IsS xRy → x S y

module <-≤-Reasoning
  (P : Type ℓ)
  ((posetstr (_≤_) isPoset)   : PosetStr ℓ≤ P)
  ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
  (<-≤-trans : ∀ x {y z} → x < y → y ≤ z → x < z)
  (≤-<-trans : ∀ x {y z} → x ≤ y → y < z → x < z) where

  open IsPoset
  open IsQuoset
  open SubRelation

  private
    variable
      x y z : P
    data _<≤≡_ : P → P → Type (ℓ-max ℓ (ℓ-max ℓ< ℓ≤)) where
      strict    : x < y → x <≤≡ y
      nonstrict : x ≤ y → x <≤≡ y
      equal     : x ≡ y → x <≤≡ y

    sub : SubRelation _<≤≡_ ℓ< ℓ<
    sub ._S_ = _<_
    sub .IsS {x} {y} r with r
    ...                   | strict x<y  = x < y
    ...                   | equal _     = ⊥*
    ...                   | nonstrict _ = ⊥*
    sub .IsS? r with r
    ...            | strict x<y  = yes x<y
    ...            | nonstrict _ = no λ ()
    ...            | equal     _ = no λ ()
    sub .extract {xRy = strict _ } x<y = x<y

  open SubRelation sub renaming (IsS? to Is<? ; extract to extract<)
  infix 1 begin_
  begin_ : (r : x <≤≡ y) → {True (Is<? r)} → x < y
  begin_ r {s} = extract< {xRy = r} (toWitness s)

  -- Partial order syntax
  module ≤-syntax where
    infixr 2 step-≤
    step-≤ : ∀ (x : P) → y <≤≡ z → x ≤ y → x <≤≡ z
    step-≤ x r x≤y with r
    ...               | strict    y<z = strict (≤-<-trans x x≤y y<z)
    ...               | nonstrict y≤z = nonstrict (isPoset .is-trans x _ _ x≤y y≤z)
    ...               | equal     y≡z = nonstrict (subst (x ≤_) y≡z x≤y)

    syntax step-≤ x yRz x≤y = x ≤⟨ x≤y ⟩ yRz

  module <-syntax where
    infixr 2 step-<
    step-< : ∀ (x : P) → y <≤≡ z → x < y → x <≤≡ z
    step-< x r x<y with r
    ...               | strict    y<z = strict (isQuoset .is-trans x _ _ x<y y<z)
    ...               | nonstrict y≤z = strict (<-≤-trans x x<y y≤z)
    ...               | equal     y≡z = strict (subst (x <_) y≡z x<y)

    syntax step-< x yRz x<y = x <⟨ x<y ⟩ yRz

  module ≡-syntax where
    infixr 2 step-≡→≤
    step-≡→≤ : ∀ (x : P) → y <≤≡ z → x ≡ y → x <≤≡ z
    step-≡→≤ x y<≤≡z x≡y = subst (_<≤≡ _) (λ i → x≡y (~ i)) y<≤≡z

    syntax step-≡→≤ x yRz x≡y = x ≡→≤⟨ x≡y ⟩ yRz

  infix 3 _◾
  _◾ : ∀ x → x <≤≡ x
  x ◾ = equal refl
