{-# OPTIONS --safe #-}
{-
  Equational reasoning in a Quoset that is also a Poset, i.e.
  for writing a chain of <,≤,≡ .

  Use begin< to obtain a strict inequality (in this case, at least one < is required in the chain).
  Use begin≤ to obtain a nonstrict inequality.

  Import <-≤-StrictReasoning if you only need begin<,
  otherwise import <-≤-Reasoning.
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

module <-≤-StrictReasoning
  (P : Type ℓ)
  ((posetstr  (_≤_) isPoset)  : PosetStr ℓ≤ P)
  ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
  (<-≤-trans  : ∀ x {y z} → x < y → y ≤ z → x < z)
  (≤-<-trans  : ∀ x {y z} → x ≤ y → y < z → x < z)  where

  open IsPoset
  open IsQuoset
  open SubRelation

  data _<≤≡_ : P → P → Type (ℓ-max ℓ (ℓ-max ℓ< ℓ≤)) where
    strict    : ∀ {x y} → x < y → x <≤≡ y
    nonstrict : ∀ {x y} → x ≤ y → x <≤≡ y
    equal     : ∀ {x y} → x ≡ y → x <≤≡ y

  private
    variable
      x y z : P
    sub : SubRelation _<≤≡_ ℓ< ℓ<
    sub ._S_ = _<_
    sub .IsS {x} {y} (strict    _) = x < y
    sub .IsS         (equal     _) = ⊥*
    sub .IsS         (nonstrict _) = ⊥*
    sub .IsS? (strict x<y ) = yes x<y
    sub .IsS? (nonstrict _) = no λ ()
    sub .IsS? (equal     _) = no λ ()
    sub .extract {xRy = strict _ } x<y = x<y

  open SubRelation sub renaming (IsS? to Is<? ; extract to extract<)

  infix 1 begin<_
  begin<_ : (r : x <≤≡ y) → {True (Is<? r)} → x < y
  begin<_ r {s} = extract< {xRy = r} (toWitness s)

  -- Partial order syntax
  module ≤-syntax where
    infixr 2 step-≤
    step-≤ : ∀ (x : P) → y <≤≡ z → x ≤ y → x <≤≡ z
    step-≤ x (strict    y<z) x≤y = strict (≤-<-trans x x≤y y<z)
    step-≤ x (nonstrict y≤z) x≤y = nonstrict (isPoset .is-trans x _ _ x≤y y≤z)
    step-≤ x (equal     y≡z) x≤y = nonstrict (subst (x ≤_) y≡z x≤y)

    syntax step-≤ x yRz x≤y = x ≤⟨ x≤y ⟩ yRz

  module <-syntax where
    infixr 2 step-<
    step-< : ∀ (x : P) → y <≤≡ z → x < y → x <≤≡ z
    step-< x (strict    y<z) x<y = strict (isQuoset .is-trans x _ _ x<y y<z)
    step-< x (nonstrict y≤z) x<y = strict (<-≤-trans x x<y y≤z)
    step-< x (equal     y≡z) x<y = strict (subst (x <_) y≡z x<y)

    syntax step-< x yRz x<y = x <⟨ x<y ⟩ yRz

  module ≡-syntax where
    infixr 2 step-≡→≤
    step-≡→≤ : ∀ (x : P) → y <≤≡ z → x ≡ y → x <≤≡ z
    step-≡→≤ x y<≤≡z x≡y = subst (_<≤≡ _) (λ i → x≡y (~ i)) y<≤≡z

    syntax step-≡→≤ x yRz x≡y = x ≡→≤⟨ x≡y ⟩ yRz

  infix 3 _◾
  _◾ : ∀ x → x <≤≡ x
  x ◾ = equal refl


module <-≤-Reasoning
  (P : Type ℓ)
  ((posetstr  (_≤_) isPoset)  : PosetStr ℓ≤ P)
  ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
  (<-≤-trans  : ∀ x {y z} → x < y → y ≤ z → x < z)
  (≤-<-trans  : ∀ x {y z} → x ≤ y → y < z → x < z)
  (<-≤-weaken : ∀ {x y}   → x < y → x ≤ y) where

  open <-≤-StrictReasoning P
    (posetstr  (_≤_) isPoset) (quosetstr (_<_) isQuoset)
    <-≤-trans ≤-<-trans public

  open IsPoset

  infix 1 begin≤_
  begin≤_ : ∀ {x y} → (r : x <≤≡ y) → x ≤ y
  begin≤_ (strict    x<y) = <-≤-weaken x<y
  begin≤_ (nonstrict x≤y) = x≤y
  begin≤_ (equal {x} x≡y) = subst (x ≤_) x≡y (isPoset .is-refl x)

-- Examples of usage:

module Examples (P : Type ℓ)
  ((posetstr  (_≤_) isPoset)  : PosetStr ℓ≤ P)
  ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
  (<-≤-trans  : ∀ x {y z} → x < y → y ≤ z → x < z)
  (≤-<-trans  : ∀ x {y z} → x ≤ y → y < z → x < z)
  (<-≤-weaken : ∀ {x y}   → x < y → x ≤ y) where

  example< : ∀ (x y z u v w α γ δ : P)
           → x < y
           → y ≤ z
           → z ≡ u
           → u < v
           → v ≤ w
           → w ≡ α
           → α ≡ γ
           → γ ≡ δ
           → x < δ
  example< x y z u v w α γ δ x<y y≤z z≡u u<v v≤w w≡α α≡γ γ≡δ = begin<
    x   <⟨   x<y      ⟩
    y   ≤⟨   y≤z      ⟩
    z   ≡→≤⟨ z ≡⟨ z≡u        ⟩
             u ≡⟨ sym z≡u    ⟩
             z ≡[ i ]⟨ z≡u i ⟩
             u ∎     ⟩
    u   <⟨   u<v      ⟩
    v   ≤⟨   v≤w      ⟩
    w   ≡→≤⟨
            w   ≡⟨ w≡α ⟩
            α   ≡⟨ α≡γ ⟩
            γ   ≡[ i ]⟨ γ≡δ i ⟩
            δ   ∎
          ⟩
    δ ◾
      where
        open <-≤-StrictReasoning P
          (posetstr (_≤_) isPoset) (quosetstr (_<_) isQuoset)
          <-≤-trans ≤-<-trans
        open <-syntax
        open ≤-syntax
        open ≡-syntax

  open <-≤-Reasoning P
    (posetstr (_≤_) isPoset) (quosetstr (_<_) isQuoset)
    <-≤-trans ≤-<-trans <-≤-weaken

  example≤ : ∀ (x y z u v w α γ δ : P)
           → x < y
           → y ≤ z
           → z ≡ u
           → u < v
           → v ≤ w
           → w ≡ α
           → α ≡ γ
           → γ ≡ δ
           → x ≤ δ
  example≤ x y z u v w α γ δ x<y y≤z z≡u u<v v≤w w≡α α≡γ γ≡δ = begin≤
    x   <⟨   x<y      ⟩
    y   ≤⟨   y≤z      ⟩
    z   ≡→≤⟨ z ≡⟨ z≡u        ⟩
             u ≡⟨ sym z≡u    ⟩
             z ≡[ i ]⟨ z≡u i ⟩
             u ∎     ⟩
    u   <⟨   u<v      ⟩
    v   ≤⟨   v≤w      ⟩
    w   ≡→≤⟨
            w   ≡⟨ w≡α ⟩
            α   ≡⟨ α≡γ ⟩
            γ   ≡[ i ]⟨ γ≡δ i ⟩
            δ   ∎
          ⟩
    δ ◾
      where
        open <-syntax
        open ≤-syntax
        open ≡-syntax

  example≤' : ∀ (y z u w α γ δ : P)
            → y ≤ z
            → z ≡ u
            → u ≤ w
            → w ≡ α
            → α ≡ γ
            → γ ≡ δ
            → y ≤ δ
  example≤' y z u w α γ δ y≤z z≡u u≤w w≡α α≡γ γ≡δ = begin≤
    y   ≤⟨   y≤z      ⟩
    z   ≡→≤⟨ z ≡⟨ z≡u        ⟩
             u ≡⟨ sym z≡u    ⟩
             z ≡[ i ]⟨ z≡u i ⟩
             u ∎     ⟩
    u   ≤⟨   u≤w      ⟩
    w   ≡→≤⟨
            w   ≡⟨ w≡α ⟩
            α   ≡⟨ α≡γ ⟩
            γ   ≡[ i ]⟨ γ≡δ i ⟩
            δ   ∎
          ⟩
    δ ◾
      where
        open ≤-syntax
        open ≡-syntax
