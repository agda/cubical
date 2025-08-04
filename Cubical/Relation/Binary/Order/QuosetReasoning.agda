{-
  Equational reasoning in a Quoset that is also a Poset,
  i.e. for writing a chain of <, ≤, ≡.

  Import <-≤-StrictReasoning if you only need to obtain strict inequalities,
  import <-≤-Reasoning otherwise.

  Use begin< to obtain a strict inequality (in this case, at least one < is required in the chain).
  Use begin≤ to obtain a nonstrict inequality.
-}

module Cubical.Relation.Binary.Order.QuosetReasoning where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty.Base as ⊥

open import Cubical.Relation.Nullary.Base

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base

private
  variable
    ℓ ℓ≤ ℓ< : Level

  module Triple
      (P : Type ℓ)
      ((posetstr  (_≤_) isPoset ) : PosetStr ℓ≤ P)
      ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
    where
      private variable
        x y : P

      data _<≤≡_ : P → P → Type (ℓ-max ℓ (ℓ-max ℓ< ℓ≤)) where
        strict    : x < y → x <≤≡ y
        nonstrict : x ≤ y → x <≤≡ y
        equal     : x ≡ y → x <≤≡ y

      Is< : ∀ {x y} → x <≤≡ y → Type ℓ<
      Is< {x} {y} (strict    _) = x < y
      Is<         (nonstrict _) = ⊥*
      Is<         (equal     _) = ⊥*

      Is<? : (x<y : x <≤≡ y) → Dec(Is< x<y)
      Is<? (strict  x<y) = yes x<y
      Is<? (nonstrict _) = no λ ()
      Is<? (equal     _) = no λ ()

      extract< : {xRy : x <≤≡ y} → Is< xRy → x < y
      extract< {xRy = strict _} x<y = x<y

module <-≤-StrictReasoning
    (P : Type ℓ)
    ((posetstr  (_≤_) isPoset ) : PosetStr ℓ≤ P)
    ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
    (<-≤-trans : ∀ x {y z} → x < y → y ≤ z → x < z)
    (≤-<-trans : ∀ x {y z} → x ≤ y → y < z → x < z)
  where

  open Triple P (posetstr (_≤_) isPoset) (quosetstr (_<_) isQuoset)

  private variable
    x y z : P

  infix 1 begin<_
  begin<_ : (r : x <≤≡ y) → {True (Is<? r)} → x < y
  begin<_ r {s} = extract< {xRy = r} (toWitness s)

  -- Partial order syntax
  module ≤-syntax where
    open IsPoset

    infixr 2 step-≤
    step-≤ : ∀ (x : P) → y <≤≡ z → x ≤ y → x <≤≡ z
    step-≤ x (strict    y<z) x≤y = strict (≤-<-trans x x≤y y<z)
    step-≤ x (nonstrict y≤z) x≤y = nonstrict (isPoset .is-trans x _ _ x≤y y≤z)
    step-≤ x (equal     y≡z) x≤y = nonstrict (subst (x ≤_) y≡z x≤y)

    syntax step-≤ x yRz x≤y = x ≤⟨ x≤y ⟩ yRz

  module <-syntax where
    open IsQuoset

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
    ((posetstr  (_≤_) isPoset ) : PosetStr ℓ≤ P)
    ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
    (<-≤-trans  : ∀ x {y z} → x < y → y ≤ z → x < z)
    (≤-<-trans  : ∀ x {y z} → x ≤ y → y < z → x < z)
    (<-≤-weaken : ∀ {x y}   → x < y → x ≤ y)
  where

  open <-≤-StrictReasoning P
      (posetstr (_≤_) isPoset) (quosetstr (_<_) isQuoset)
      <-≤-trans ≤-<-trans
    public

  open Triple P (posetstr (_≤_) isPoset) (quosetstr (_<_) isQuoset)
  open IsPoset

  infix 1 begin≤_
  begin≤_ : ∀ {x y} → (r : x <≤≡ y) → x ≤ y
  begin≤_ (strict    x<y) = <-≤-weaken x<y
  begin≤_ (nonstrict x≤y) = x≤y
  begin≤_ (equal {x} x≡y) = subst (x ≤_) x≡y (isPoset .is-refl x)

-- Examples of usage:

module Examples (P : Type ℓ)
    ((posetstr  (_≤_) isPoset ) : PosetStr ℓ≤ P)
    ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
    (<-≤-trans  : ∀ x {y z} → x < y → y ≤ z → x < z)
    (≤-<-trans  : ∀ x {y z} → x ≤ y → y < z → x < z)
    (<-≤-weaken : ∀ {x y}   → x < y → x ≤ y)
  where

  example< : ∀ x y z u v w α γ δ
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
    x <⟨ x<y ⟩
    y ≤⟨ y≤z ⟩
    z ≡→≤⟨ z ≡⟨      z≡u   ⟩
           u ≡⟨  sym z≡u   ⟩
           z ≡[ i ]⟨ z≡u i ⟩
           u ∎ ⟩
    u <⟨ u<v ⟩
    v ≤⟨ v≤w ⟩
    w ≡→≤⟨
          w ≡⟨ w≡α ⟩
          α ≡⟨ α≡γ ⟩
          γ ≡[ i ]⟨ γ≡δ i ⟩
          δ ∎
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

  example≤ : ∀ x y z u v w α γ δ
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
    x <⟨ x<y ⟩
    y ≤⟨ y≤z ⟩
    z ≡→≤⟨ z ≡⟨      z≡u   ⟩
           u ≡⟨  sym z≡u   ⟩
           z ≡[ i ]⟨ z≡u i ⟩
           u ∎ ⟩
    u <⟨ u<v ⟩
    v ≤⟨ v≤w ⟩
    w ≡→≤⟨
          w ≡⟨ w≡α ⟩
          α ≡⟨ α≡γ ⟩
          γ ≡[ i ]⟨ γ≡δ i ⟩
          δ ∎
        ⟩
    δ ◾
      where
        open <-syntax
        open ≤-syntax
        open ≡-syntax

  example≤' : ∀ y z u w α γ δ
            → y ≤ z
            → z ≡ u
            → u ≤ w
            → w ≡ α
            → α ≡ γ
            → γ ≡ δ
            → y ≤ δ
  example≤' y z u w α γ δ y≤z z≡u u≤w w≡α α≡γ γ≡δ = begin≤
    y ≤⟨ y≤z ⟩
    z ≡→≤⟨ z ≡⟨      z≡u   ⟩
           u ≡⟨  sym z≡u   ⟩
           z ≡[ i ]⟨ z≡u i ⟩
           u ∎ ⟩
    u ≤⟨ u≤w ⟩
    w ≡→≤⟨
          w ≡⟨ w≡α ⟩
          α ≡⟨ α≡γ ⟩
          γ ≡[ i ]⟨ γ≡δ i ⟩
          δ ∎
        ⟩
    δ ◾
      where
        open ≤-syntax
        open ≡-syntax
