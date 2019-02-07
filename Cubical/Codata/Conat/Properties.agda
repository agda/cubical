{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Codata.Conat.Base

Unwrap-prev : Conat′ -> Set
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Conat′) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 : Conat
  force 𝟘 = zero
  one  = succ 𝟘
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-prev (force two) ≡ one
  predTwo≡one i = one

∞ : Conat
force ∞ = suc ∞

∞+1≡∞ : succ ∞ ≡ ∞
force (∞+1≡∞ _) = suc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

module Bisimulation where

  record _≈_ (x y : Conat) : Set
  data _≈′_ (x y : Conat′) : Set
  _≈′′_ : Conat′ → Conat′ → Set
  zero  ≈′′ zero  = Unit
  suc x ≈′′ suc y = x ≈ y
  -- So impossible proofs are preserved
  x ≈′′ y = ⊥

  record _≈_ x y where
    coinductive
    field prove : force x ≈′ force y

  data _≈′_  x y where
    con : x ≈′′ y → x ≈′ y

  open _≈_ public

  zsuc-inv : ∀ {y : Conat} {ℓ} {Whatever : Set ℓ} → zero ≡ suc y → Whatever
  zsuc-inv eq = ⊥-elim (transport (cong diag eq) tt)
    where
    diag : Conat′ → Set
    diag zero = Unit
    diag (suc _) = ⊥

  bisim : ∀ {x y} → x ≈ y → x ≡ y
  bisim′ : ∀ {x y} → x ≈′ y → x ≡ y

  bisim′ {zero} {zero} (con tt) = refl
  bisim′ {zero} {suc x} (con ())
  bisim′ {suc x} {zero} (con ())
  bisim′ {suc x} {suc y} (con eq) i = suc (bisim eq i)
  force (bisim eq i) = bisim′ (prove eq) i

  misib : ∀ {x y} → x ≡ y → x ≈ y
  misib′ : ∀ {x y} → x ≡ y → x ≈′ y

  misib′ {zero} {zero} p = con _
  misib′ {zero} {suc x} p = zsuc-inv p
  misib′ {suc x} {zero} p = zsuc-inv (sym p)
  -- misib′ {suc x} {suc y} p = con λ where .prove → misib′ (cong pred′ p)
  misib′ {suc x} {suc y} p = con (misib (cong pred′′ p))
  prove (misib x≡y) = misib′ (cong force x≡y)

  iso : ∀ {x y} → (p : x ≈ y) → misib (bisim p) ≡ p
  iso′ : ∀ {x y} → (p : x ≈′ y) → misib′ (bisim′ p) ≡ p

  iso′ {zero} {zero} (con p) = refl
  iso′ {zero} {suc x} (con ())
  iso′ {suc x} {zero} (con ())
  iso′ {suc x} {suc y} (con p) = cong con (iso p)
  prove (iso p i) = iso′ (prove p) i

  ≡-stable  : {x y : Conat} → Stable (x ≡ y)
  ≡′-stable : {x y : Conat′} → Stable (x ≡ y)

  force (≡-stable ¬¬p i) = ≡′-stable (λ ¬p → ¬¬p (λ p → ¬p (cong force p))) i
  ≡′-stable {zero}  {zero}  ¬¬p′ = refl
  ≡′-stable {suc x} {suc y} ¬¬p′ =
     cong′ suc (≡-stable λ ¬p → ¬¬p′ (λ p → ¬p (cong pred′′ p )))
  ≡′-stable {zero}  {suc y} ¬¬p′ = ⊥-elim (¬¬p′ zsuc-inv)
  ≡′-stable {suc x} {zero}  ¬¬p′ = ⊥-elim (¬¬p′ λ p → zsuc-inv(sym p))

  ≡-unique : {m n : Conat} (p q : m ≡ n) → p ≡ q
  ≡-unique = Stable≡→isSet (λ a b → ≡-stable) _ _

  ≡′-unique : {m n : Conat′} (p q : m ≡ n) → p ≡ q
  ≡′-unique {m′} {n′} p′ q′ = cong (cong force) (≡-unique {m} {n} p q)
    where m = λ where   .force → m′
          n = λ where .force → n′
          p = λ where i .force → p′ i
          q = λ where i .force → q′ i

  osi : ∀ {x y} → (p : x ≡ y) → bisim (misib p) ≡ p
  osi p = ≡-unique _ p

  path≃bisim : ∀ {x y} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv misib bisim iso osi

  path≡bisim : ∀ {x y} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

