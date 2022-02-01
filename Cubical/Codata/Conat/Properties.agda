{- Conatural number properties (Tesla Ice Zhang et al., Feb. 2019)

This file defines operations and properties on conatural numbers:

- Infinity (∞).

- Proof that ∞ + 1 is equivalent to ∞.

- Proof that conatural is an hSet.

- Bisimulation on conatural

- Proof that bisimulation is equivalent to equivalence (Coinductive Proof
  Principle).

- Proof that this bisimulation is prop valued

The standard library also defines bisimulation on conaturals:

https://github.com/agda/agda-stdlib/blob/master/src/Codata/Conat/Bisimilarity.agda
-}

{-# OPTIONS --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary
open import Cubical.Codata.Conat.Base

Unwrap-prev : Conat′ → Type₀
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Conat′) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 = conat zero
  𝟙  = succ 𝟘
  𝟚  = succ 𝟙

  succ𝟙≡𝟚 : succ 𝟙 ≡ 𝟚
  succ𝟙≡𝟚 i = 𝟚

  pred𝟚≡𝟙 : unwrap-prev (force 𝟚) ≡ 𝟙
  pred𝟚≡𝟙 i = 𝟙

∞ : Conat
force ∞ = suc ∞

∞+1≡∞ : succ ∞ ≡ ∞
force (∞+1≡∞ _) = suc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = (cong succ ∞+1≡∞) ∙ ∞+1≡∞

_+_ : Conat → Conat → Conat
_+′_ : Conat′ → Conat → Conat′

force (x + y) = force x +′ y
zero +′ y = force y
suc x +′ y = suc (x + y)

n+∞≡∞ : ∀ n → n + ∞ ≡ ∞
n+′∞≡∞′ : ∀ n → n +′ ∞ ≡ suc ∞

force (n+∞≡∞ n i) = n+′∞≡∞′ (force n) i
n+′∞≡∞′ zero = refl
n+′∞≡∞′ (suc n) = λ i → suc (n+∞≡∞ n i)

∞+∞≡∞ : ∞ + ∞ ≡ ∞
force (∞+∞≡∞ i) = suc (∞+∞≡∞ i)

+-zeroˡ : ∀ n → 𝟘 + n ≡ n
force (+-zeroˡ n _) = force n

+-zeroʳ : ∀ n → n + 𝟘 ≡ n
+′-zeroʳ : ∀ n → n +′ 𝟘 ≡ n

force (+-zeroʳ n i) = +′-zeroʳ (force n) i
+′-zeroʳ zero _ = zero
+′-zeroʳ (suc n) i = suc (+-zeroʳ n i)

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+′-assoc : ∀ m n p → (m +′ n) +′ p ≡ m +′ (n + p)

force (+-assoc m n p i) = +′-assoc (force m) n p i
+′-assoc zero _ _ = refl
+′-assoc (suc m) n p i = suc (+-assoc m n p i)


conat-absurd : ∀ {y : Conat} {ℓ} {Whatever : Type ℓ} → zero ≡ suc y → Whatever
conat-absurd eq = ⊥.rec (transport (cong diag eq) tt)
  where
  diag : Conat′ → Type₀
  diag zero = Unit
  diag (suc _) = ⊥

module IsSet where
  ≡-stable  : {x y : Conat} → Stable (x ≡ y)
  ≡′-stable : {x y : Conat′} → Stable (x ≡ y)

  force (≡-stable ¬¬p i) = ≡′-stable (λ ¬p → ¬¬p (λ p → ¬p (cong force p))) i
  ≡′-stable {zero}  {zero}  ¬¬p′ = refl
  ≡′-stable {suc x} {suc y} ¬¬p′ =
     cong′ suc (≡-stable λ ¬p → ¬¬p′ λ p → ¬p (cong pred′′ p))
  ≡′-stable {zero}  {suc y} ¬¬p′ = ⊥.rec (¬¬p′ conat-absurd)
  ≡′-stable {suc x} {zero}  ¬¬p′ = ⊥.rec (¬¬p′ λ p → conat-absurd (sym p))

  isSetConat : isSet Conat
  isSetConat _ _ = Separated→isSet (λ _ _ → ≡-stable) _ _

  isSetConat′ : isSet Conat′
  isSetConat′ m n p′ q′ = cong (cong force) (isSetConat (conat m) (conat n) p q)
    where p = λ where i .force → p′ i
          q = λ where i .force → q′ i

module Bisimulation where
  open IsSet using (isSetConat)

  record _≈_ (x y : Conat) : Type₀
  data _≈′_ (x y : Conat′) : Type₀
  _≈′′_ : Conat′ → Conat′ → Type₀
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

  bisim : ∀ {x y} → x ≈ y → x ≡ y
  bisim′ : ∀ {x y} → x ≈′ y → x ≡ y

  bisim′ {zero} {zero} (con tt) = refl
  bisim′ {zero} {suc x} (con ())
  bisim′ {suc x} {zero} (con ())
  bisim′ {suc x} {suc y} (con eq) i = suc (bisim eq i)
  force (bisim eq i) = bisim′ (prove eq) i

  misib : ∀ {x y} → x ≡ y → x ≈ y
  misib′ : ∀ {x y} → x ≡ y → x ≈′ y

  misib′ {zero} {zero} _ = con tt
  misib′ {zero} {suc x} = conat-absurd
  misib′ {suc x} {zero} p = conat-absurd (sym p)
  -- misib′ {suc x} {suc y} p = con λ where .prove → misib′ (cong pred′ p)
  misib′ {suc x} {suc y} p = con (misib (cong pred′′ p))
  prove (misib x≡y) = misib′ (cong force x≡y)

  iso″ : ∀ {x y} → (p : x ≈ y) → misib (bisim p) ≡ p
  iso′ : ∀ {x y} → (p : x ≈′ y) → misib′ (bisim′ p) ≡ p

  iso′ {zero} {zero} (con p) = refl
  iso′ {zero} {suc x} (con ())
  iso′ {suc x} {zero} (con ())
  iso′ {suc x} {suc y} (con p) = cong con (iso″ p)
  prove (iso″ p i) = iso′ (prove p) i

  osi : ∀ {x y} → (p : x ≡ y) → bisim (misib p) ≡ p
  osi p = isSetConat _ _ _ p

  path≃bisim : ∀ {x y} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv (iso misib bisim iso″ osi)

  path≡bisim : ∀ {x y} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

  isProp≈ : ∀ {x y} → isProp (x ≈ y)
  isProp≈ = subst isProp path≡bisim (isSetConat _ _)
