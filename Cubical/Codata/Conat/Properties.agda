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

{-# OPTIONS --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
  renaming (Bool→Type to ⟨_⟩)

import Cubical.Data.Nat as Nat

open import Cubical.Functions.Embedding

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary
open import Cubical.Codata.Conat.Base

import Cubical.Axiom.Omniscience as Omni

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

embed : Nat.ℕ → Conat
embed Nat.zero .force = zero
embed (Nat.suc n) .force = suc (embed n)

embed-inj : ∀ m n → embed m ≡ embed n → m ≡ n
embed-inj m n p with ⊎Path.encode _ _ (cong force p)
embed-inj Nat.zero Nat.zero _ | _ = refl
embed-inj (Nat.suc m) (Nat.suc n) _ | lift q
  = cong Nat.suc (embed-inj m n q)

embed≢∞ : ∀ n → embed n ≡ ∞ → ⊥
embed≢∞ Nat.zero = lower ∘ ⊎Path.encode _ _ ∘ cong force
embed≢∞ (Nat.suc n) = embed≢∞ n ∘ lower ∘ ⊎Path.encode _ _ ∘ cong force

cover : Nat.ℕ → Conat
cover Nat.zero = ∞
cover (Nat.suc n) = embed n

cover-inj : ∀ m n → cover m ≡ cover n → m ≡ n
cover-inj Nat.zero Nat.zero _ = refl
cover-inj (Nat.suc m) (Nat.suc n) p = cong Nat.suc (embed-inj m n p)
cover-inj Nat.zero (Nat.suc n) = ⊥.rec ∘ embed≢∞ n ∘ sym
cover-inj (Nat.suc m) Nat.zero = ⊥.rec ∘ embed≢∞ m

module IsSet where
  ≡-stable  : {x y : Conat} → Stable (x ≡ y)
  ≡′-stable : {x y : Conat′} → Stable (x ≡ y)

  force (≡-stable ¬¬p i) = ≡′-stable (λ ¬p → ¬¬p (λ p → ¬p (cong force p))) i
  ≡′-stable {zero}  {zero}  ¬¬p′ = refl
  ≡′-stable {suc x} {suc y} ¬¬p′ =
     congS suc (≡-stable λ ¬p → ¬¬p′ λ p → ¬p (cong pred′′ p))
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

module WLPO where
  -- search a decidable predicate on ℕ for the first true
  search : (Nat.ℕ → Bool) → Conat
  search′ : (Nat.ℕ → Bool) → Bool → Conat′

  search f .force = search′ f (f 0)

  search′ _  true = zero
  search′ f false = suc (search (f ∘ Nat.suc))

  -- the constantly false predicate searches to ∞
  search-false : search (const false) ≡ ∞
  search-false i .force = suc (search-false i)

  wrap : Conat′ → Conat
  wrap zero = ∞
  wrap (suc m) = m

  search-lemma : ∀ α n → search α ≡ ∞ → α n ≡ false
  search-lemma α Nat.zero p with α 0 | cong force p
  ... | false | q = refl
  ... | true | q = ⊥.rec (⊎Path.encode zero (suc ∞) q .lower)
  search-lemma α (Nat.suc n) p with α 0 | cong force p
  ... | false | q = search-lemma (α ∘ Nat.suc) n (cong wrap q)
  ... |  true | q = ⊥.rec (⊎Path.encode zero (suc ∞) q .lower)

  search-n : ∀ α n → search α ≡ embed n → α n ≡ true
  search-n α Nat.zero p with α 0 | ⊎Path.encode _ _ (cong force p)
  ... |  true | _ = refl
  search-n α (Nat.suc n) p with α 0 | ⊎Path.encode _ _ (cong force p)
  ... | false | q = search-n (α ∘ Nat.suc) n (q .lower)


  module _ (f : Conat → Nat.ℕ) (emb : isEmbedding f) where
    discreteConat : Discrete Conat
    discreteConat
      = Embedding-into-Discrete→Discrete (f , emb) Nat.discreteℕ

    wlpo' : Omni.WLPO' Nat.ℕ
    wlpo' α with discreteConat (search α) ∞
    ... | yes p = yes λ i n → search-lemma α n p i
    ... | no ¬p = no (¬p ∘ _∙ search-false ∘ cong search)

module LPO where
  open WLPO using (search; search-lemma; search-n)

  module Un (uncover : Conat → Nat.ℕ) (sect : section cover uncover) where
    search-0 : ∀ α → uncover (search α) ≡ 0 → ∀ n → α n ≡ false
    search-0 α p n
      = search-lemma α n (sym (sect (search α)) ∙ cong cover p)

    search-n' : ∀ α n → uncover (search α) ≡ Nat.suc n → α n ≡ true
    search-n' α n p = search-n α n (sym (sect (search α)) ∙ cong cover p)

    -- So, surjectivity of `cover` implies LPO, since `cover` has
    -- already been shown injective, and surjectivity would make it an
    -- equivalence (as ℕ and Conat are sets).
    lpo' : Omni.LPO∞ Nat.ℕ
    lpo' α = disc (uncover (search α)) refl where
      disc : ∀ n → uncover (search α) ≡ n → _
      disc Nat.zero p = inl λ n → subst ⟨_⟩ (search-0 α p n)
      disc (Nat.suc n) p = inr (n , subst⁻ ⟨_⟩ (search-n' α n p) _)
