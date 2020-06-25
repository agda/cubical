-- We define ZigZag-complete relations and prove that bisimulations
-- give rise to equivalences on the set quotients.
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.ZigZag.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.Relation.Binary.Base

open BinaryRelation
open isEquivRel

private
 variable
  ℓ ℓ' : Level

isZigZagComplete : {A B : Type ℓ} (R : A → B → Type ℓ') → Type (ℓ-max ℓ ℓ')
isZigZagComplete R = ∀ {a b a' b'} → R a b → R a' b → R a' b' → R a b'

ZigZagRel : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
ZigZagRel A B ℓ' = Σ[ R ∈ (A → B → Type ℓ') ] (isZigZagComplete R)

record isBisimulation {A B : Type ℓ} (R : A → B → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    zigzag : isZigZagComplete R
    fwd : A → B
    fwdRel : (a : A) → R a (fwd a)
    bwd : B → A
    bwdRel : (b : B) → R (bwd b) b

open isBisimulation

Bisimulation : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Bisimulation A B ℓ' =
  Σ[ R ∈ PropRel A B ℓ' ] isBisimulation (R .fst)

invBisim : {A B : Type ℓ} {ℓ' : Level} → Bisimulation A B ℓ' → Bisimulation B A ℓ'
invBisim (R , bisim) .fst = invPropRel R
invBisim (R , bisim) .snd .zigzag aRb aRb' a'Rb' = bisim .zigzag a'Rb' aRb' aRb
invBisim (R , bisim) .snd .fwd = bisim .bwd
invBisim (R , bisim) .snd .fwdRel = bisim .bwdRel
invBisim (R , bisim) .snd .bwd = bisim .fwd
invBisim (R , bisim) .snd .bwdRel = bisim .fwdRel

bisim→EquivRel : {A B : Type ℓ}
  → Bisimulation A B ℓ' → EquivPropRel A ℓ'
bisim→EquivRel (R , sim) .fst .fst a₀ a₁ = R .fst a₀ (sim .fwd a₁)
bisim→EquivRel (R , sim) .fst .snd _ _ = R .snd _ _
bisim→EquivRel (R , sim) .snd .reflexive a = sim .fwdRel a
bisim→EquivRel (R , sim) .snd .symmetric a₀ a₁ r =
  sim .zigzag (sim .fwdRel a₁) r (sim .fwdRel a₀)
bisim→EquivRel (R , sim) .snd .transitive a₀ a₁ a₂ r s =
  sim .zigzag r (sim .fwdRel a₁) s

-- The following result is due to Carlo Angiuli
module Bisim→Equiv {A B : Type ℓ} (R : Bisimulation A B ℓ') where

  private
    sim = R .snd
    f = sim .fwd
    g = sim .bwd

  Rᴸ = bisim→EquivRel R .fst .fst
  Rᴿ = bisim→EquivRel (invBisim R) .fst .fst

  Thm : (A / Rᴸ) ≃ (B / Rᴿ)
  Thm = isoToEquiv (iso φ ψ η ε)
    where
    φ : _
    φ [ a ] = [ f a ]
    φ (eq/ a₀ a₁ r i) = eq/ _ _ (sim .zigzag (sim .bwdRel (f a₁)) r (sim .fwdRel a₀)) i
    φ (squash/ _ _ p q j i) = squash/ _ _ (cong φ p) (cong φ q) j i

    ψ : _
    ψ [ b ] = [ g b ]
    ψ (eq/ b₀ b₁ s i) = eq/ _ _ (sim .zigzag (sim .bwdRel b₀) s (sim .fwdRel (g b₁))) i
    ψ (squash/ _ _ p q j i) = squash/ _ _ (cong ψ p) (cong ψ q) j i

    η = elimProp (λ _ → squash/ _ _) (λ b → eq/ _ _ (sim .fwdRel (g b)))

    ε = elimProp (λ _ → squash/ _ _) (λ a → eq/ _ _ (sim .bwdRel (f a)))
