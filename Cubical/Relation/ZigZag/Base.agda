-- We define ZigZag-complete relations and prove that quasi equivalence relations
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

record isQuasiEquivRel {A B : Type ℓ} (R : A → B → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    zigzag : isZigZagComplete R
    fwd : A → B
    fwdRel : (a : A) → R a (fwd a)
    bwd : B → A
    bwdRel : (b : B) → R (bwd b) b

open isQuasiEquivRel

QuasiEquivRel : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
QuasiEquivRel A B ℓ' =
  Σ[ R ∈ PropRel A B ℓ' ] isQuasiEquivRel (R .fst)

invQER : {A B : Type ℓ} {ℓ' : Level} → QuasiEquivRel A B ℓ' → QuasiEquivRel B A ℓ'
invQER (R , qer) .fst = invPropRel R
invQER (R , qer) .snd .zigzag aRb aRb' a'Rb' = qer .zigzag a'Rb' aRb' aRb
invQER (R , qer) .snd .fwd = qer .bwd
invQER (R , qer) .snd .fwdRel = qer .bwdRel
invQER (R , qer) .snd .bwd = qer .fwd
invQER (R , qer) .snd .bwdRel = qer .fwdRel

QER→EquivRel : {A B : Type ℓ}
  → QuasiEquivRel A B ℓ' → EquivPropRel A ℓ'
QER→EquivRel (R , sim) .fst .fst a₀ a₁ = R .fst a₀ (sim .fwd a₁)
QER→EquivRel (R , sim) .fst .snd _ _ = R .snd _ _
QER→EquivRel (R , sim) .snd .reflexive a = sim .fwdRel a
QER→EquivRel (R , sim) .snd .symmetric a₀ a₁ r =
  sim .zigzag (sim .fwdRel a₁) r (sim .fwdRel a₀)
QER→EquivRel (R , sim) .snd .transitive a₀ a₁ a₂ r s =
  sim .zigzag r (sim .fwdRel a₁) s

-- The following result is due to Carlo Angiuli
module QER→Equiv {A B : Type ℓ} (R : QuasiEquivRel A B ℓ') where

  private
    sim = R .snd
    f = sim .fwd
    g = sim .bwd

  Rᴸ = QER→EquivRel R .fst .fst
  Rᴿ = QER→EquivRel (invQER R) .fst .fst

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
