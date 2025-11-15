-- We define ZigZag-complete relations and prove that quasi equivalence relations
-- give rise to equivalences on the set quotients.
module Cubical.Relation.ZigZag.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

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
    fwd : (a : A) → ∃[ b ∈ B ] R a b
    bwd : (b : B) → ∃[ a ∈ A ] R a b

open isQuasiEquivRel

QuasiEquivRel : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
QuasiEquivRel A B ℓ' =
  Σ[ R ∈ PropRel A B ℓ' ] isQuasiEquivRel (R .fst)

invQER : {A B : Type ℓ} {ℓ' : Level} → QuasiEquivRel A B ℓ' → QuasiEquivRel B A ℓ'
invQER (R , qer) .fst = invPropRel R
invQER (R , qer) .snd .zigzag aRb aRb' a'Rb' = qer .zigzag a'Rb' aRb' aRb
invQER (R , qer) .snd .fwd = qer .bwd
invQER (R , qer) .snd .bwd = qer .fwd

QER→EquivRel : {A B : Type ℓ}
  → QuasiEquivRel A B ℓ' → EquivPropRel A (ℓ-max ℓ ℓ')
QER→EquivRel (R , sim) .fst = compPropRel R (invPropRel R)
QER→EquivRel (R , sim) .snd .reflexive a = Trunc.map (λ {(b , r) → b , r , r}) (sim .fwd a)
QER→EquivRel (R , sim) .snd .symmetric _ _ = Trunc.map (λ {(b , r₀ , r₁) → b , r₁ , r₀})
QER→EquivRel (R , sim) .snd .transitive _ _ _ =
  Trunc.map2 (λ {(b , r₀ , r₁) (b' , r₀' , r₁') → b , r₀ , sim .zigzag r₁' r₀' r₁})

-- The following result is due to Carlo Angiuli
module QER→Equiv {A B : Type ℓ} (R : QuasiEquivRel A B ℓ') where

  Rᴸ = QER→EquivRel R .fst .fst
  Rᴿ = QER→EquivRel (invQER R) .fst .fst

  private
    sim = R .snd

  private
    f : (a : A) → ∃[ b ∈ B ] R .fst .fst a b → B / Rᴿ
    f a =
      Trunc.rec→Set squash/
        ([_] ∘ fst)
        (λ {(b , r) (b' , r') → eq/ b b' ∣ a , r , r' ∣₁})

    fPath :
      (a₀ : A) (s₀ : ∃[ b ∈ B ] R .fst .fst a₀ b)
      (a₁ : A) (s₁ : ∃[ b ∈ B ] R .fst .fst a₁ b)
      → Rᴸ a₀ a₁
      → f a₀ s₀ ≡ f a₁ s₁
    fPath a₀ =
      Trunc.elim (λ _ → isPropΠ3 λ _ _ _ → squash/ _ _)
        (λ {(b₀ , r₀) a₁ →
          Trunc.elim (λ _ → isPropΠ λ _ → squash/ _ _)
            (λ {(b₁ , r₁) →
              Trunc.elim (λ _ → squash/ _ _)
                (λ {(b' , r₀' , r₁') → eq/ b₀ b₁ ∣ a₀ , r₀ , sim .zigzag r₀' r₁' r₁ ∣₁})})})

    φ : A / Rᴸ → B / Rᴿ
    φ [ a ] = f a (sim .fwd a)
    φ (eq/ a₀ a₁ r i) =  fPath a₀ (sim .fwd a₀) a₁ (sim .fwd a₁) r i
    φ (squash/ _ _ p q j i) = squash/ _ _ (cong φ p) (cong φ q) j i


  relToFwd≡ : ∀ {a b} → R .fst .fst a b → φ [ a ] ≡ [ b ]
  relToFwd≡ {a} {b} r =
    Trunc.elim {P = λ s → f a s ≡ [ b ]} (λ _ → squash/ _ _)
      (λ {(b' , r') → eq/ b' b ∣ a , r' , r ∣₁})
      (sim .fwd a)

  fwd≡ToRel : ∀ {a b} → φ [ a ] ≡ [ b ] → R .fst .fst a b
  fwd≡ToRel {a} {b} =
    Trunc.elim {P = λ s → f a s ≡ [ b ] → R .fst .fst a b}
      (λ _ → isPropΠ λ _ → R .fst .snd _ _)
      (λ {(b' , r') p →
        Trunc.rec (R .fst .snd _ _)
          (λ {(a' , s' , s) → R .snd .zigzag r' s' s})
          (effective
            (QER→EquivRel (invQER R) .fst .snd)
            (QER→EquivRel (invQER R) .snd)
            b' b p)})
      (sim .fwd a)

  private
    g : (b : B) → ∃[ a ∈ A ] R .fst .fst a b → A / Rᴸ
    g b =
      Trunc.rec→Set squash/
        ([_] ∘ fst)
        (λ {(a , r) (a' , r') → eq/ a a' ∣ b , r , r' ∣₁})

    gPath :
      (b₀ : B) (s₀ : ∃[ a ∈ A ] R .fst .fst a b₀)
      (b₁ : B) (s₁ : ∃[ a ∈ A ] R .fst .fst a b₁)
      → Rᴿ b₀ b₁
      → g b₀ s₀ ≡ g b₁ s₁
    gPath b₀ =
      Trunc.elim (λ _ → isPropΠ3 λ _ _ _ → squash/ _ _)
        (λ {(a₀ , r₀) b₁ →
          Trunc.elim (λ _ → isPropΠ λ _ → squash/ _ _)
            (λ {(a₁ , r₁) →
              Trunc.elim (λ _ → squash/ _ _)
                (λ {(a' , r₀' , r₁') → eq/ a₀ a₁ ∣ b₀ , r₀ , sim .zigzag r₁ r₁' r₀' ∣₁})})})

    ψ : B / Rᴿ → A / Rᴸ
    ψ [ b ] = g b (sim .bwd b)
    ψ (eq/ b₀ b₁ r i) = gPath b₀ (sim .bwd b₀) b₁ (sim .bwd b₁) r i
    ψ (squash/ _ _ p q j i) = squash/ _ _ (cong ψ p) (cong ψ q) j i

  relToBwd≡ : ∀ {a b} → R .fst .fst a b → ψ [ b ] ≡ [ a ]
  relToBwd≡ {a} {b} r =
    Trunc.elim {P = λ s → g b s ≡ [ a ]} (λ _ → squash/ _ _)
      (λ {(a' , r') → eq/ a' a ∣ b , r' , r ∣₁})
      (sim .bwd b)

  private
    η : ∀ qb → φ (ψ qb) ≡ qb
    η =
      elimProp (λ _ → squash/ _ _)
        (λ b →
          Trunc.elim {P = λ s → φ (g b s) ≡ [ b ]} (λ _ → squash/ _ _)
            (λ {(a , r) → relToFwd≡ r})
            (sim .bwd b))

    ε : ∀ qa → ψ (φ qa) ≡ qa
    ε =
      elimProp (λ _ → squash/ _ _)
        (λ a →
          Trunc.elim {P = λ s → ψ (f a s) ≡ [ a ]} (λ _ → squash/ _ _)
            (λ {(b , r) → relToBwd≡ r})
            (sim .fwd a))

  bwd≡ToRel : ∀ {a b} → ψ [ b ] ≡ [ a ] → R .fst .fst a b
  bwd≡ToRel {a} {b} p = fwd≡ToRel (cong φ (sym p) ∙ η [ b ])

  Thm : (A / Rᴸ) ≃ (B / Rᴿ)
  Thm = isoToEquiv (iso φ ψ η ε)

-- A claim* is that Rᴸ and Rᴿ PER would imply R to be a zigzag complete.
-- That is not true, even if we assume that Rᴸ and Rᴿ are universal relations.
--
-- * Krishnaswami and Dreyer (https://drops.dagstuhl.de/opus/volltexte/2013/4212/) just below Definition 1,
--   which propagated to "Internalizing representation independence with univalence"
--   https://doi.org/10.1145/3434293, just above Definition 5.3
--
open HeterogenousRelation

module Universal→ZigZag {A B : Type ℓ} (R : PropRel A B ℓ') where

  Rᴸ = compPropRel R (invPropRel R)
  Rᴿ = compPropRel (invPropRel R) R

  Claim = isUniversalRel (Rᴸ .fst) → isUniversalRel (Rᴿ .fst) → isZigZagComplete (R .fst)

open import Cubical.Data.Empty using (⊥; isProp⊥)

¬Universal→ZigZag : (∀ {ℓ ℓ'} (A B : Type ℓ) (R : PropRel A B ℓ') → Universal→ZigZag.Claim R) → ⊥
¬Universal→ZigZag p = ¬R-zigzag (λ {a} {b} {a'} {b'} → p Bool Bool R Rᴸ-universal Rᴿ-universal {a} {b} {a'} {b'})
  where
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool

  -- zig...
  R : PropRel Bool Bool ℓ-zero
  R .fst false false = Unit
  R .fst false true  = ⊥
  R .fst true  b     = Unit
  R .snd false false = isPropUnit
  R .snd false true  = isProp⊥
  R .snd true  false = isPropUnit
  R .snd true  true  = isPropUnit

  -- ... but not zag
  ¬R-zigzag : isZigZagComplete (R .fst) → ⊥
  ¬R-zigzag p = p {a = false} {b = false} {a' = true} {b' = true} tt tt tt

  Rᴸ = compPropRel R (invPropRel R)
  Rᴿ = compPropRel (invPropRel R) R

  Rᴸ-universal : isUniversalRel (Rᴸ .fst)
  Rᴸ-universal false false = ∣ false , tt , tt ∣₁
  Rᴸ-universal false true  = ∣ false , tt , tt ∣₁
  Rᴸ-universal true  false = ∣ false , tt , tt ∣₁
  Rᴸ-universal true  true  = ∣ false , tt , tt ∣₁

  Rᴿ-universal : isUniversalRel (Rᴿ .fst)
  Rᴿ-universal false false = ∣ true , tt , tt ∣₁
  Rᴿ-universal false true  = ∣ true , tt , tt ∣₁
  Rᴿ-universal true  false = ∣ true , tt , tt ∣₁
  Rᴿ-universal true  true  = ∣ true , tt , tt ∣₁
