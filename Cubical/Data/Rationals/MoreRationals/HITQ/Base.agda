{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreRationals.HITQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import Cubical.Data.Int

open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma


-- ℚ as a higher inductive type

data ℚ : Type₀ where
  con : (u : ℤ) (a : ℤ) → ¬ (a ≡ 0) → ℚ
  path : ∀ u a v b {p q} → (u · b) ≡ (v · a) → con u a p ≡ con v b q
  trunc : isSet ℚ

[_] : ℤ × ℕ₊₁ → ℚ
[ a , 1+ b ] = con a (pos (suc b)) (ℕ.snotz ∘ cong abs)

module Elim {ℓ} {B : ℚ → Type ℓ}
  (con* : ∀ u a (p : ¬ (a ≡ 0)) → B (con u a p))
  (path* : ∀ u a v b {p q} (eq : (u · b) ≡ (v · a))
    → PathP (λ i → B (path u a v b {p} {q} eq i)) (con* u a p) (con* v b q))
  (trunc* : (q : ℚ) → isSet (B q))
  where

  f : (q : ℚ) → B q
  f (con u a x) = con* u a x
  f (path u a v b x i) = path* u a v b x i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {ℓ} {B : ℚ → Type ℓ} {BProp : {q : ℚ} → isProp (B q)}
  (con* : ∀ u a (p : ¬ (a ≡ 0)) → B (con u a p))
  where

  f : (q : ℚ) → B q
  f = Elim.f con*
    (λ u a v b {p} {q} eq →
      toPathP (BProp (transport (λ i → B (path u a v b eq i)) (con* u a p)) (con* v b q)))
    λ q → isProp→isSet BProp

module Rec {ℓ} {B : Type ℓ} {BType : isSet B}
  (con* : ∀ u a (p : ¬ (a ≡ 0)) → B)
  (path* : ∀ u a v b {p q} (eq : (u · b) ≡ (v · a))
    → con* u a p ≡ con* v b q) where

  f : ℚ → B
  f = Elim.f con* path* λ _ → BType

module Rec2 {ℓ} {B : Type ℓ} {BType : isSet B}
  (con* : ∀ u a (p : ¬ (a ≡ 0)) v b (q : ¬ (b ≡ 0)) → B)
  (path*₁ : ∀ u₁ a₁ {p₁}
    u₂ a₂ v₂ b₂ {p₂ q₂}
    (eq₁ : (u₁ · b₂) ≡ (v₂ · a₁))
    → con* u₁ a₁ p₁ u₂ a₂ p₂ ≡ con* v₂ b₂ q₂ u₂ a₂ p₂)
  (path*₂ : ∀ u₁ a₁ {p₁}
    u₂ a₂ v₂ b₂ {p₂ q₂}
    (eq₂ : (u₂ · b₂) ≡ (v₂ · a₂))
    → con* u₁ a₁ p₁ u₂ a₂ p₂ ≡ con* u₁ a₁ p₁ v₂ b₂ q₂)
  where

  f : ℚ → ℚ → B
  f = Rec.f {BType = λ x y p q i j w → BType (x w) (y w) (λ k → p k w) (λ k → q k w) i j}
    (λ u a p → Rec.f {BType = BType} (con* u a p) (path*₂ u a {p}))
    λ u a v b eq → funExt (ElimProp.f {BProp = BType _ _}
      λ u₂ a₂ p₂ → path*₁ _ _ _ _ _ _ eq)


--- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n , 1 ] }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n , 1 ] }
