{-# OPTIONS --safe #-}
module Cubical.HITs.Rationals.HITQ.Base where

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
  con : (u : ℤ) (a : ℤ) → ¬ (a ≡ pos 0) → ℚ
  path : ∀ u a v b {p q} → (u · b) ≡ (v · a) → con u a p ≡ con v b q
  trunc : isSet ℚ

[_] : ℤ × ℕ₊₁ → ℚ
[ a , 1+ b ] = con a (pos (suc b)) (ℕ.snotz ∘ cong abs)

module Elim {ℓ} {B : ℚ → Type ℓ}
  (con* : ∀ u a (p : ¬ (a ≡ pos 0)) → B (con u a p))
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
  (con* : ∀ u a (p : ¬ (a ≡ pos 0)) → B (con u a p))
  where

  f : (q : ℚ) → B q
  f = Elim.f con*
    (λ u a v b {p} {q} eq →
      toPathP (BProp (transport (λ i → B (path u a v b eq i)) (con* u a p)) (con* v b q)))
    λ q → isProp→isSet BProp

module Rec {ℓ} {B : Type ℓ} {BType : isSet B}
  (con* : ∀ u a (p : ¬ (a ≡ pos 0)) → B)
  (path* : ∀ u a v b {p q} (eq : (u · b) ≡ (v · a))
    → con* u a p ≡ con* v b q) where

  f : ℚ → B
  f = Elim.f con* path* λ _ → BType

-- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n , 1 ] }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n , 1 ] }
