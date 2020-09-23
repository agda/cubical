{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.S2.Base where

open import Cubical.Foundations.Prelude

data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl

open import Cubical.Foundations.HLevels
S²ToSetRec : ∀ {ℓ} {A : S² → Type ℓ} → ((x : S²) → isSet (A x)) → (A base) → (x : S²) → A x
S²ToSetRec {A = A} set b base = b
S²ToSetRec {A = A} set b (surf i j) = isOfHLevel→isOfHLevelDep 2 set b b {a0 = refl} {a1 = refl} refl refl surf i j
