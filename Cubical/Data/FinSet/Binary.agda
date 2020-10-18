{-# OPTIONS --cubical --no-import-sorts --safe --postfix-projections #-}

module Cubical.Data.FinSet.Binary where

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ : Level

isBinary : Type ℓ → Type ℓ
isBinary B = ∥ Bool ≃ B ∥

Binary : ∀ ℓ → Type _
Binary ℓ = Σ (Type ℓ) isBinary

isBinary→isSet : ∀{B : Type ℓ} → isBinary B → isSet B
isBinary→isSet {B} = rec isPropIsSet λ eqv → isOfHLevelRespectEquiv 2 eqv isSetBool

private
  Σ≡Prop²
    : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → {w x : Σ A B}
    → isOfHLevelDep 1 B
    → (p q : w ≡ x)
    → cong fst p ≡ cong fst q
    → p ≡ q
  Σ≡Prop² _ _ _ r i j .fst = r i j
  Σ≡Prop² {B = B} {w} {x} Bprp p q r i j .snd
    = isPropDep→isSetDep Bprp (w .snd) (x .snd) (cong snd p) (cong snd q) r i j


BinaryEmbedding : isEmbedding (λ(B : Binary ℓ) → map-snd isBinary→isSet B)
BinaryEmbedding w x = isoToIsEquiv theIso
  where
  open Iso
  f = map-snd isBinary→isSet

  theIso : Iso (w ≡ x) (f w ≡ f x)
  theIso .fun = cong f
  theIso .inv p i .fst = p i .fst
  theIso .inv p i .snd
    = ∥∥-isPropDep (Bool ≃_) (w .snd) (x .snd) (λ i → p i .fst) i
  theIso .rightInv p
    = Σ≡Prop² (isOfHLevel→isOfHLevelDep 1 (λ _ → isPropIsSet)) _ p refl
  theIso .leftInv p
    = Σ≡Prop² (∥∥-isPropDep (Bool ≃_)) _ p refl

Base : Binary _
Base .fst = Bool
Base .snd = ∣ idEquiv Bool ∣

Loop : Base ≡ Base
Loop i .fst = notEq i
Loop i .snd = ∥∥-isPropDep (Bool ≃_) (Base .snd) (Base .snd) notEq i

private
  notEq² : Square notEq refl refl notEq
  notEq² = involPath² {f = not} notnot

Loop² : Square Loop refl refl Loop
Loop² i j .fst = notEq² i j
Loop² i j .snd
  = isPropDep→isSetDep' (∥∥-isPropDep (Bool ≃_))
      notEq² (cong snd Loop) refl refl (cong snd Loop) i j

isGroupoidBinary : isGroupoid (Binary ℓ)
isGroupoidBinary
  = Embedding-into-hLevel→hLevel 2
      (map-snd isBinary→isSet , isEmbedding→hasPropFibers BinaryEmbedding)
      (isOfHLevelTypeOfHLevel 2)
