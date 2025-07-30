{-# OPTIONS --postfix-projections #-}

module Cubical.Data.FinSet.Binary.Large where

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ : Level

isBinary : Type ℓ → Type ℓ
isBinary B = ∥ Bool ≃ B ∥₁

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
Base .snd = ∣ idEquiv Bool ∣₁

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
      (map-snd isBinary→isSet , BinaryEmbedding)
      (isOfHLevelTypeOfHLevel 2)

record BinStructure (B : Type ℓ) : Type ℓ where
  field
    base : B
    loop : base ≡ base
    loop² : Square loop refl refl loop
    trunc : isGroupoid B

structure₀ : BinStructure (Binary ℓ-zero)
structure₀ .BinStructure.base = Base
structure₀ .BinStructure.loop = Loop
structure₀ .BinStructure.loop² = Loop²
structure₀ .BinStructure.trunc = isGroupoidBinary

module Parameterized (B : Type ℓ) where
  Baseᴾ : Bool ≃ B → Binary ℓ
  Baseᴾ P = B , ∣ P ∣₁

  Loopᴾ : (P Q : Bool ≃ B) → Baseᴾ P ≡ Baseᴾ Q
  Loopᴾ P Q i = λ where
      .fst → ua first i
      .snd → ∥∥-isPropDep (Bool ≃_) ∣ P ∣₁ ∣ Q ∣₁ (ua first) i
    where
    first : B ≃ B
    first = compEquiv (invEquiv P) Q

  Loopᴾ² : (P Q R : Bool ≃ B) → Square (Loopᴾ P Q) (Loopᴾ P R) refl (Loopᴾ Q R)
  Loopᴾ² P Q R i = Σ≡Prop (λ _ → squash₁) (S i)
    where
    PQ : B ≃ B
    PQ = compEquiv (invEquiv P) Q
    PR : B ≃ B
    PR = compEquiv (invEquiv P) R
    QR : B ≃ B
    QR = compEquiv (invEquiv Q) R
    Q-Q : Bool ≃ Bool
    Q-Q = compEquiv Q (invEquiv Q)

    PQRE : compEquiv PQ QR ≡ PR
    PQRE = compEquiv PQ QR
             ≡[ i ]⟨ compEquiv-assoc (invEquiv P) Q QR (~ i) ⟩
           compEquiv (invEquiv P) (compEquiv Q QR)
             ≡[ i ]⟨ compEquiv (invEquiv P) (compEquiv-assoc Q (invEquiv Q) R i) ⟩
           compEquiv (invEquiv P) (compEquiv Q-Q R)
             ≡[ i ]⟨ compEquiv (invEquiv P) (compEquiv (invEquiv-is-rinv Q i) R) ⟩
           compEquiv (invEquiv P) (compEquiv (idEquiv _) R)
             ≡[ i ]⟨ compEquiv (invEquiv P) (compEquivIdEquiv R i) ⟩
           PR ∎

    PQR : ua PQ ∙ ua QR ≡ ua PR
    PQR = ua PQ ∙ ua QR
            ≡[ i ]⟨ uaCompEquiv PQ QR (~ i) ⟩
          ua (compEquiv PQ QR)
            ≡⟨ cong ua PQRE ⟩
          ua PR ∎

    S : Square (ua PQ) (ua PR) refl (ua QR)
    S i j
      = hcomp (λ k → λ where
            (j = i0) → B
            (i = i0) → compPath-filler (ua PQ) (ua QR) (~ k) j
            (i = i1) → ua PR j
            (j = i1) → ua QR (i ∨ ~ k))
          (PQR i j)
