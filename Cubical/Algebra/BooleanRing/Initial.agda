{-# OPTIONS --safe #-}

module Cubical.Algebra.BooleanRing.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Algebra.BooleanRing.Base
open import Cubical.Data.Bool renaming (elim to bool-ind)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module _ where
  open BooleanStr

  BoolBRStr : BooleanStr Bool
  BoolBRStr .𝟘 = false
  BoolBRStr .𝟙 = true
  BoolBRStr ._+_ = _⊕_
  BoolBRStr ._·_ = _and_
  BoolBRStr .-_ x = x
  BoolBRStr .isBooleanRing = record
    { isCommRing = makeIsCommRing isSetBool ⊕-assoc ⊕-identityʳ
              (bool-ind refl refl) ⊕-comm and-assoc and-identityʳ
              (bool-ind (λ _ _ → refl) λ _ _ → refl) and-comm
    ; ·Idem = bool-ind refl refl
    }

BoolBR : BooleanRing ℓ-zero
BoolBR = Bool , BoolBRStr

BoolCR : CommRing ℓ-zero
BoolCR = BooleanRing→CommRing BoolBR

module _ {ℓ : Level} (B : BooleanRing ℓ) where
  private
    B' = BooleanRing→CommRing B

  open CommRingStr (snd B')
  open BooleanAlgebraStr B
  open IsCommRingHom

  BoolBR→BAMap : Bool → ⟨ B ⟩
  BoolBR→BAMap = bool-ind 1r 0r

  BoolBR→BAIsCommRingHom : IsCommRingHom (snd BoolCR) BoolBR→BAMap (snd B')
  pres0 BoolBR→BAIsCommRingHom = refl
  pres1 BoolBR→BAIsCommRingHom = refl
  pres+ BoolBR→BAIsCommRingHom =
    λ { false false → solve! B'
    ; false true  → solve! B'
    ; true  false → solve! B'
    ; true  true  → sym characteristic2
    }
  pres· BoolBR→BAIsCommRingHom =
    λ { false false → solve! B'
    ; false true  → solve! B'
    ; true  false → solve! B'
    ; true  true  → solve! B'
    }
  pres- BoolBR→BAIsCommRingHom false = solve! B'
  pres- BoolBR→BAIsCommRingHom true  = -IsId :> 1r ≡ - 1r

  BoolBR→ : BoolHom BoolBR B
  BoolBR→ = BoolBR→BAMap , BoolBR→BAIsCommRingHom

  BoolBR→IsUnique : (f : BoolHom BoolBR B) → (fst f) ≡ fst (BoolBR→)
  BoolBR→IsUnique f =  funExt (bool-ind (pres1 (snd f)) (pres0 (snd f)))
