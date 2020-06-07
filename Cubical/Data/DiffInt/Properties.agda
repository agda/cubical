{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.DiffInt.Base
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Bool

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients

open BinaryRelation

relIsEquiv : isEquivRel rel
relIsEquiv = EquivRel {A = ℕ × ℕ} relIsRefl relIsSym relIsTrans
  where
    relIsRefl : isRefl rel
    relIsRefl (a0 , a1) = refl

    relIsSym : isSym rel
    relIsSym (a0 , a1) (b0 , b1) p = sym p

    relIsTrans : isTrans rel
    relIsTrans (a0 , a1) (b0 , b1) (c0 , c1) p0 p1 =
      inj-m+ {m = (b0 + b1)} ((b0 + b1) + (a0 + c1) ≡⟨ +-assoc (b0 + b1) a0 c1  ⟩
            ((b0 + b1) + a0) + c1 ≡[ i ]⟨ +-comm b0 b1 i + a0   + c1 ⟩
            ((b1 + b0) + a0) + c1 ≡[ i ]⟨ +-comm (b1 + b0) a0 i + c1 ⟩
            (a0 + (b1 + b0)) + c1 ≡[ i ]⟨ +-assoc a0 b1 b0 i    + c1 ⟩
            (a0 + b1) + b0 + c1 ≡⟨ sym (+-assoc (a0 + b1) b0 c1) ⟩
            (a0 + b1) + (b0 + c1) ≡⟨ cong (λ p → p . fst + p .snd) (transport ΣPath≡PathΣ (p0 , p1))⟩
            (b0 + a1) + (c0 + b1) ≡⟨ sym (+-assoc b0 a1 (c0 + b1))⟩
            b0 + (a1 + (c0 + b1)) ≡[ i ]⟨ b0 + (a1 + +-comm c0 b1 i) ⟩
            b0 + (a1 + (b1 + c0)) ≡[ i ]⟨ b0 + +-comm a1 (b1 + c0) i ⟩
            b0 + ((b1 + c0) + a1) ≡[ i ]⟨ b0 + +-assoc b1 c0 a1 (~ i) ⟩
            b0 + (b1 + (c0 + a1)) ≡⟨ +-assoc b0 b1 (c0 + a1)⟩
            (b0 + b1) + (c0 + a1) ∎ )

relIsProp : BinaryRelation.isPropValued rel
relIsProp a b x y = isSetℕ _ _ _ _

discreteℤ : Discrete ℤ
discreteℤ = discreteSetQuotients (discreteΣ discreteℕ λ _ → discreteℕ) relIsProp relIsEquiv (λ _ _ → discreteℕ _ _)

private
  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 6) ]) ≡ true
  _ = refl

  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 7) ]) ≡ false
  _ = refl
