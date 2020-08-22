{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.DiffInt.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

open import Cubical.Data.DiffInt.Base
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients

open BinaryRelation

relIsEquiv : isEquivRel rel
relIsEquiv = equivRel {A = ℕ × ℕ} relIsRefl relIsSym relIsTrans
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


module _ where
  isSetℤ : isSet ℤ
  isSetℤ = squash/

  isSetℤ→ℤ : isSet (ℤ → ℤ)
  isSetℤ→ℤ = isOfHLevelΠ 2 λ _ → isSetℤ

  _+ℤ_ : ℤ → ℤ → ℤ
  _+ℤ_ = rec2 isSetℤ
              (λ {(n , k) (m , l) → [ (n + m , k + l) ]})
              (λ {a b c a₁+b₂≡b₁+a₂ →
                eq/ _ _
                    (p a b c a₁+b₂≡b₁+a₂)})
              λ {a b c b₁+c₂≡c₁+b₂ →
                eq/ _ _
                    (q a b c b₁+c₂≡c₁+b₂)}
            where
              p : ((a₁ , a₂) : ℕ × ℕ) → ((b₁ , b₂) : ℕ × ℕ) → ((c₁ , c₂) : ℕ × ℕ) → _ ≡ _
                  → (a₁ + c₁) + (b₂ + c₂) ≡ (b₁ + c₁) + (a₂ + c₂)
              p (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) a₁+b₂≡b₁+a₂
                = (a₁ + c₁) + (b₂ + c₂) ≡⟨ cong (λ u → u + (b₂ + c₂)) (+-comm a₁ c₁) ⟩
                  (c₁ + a₁) + (b₂ + c₂) ≡⟨ sym (+-assoc c₁ _ _) ⟩
                  c₁ + (a₁ + (b₂ + c₂)) ≡⟨ cong (λ u → c₁ + u) (+-assoc a₁ _ _) ⟩
                  c₁ + ((a₁ + b₂) + c₂) ≡⟨ cong (λ u → c₁ + (u + c₂)) a₁+b₂≡b₁+a₂ ⟩
                  c₁ + ((b₁ + a₂) + c₂) ≡⟨ cong (λ u → c₁ + u) (sym (+-assoc b₁ _ _)) ⟩
                  c₁ + (b₁ + (a₂ + c₂)) ≡⟨ +-assoc c₁ _ _ ⟩
                  (c₁ + b₁) + (a₂ + c₂) ≡⟨ cong (λ u → u + (a₂ + c₂)) (+-comm c₁ b₁) ⟩
                  (b₁ + c₁) + (a₂ + c₂) ∎
              q : ((a₁ , a₂) : ℕ × ℕ) → ((b₁ , b₂) : ℕ × ℕ) → ((c₁ , c₂) : ℕ × ℕ) → _ ≡ _
                  → (a₁ + b₁) + (a₂ + c₂) ≡ (a₁ + c₁) + (a₂ + b₂)
              q (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) b₁+c₂≡c₁+b₂
                = (a₁ + b₁) + (a₂ + c₂) ≡⟨ cong (λ u → u + (a₂ + c₂)) (+-comm a₁ b₁) ⟩
                  (b₁ + a₁) + (a₂ + c₂) ≡⟨ cong (λ u → (b₁ + a₁) + u) (+-comm a₂ _)  ⟩
                  (b₁ + a₁) + (c₂ + a₂) ≡⟨ p (b₁ , b₂) _ _ b₁+c₂≡c₁+b₂ ⟩
                  (c₁ + a₁) + (b₂ + a₂) ≡⟨ cong (λ u → (c₁ + a₁) + u) (+-comm b₂ _) ⟩
                  (c₁ + a₁) + (a₂ + b₂) ≡⟨ cong (λ u → u + (a₂ + b₂)) (+-comm c₁ a₁) ⟩
                  (a₁ + c₁) + (a₂ + b₂) ∎

  +ℤ-assoc : (a b c : ℤ)
             → a +ℤ (b +ℤ c) ≡ (a +ℤ b) +ℤ c
  +ℤ-assoc = elimProp3 (λ _ _ _ → isSetℤ _ _)
                       λ {(a₁ , a₂) (b₁ , b₂) (c₁ , c₂) i
                        → [ +-assoc a₁ b₁ c₁ i , +-assoc a₂ b₂ c₂ i ]}

  +ℤ-comm : (a b : ℤ)
             → a +ℤ b ≡ b +ℤ a
  +ℤ-comm = elimProp2 (λ _ _ → isSetℤ _ _)
                       λ {(a₁ , a₂) (b₁ , b₂) i
                       → [ +-comm a₁ b₁ i , +-comm a₂ b₂ i ]}

  0ℤ : ℤ
  0ℤ = [ (0 , 0) ]

  1ℤ : ℤ
  1ℤ = [ (1 , 0) ]

  +ℤ-rid : (a : ℤ) → a +ℤ 0ℤ ≡ a
  +ℤ-rid = elimProp (λ _ → isSetℤ _ _)
                    λ {(a₁ , a₂) i → [ +-zero a₁ i , +-zero a₂ i ]}
