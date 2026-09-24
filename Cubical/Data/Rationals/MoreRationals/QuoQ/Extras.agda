module Cubical.Data.Rationals.MoreRationals.QuoQ.Extras where

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Int.MoreInts.QuoInt renaming (_·_ to _ℤ·_)
open import Cubical.Data.Fast.Int as Int renaming (ℤ to Int)
open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Binary.Base
open BinaryRelation
open import Cubical.Data.Rationals as Rationals renaming (_∼_ to _Rationals∼_)
open import Cubical.Data.Rationals.MoreRationals.QuoQ.Base as Quo

iso/rHlp : ∀ (zn : ℤ × ℕ₊₁) → (Int→ℤ (ℤ→Int (fst zn)) , snd zn) ∼ (fst zn , snd zn)
iso/rHlp (z , n) = ∼≡-lemma (Int→ℤ (ℤ→Int z)) z n (ℤ→Int→ℤ z)
  where
    ∼≡-lemma : ∀ (a a' : ℤ) → (b : ℕ₊₁) → a ≡ a' → (a , b) ∼ (a' , b)
    ∼≡-lemma a a' b aa' i = (Quo.isEquivRel∼ .isEquivRel.reflexive) ((aa' i) , b) i

Int≡Int→ℤ·≡ℤ· : ∀ x y → x Int.· (Rationals.ℕ₊₁→ℤ y) ≡ ℤ→Int ((Int→ℤ x) ℤ· (Quo.ℕ₊₁→ℤ y))
Int≡Int→ℤ·≡ℤ· x y = sym (
     ℤ→IntIsHom· (Int→ℤ x) (Quo.ℕ₊₁→ℤ y)
  ∙∙ Int.·≡·f (ℤ→Int (Int→ℤ x)) (Rationals.ℕ₊₁→ℤ y)
  ∙∙ congL Int._·_ (Int→ℤ→Int x))

∼'→R* : ∀ u v → (u Rationals∼ v) → R* {ER = Quo.isEquivRel∼}
                                {iso/r = iso/R (λ x → ℤ→Int (fst x) , (snd x))
                                  (λ x → (Int→ℤ (fst x)) , (snd x)) λ u → iso/rHlp u} u v
∼'→R* (a , b) (c , d) R =
  sym (ℤ→Int→ℤ (Int→ℤ a ℤ· Quo.ℕ₊₁→ℤ d)) ∙
  (cong Int→ℤ (sym (Int≡Int→ℤ·≡ℤ· a d) ∙ R ∙ Int≡Int→ℤ·≡ℤ· c b)) ∙
  ℤ→Int→ℤ (Int→ℤ c ℤ· Quo.ℕ₊₁→ℤ b)

R*→∼' : ∀ u v → R* {ER = Quo.isEquivRel∼} {iso/r = iso/R (λ x → ℤ→Int (fst x) , (snd x))
           (λ x → (Int→ℤ (fst x)) , (snd x)) λ u → iso/rHlp u} u v → (u Rationals∼ v)
R*→∼' (a , b) (c , d) R* = Int≡Int→ℤ·≡ℤ· a d ∙ (cong ℤ→Int R*) ∙ sym (Int≡Int→ℤ·≡ℤ· c b)

module EqualityQ where
  -- Equality of Quo ℚ and Rationals ℚ
  Quoℚ≡ℚ : Quo.ℚ ≡ Rationals.ℚ
  Quoℚ≡ℚ = quotientEqualityLemma {ER = Quo.isEquivRel∼ }
              {iso/r = iso/R (λ x → ℤ→Int (fst x) , (snd x))
              (λ x → (Int→ℤ (fst x)) , (snd x)) λ a → iso/rHlp a} ∙
                sym (A/R≡A/R' ∼'→R* R*→∼')
