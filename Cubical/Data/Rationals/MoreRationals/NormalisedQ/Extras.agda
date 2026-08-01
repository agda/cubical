
module Cubical.Data.Rationals.MoreRationals.NormalisedQ.Extras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat
open import Cubical.Data.Nat.GCD using (isPropIsGCD)
open import Cubical.Data.Nat.Coprime using (areCoprime)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ; 1+_)
open import Cubical.Data.Sigma using (Σ≡Prop)

open import Cubical.Data.Int as ℤ renaming (abs to absℤ)
open import Cubical.Data.Int.MoreInts.QuoInt using () renaming
  (abs to abs'; ℤ→Int to Int→ℤ; Int→ℤ to ℤ→Int; ℤ→Int→ℤ to Int→ℤ→Int)
open import Cubical.Data.Rationals.MoreRationals.SigmaQ using (Quoℚ≡Sigmaℚ)
  renaming (ℚ to Sigmaℚ; isSetℚ to isSetSigmaℚ)
open import Cubical.Data.Rationals.MoreRationals.QuoQ using () renaming
  (ℚ to Quoℚ; discreteℚ to discreteQuoℚ; [_] to Quo[_]; Quoℚ≡ℚ to Quoℚ≡Rationalsℚ)
open import Cubical.Data.Rationals as Rationals
  renaming (ℚ to Rationalsℚ; [_] to Rationals[_])

open import Cubical.Data.Rationals.MoreRationals.NormalisedQ.Base

-- Normalisedℚ using other rationals --

-- Helper functions

private
  coprime≡lemma : {z : ℤ}{n : ℕ} →
    areCoprime (absℤ z , ℕ.suc n) ≡ areCoprime (abs' (ℤ→Int z) , ℕ₊₁→ℕ (1+ n))
  coprime≡lemma {z}{n} =
    cong₂ (λ u v → areCoprime (u , v)) (abs≡abs {z}) (refl {x = ℕ.suc n})
    where
      abs≡abs : {z' : ℤ} → absℤ z' ≡ (abs' (ℤ→Int z'))
      abs≡abs z'@{pos n'} = refl {x = absℤ z'}
      abs≡abs z'@{negsuc n'} = refl {x = absℤ z'}

ℚ→Sigmaℚ : ℚ → Sigmaℚ
ℚ→Sigmaℚ ((z , n) , copr) =
  (ℤ→Int z , (1+ n)) , transport (coprime≡lemma {z}{n}) copr

Sigmaℚ→ℚ : Sigmaℚ → ℚ
Sigmaℚ→ℚ ((z , (1+ n)) , copr) =
  (Int→ℤ z , n) , transport⁻ (coprime≡lemma {Int→ℤ z}{n}) areCopr
  where
    areCopr : areCoprime (abs' (ℤ→Int (Int→ℤ z)) , ℕ₊₁→ℕ (1+ n))
    areCopr = transport (cong (λ u → areCoprime ((abs' u) , ℕ₊₁→ℕ (1+ n)))
                          (sym (Int→ℤ→Int z))) copr

ℚ≡Sigmaℚ : ℚ ≡ Sigmaℚ
ℚ≡Sigmaℚ =
  isoToPath (iso ℚ→Sigmaℚ Sigmaℚ→ℚ (λ b → qssq b) λ a → ℚ-unique₋₁ (sqqsHlp a) refl)
  where
    sqqsHlp : ∀ b → ↥ (Sigmaℚ→ℚ (ℚ→Sigmaℚ b)) ≡ ↥ b
    sqqsHlp ((pos n , d-1) , sn) = refl
    sqqsHlp ((negsuc n , d-1) , sn) = refl
    Sigmaℚ-def : ∀ (a b : Sigmaℚ) → fst a ≡ fst b → a ≡ b
    Sigmaℚ-def (fst₁ , snd₁) (fst₂ , snd₂) ab = Σ≡Prop (λ x  → isPropIsGCD) ab
    Sigmaℚ-def' : ∀ (a b : Sigmaℚ) → fst (fst a) ≡ fst (fst b) →
      snd (fst a) ≡ snd (fst b) → a ≡ b
    Sigmaℚ-def' a b numerators denominators = Sigmaℚ-def a b
      λ i → (numerators i) , (denominators i)
    qssq : ∀ a → ℚ→Sigmaℚ (Sigmaℚ→ℚ a) ≡ a
    qssq ((z , d) , copr) = Sigmaℚ-def' (ℚ→Sigmaℚ (Sigmaℚ→ℚ ((z , d) , copr)))
                                        ((z , d) , copr) (Int→ℤ→Int z) refl

-- Sigmaℚ gives us:
isSetℚ' : isSet ℚ
isSetℚ' = transport⁻ (cong isSet ℚ≡Sigmaℚ) isSetSigmaℚ

-- We also have Quoℚ:
Quoℚ≡ℚ : Quoℚ ≡ ℚ
Quoℚ≡ℚ = Quoℚ≡Sigmaℚ ∙ (sym ℚ≡Sigmaℚ)

Quoℚ→ℚ : Quoℚ → ℚ
Quoℚ→ℚ q = transport Quoℚ≡ℚ q

-- Quoℚ gives us (alternative proof):
discreteℚ' : Discrete ℚ
discreteℚ' = isoPresDiscrete (pathToIso Quoℚ≡ℚ) discreteQuoℚ

-- We also have Rationalsℚ:
ℚ≡Rationalsℚ : ℚ ≡ Rationalsℚ
ℚ≡Rationalsℚ = sym Quoℚ≡ℚ ∙ Quoℚ≡Rationalsℚ

Rationalsℚ→ℚ : Rationalsℚ → ℚ
Rationalsℚ→ℚ q = transport⁻ ℚ≡Rationalsℚ q

ℚ→Rationalsℚ : ℚ → Rationalsℚ
ℚ→Rationalsℚ q = transport ℚ≡Rationalsℚ q

-- Rationalsℚ gives us:
[↥↧₊₁]≡Rationalsℚ : ∀ (p : ℚ) → Rationals[ (↥ p) , (↧₊₁ p) ] ≡ ℚ→Rationalsℚ p
[↥↧₊₁]≡Rationalsℚ ((pos n , d-1) , c) = refl
[↥↧₊₁]≡Rationalsℚ ((negsuc n , d-1) , c) = refl

[↥↧₊₁]≡ℚ : ∀ (q : ℚ) → Rationalsℚ→ℚ (Rationals[ (↥ q) , (↧₊₁ q) ]) ≡ q
[↥↧₊₁]≡ℚ q = (cong Rationalsℚ→ℚ ([↥↧₊₁]≡Rationalsℚ q)) ∙
         (transport⁻Transport ℚ≡Rationalsℚ q)

≃-∼-def' : ∀ (p : ℚ) (q : ℚ) → (p ≃ q) ≡ ((↥ p , ↧₊₁ p) ∼ (↥ q , ↧₊₁ q))
≃-∼-def' p q = sym (≃-def p q)

-- An alternative proof of ≃→≡
≃→≡' : ∀ {p q} → (p ≃ q) → p ≡ q
≃→≡' {p}{q} (*≡* x) = sym ([↥↧₊₁]≡ℚ p) ∙ cong Rationalsℚ→ℚ
 (transport⁻ (path∼ (↥ p , ↧₊₁ p) (↥ q , ↧₊₁ q)) x) ∙ ([↥↧₊₁]≡ℚ q)
