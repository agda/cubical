module Cubical.Data.Rationals.MoreRationals.SigmaQ.Extras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat as ℕ using (ℕ; suc)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ·₊₁-comm)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
import Cubical.HITs.SetQuotients as SetQuotient
open import Cubical.Data.Rationals.MoreRationals.QuoQ using ()
  renaming (ℚ to Quoℚ; discreteℚ to discreteQuoℚ; [_] to Quo[_];
    Quoℚ≡ℚ to Quoℚ≡Rationalsℚ)
open import Cubical.Data.Rationals as Rationals
  using (_∼_; path∼; isEquivRel∼; isProp∼; eq/; ℕ₊₁→ℤ)
  renaming (ℚ to Rationalsℚ; [_] to Rationals[_];
    isSetℚ to isSetRationalsℚ)
open import Cubical.Data.Rationals.MoreRationals.SigmaQ

-- instances may be placed here to avoid conflicts elsewhere:

instance
  nonZero-1/' : {q : ℚ} → {{nz : NonZero q}} → NonZero (1/ q)
  nonZero-1/' {(pos (suc m) , n) , c} ⦃ nz ⦄ = tt
  nonZero-1/' {(negsuc m , n) , c} ⦃ nz ⦄ = tt

-- Conversions between SigmaQ and RationalQ

[]-respects-∼ : ∀ (x y : ℤ × ℕ₊₁) → x ∼ y → [ x ] ≡ [ y ]
[]-respects-∼ (a , b) (c , d) p =
    sym (·[]CancelR {a} {b} d)
  ∙ (λ i → [ p i , ·₊₁-comm b d i ])
  ∙ ·[]CancelR {c} {d} b

normalise-∼ : ∀ a n → (↥ [ a , 1+ n ] , ↧₊₁ [ a , 1+ n ]) ∼ (a , 1+ n)
normalise-∼ a n = sym (*≃*ᵘ⁻¹ {a}{(↥ [ a , (1+ n) ])}{n}
  {[ a , (1+ n) ] .fst .snd} (≡→≃ (≡↥↧₊₁ [ a , 1+ n ])))

Rationalsℚ→ℚ : Rationalsℚ → ℚ
Rationalsℚ→ℚ = SetQuotient.rec isSetℚ [_] []-respects-∼

ℚ→Rationalsℚ : ℚ → Rationalsℚ
ℚ→Rationalsℚ q = Rationals[ ↥ q , ↧₊₁ q ]

toRat-fromRat : ∀ q → ℚ→Rationalsℚ (Rationalsℚ→ℚ q) ≡ q
toRat-fromRat = SetQuotient.elimProp (λ _ → isSetRationalsℚ _ _)
  (λ { (a , 1+ n) → eq/ _ _ (normalise-∼ a n) })

fromRat-toRat : ∀ q → Rationalsℚ→ℚ (ℚ→Rationalsℚ q) ≡ q
fromRat-toRat q = sym (≡↥↧₊₁ q)

ℚ≡Rationalsℚ : ℚ ≡ Rationalsℚ
ℚ≡Rationalsℚ = isoToPath
  (iso ℚ→Rationalsℚ Rationalsℚ→ℚ toRat-fromRat fromRat-toRat)

Quoℚ≡ℚ : Quoℚ ≡ ℚ
Quoℚ≡ℚ = Quoℚ≡Rationalsℚ ∙ sym ℚ≡Rationalsℚ

Quoℚ→ℚ : Quoℚ → ℚ
Quoℚ→ℚ = Rationalsℚ→ℚ ∘ transport Quoℚ≡Rationalsℚ

[↥↧₊₁]≡Rationalsℚ : ∀ (p : ℚ) →
  Rationals[ (↥ p) , (↧₊₁ p) ] ≡ ℚ→Rationalsℚ p
[↥↧₊₁]≡Rationalsℚ p = refl

[↥↧₊₁]≡ℚ : ∀ (q : ℚ) → Rationalsℚ→ℚ (Rationals[ (↥ q) , (↧₊₁ q) ]) ≡ q
[↥↧₊₁]≡ℚ q = cong Rationalsℚ→ℚ ([↥↧₊₁]≡Rationalsℚ q) ∙ fromRat-toRat q

≃-∼-def' : ∀ (p : ℚ) (q : ℚ) → (p ≃ q) ≡ ((↥ p , ↧₊₁ p) ∼ (↥ q , ↧₊₁ q))
≃-∼-def' p q = sym (≃-def p q)

≃→≡' : ∀ {p q} → (p ≃ q) → p ≡ q
≃→≡' {p}{q} (*≡* x) = sym ([↥↧₊₁]≡ℚ p) ∙ cong Rationalsℚ→ℚ
 (transport⁻ (path∼ (↥ p , ↧₊₁ p) (↥ q , ↧₊₁ q)) x) ∙ [↥↧₊₁]≡ℚ q
