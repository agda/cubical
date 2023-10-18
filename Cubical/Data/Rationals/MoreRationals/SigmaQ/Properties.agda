{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreRationals.SigmaQ.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int.MoreInts.QuoInt
import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime

open import Cubical.Data.Rationals.MoreRationals.QuoQ as Quo using (ℕ₊₁→ℤ)
import Cubical.Data.Rationals.MoreRationals.SigmaQ.Base as Sigma


reduce : Quo.ℚ → Sigma.ℚ
reduce = SetQuotient.rec Sigma.isSetℚ Sigma.[_]
  (λ { (a , b) (c , d) p →   sym (Sigma.[]-cancelʳ (a , b) d)
                           ∙ (λ i → Sigma.[ p i , ·₊₁-comm b d i ])
                           ∙ Sigma.[]-cancelʳ (c , d) b })

private
  toCoprime-eq₁ : ∀ s ((a , b) : ℕ × ℕ₊₁)
                  → signed s (toCoprime (a , b) .fst) · ℕ₊₁→ℤ b
                  ≡ signed s a · ℕ₊₁→ℤ (toCoprime (a , b) .snd)
  toCoprime-eq₁ s (a , b) =
    signed s c₁ · ℕ₊₁→ℤ b              ≡⟨ ·-signed-pos c₁ (ℕ₊₁→ℕ b) ⟩
    signed s (c₁ ℕ.· ℕ₊₁→ℕ b)          ≡[ i ]⟨ signed s (c₁ ℕ.· p₂ (~ i)) ⟩
    signed s (c₁ ℕ.· (ℕ₊₁→ℕ c₂ ℕ.· d)) ≡[ i ]⟨ signed s (c₁ ℕ.· ℕ.·-comm (ℕ₊₁→ℕ c₂) d i) ⟩
    signed s (c₁ ℕ.· (d ℕ.· ℕ₊₁→ℕ c₂)) ≡[ i ]⟨ signed s (ℕ.·-assoc c₁ d (ℕ₊₁→ℕ c₂) i) ⟩
    signed s ((c₁ ℕ.· d) ℕ.· ℕ₊₁→ℕ c₂) ≡[ i ]⟨ signed s (p₁ i ℕ.· ℕ₊₁→ℕ c₂) ⟩
    signed s (a ℕ.· ℕ₊₁→ℕ c₂)          ≡⟨ sym (·-signed-pos a (ℕ₊₁→ℕ c₂)) ⟩
    signed s a · ℕ₊₁→ℤ c₂ ∎
    where open ToCoprime (a , b)

[]-reduce : ∀ x → Quo.[ reduce x .fst ] ≡ x
[]-reduce = SetQuotient.elimProp (λ _ → Quo.isSetℚ _ _)
  (λ { (signed s a , b) → Quo.eq/ _ _ (toCoprime-eq₁ s (a , b))
     ; (posneg i , b) j → isSet→isSet' Quo.isSetℚ
         (Quo.eq/ (fst (reduce Quo.[ pos 0 , b ])) (pos 0 , b) (toCoprime-eq₁ spos (0 , b)))
         (Quo.eq/ (fst (reduce Quo.[ neg 0 , b ])) (neg 0 , b) (toCoprime-eq₁ sneg (0 , b)))
         (λ i → Quo.[ reduce (Quo.[ posneg i , b ]) .fst ]) (λ i → Quo.[ posneg i , b ]) i j })

private
  toCoprime-eq₂ : ∀ s ((a , b) : ℕ × ℕ₊₁) (cp : areCoprime (a , ℕ₊₁→ℕ b))
                  → Sigma.signedPair s (toCoprime (a , b)) ≡ Sigma.signedPair s (a , b)
  toCoprime-eq₂ s (a , b) cp i = Sigma.signedPair s (toCoprime-idem (a , b) cp i)

reduce-[] : ∀ x → reduce Quo.[ x .fst ] ≡ x
     -- equivalent to: Sigma.[ s .fst ] ≡ x
reduce-[] ((signed s a , b) , cp) =
  Σ≡Prop (λ _ → isPropIsGCD) (toCoprime-eq₂ s (a , b) cp)
reduce-[] ((posneg i , b) , cp) j =
  isSet→isSet' Sigma.isSetℚ
    (Σ≡Prop (λ _ → isPropIsGCD) (toCoprime-eq₂ spos (0 , b) cp))
    (Σ≡Prop (λ _ → isPropIsGCD) (toCoprime-eq₂ sneg (0 , b) cp))
    (λ i → Sigma.[ posneg i , b ]) (λ i → (posneg i , b) , cp) i j


Quoℚ-iso-Sigmaℚ : Iso Quo.ℚ Sigma.ℚ
Iso.fun Quoℚ-iso-Sigmaℚ = reduce
Iso.inv Quoℚ-iso-Sigmaℚ = Quo.[_] ∘ fst
Iso.rightInv Quoℚ-iso-Sigmaℚ = reduce-[]
Iso.leftInv  Quoℚ-iso-Sigmaℚ = []-reduce

Quoℚ≃Sigmaℚ : Quo.ℚ ≃ Sigma.ℚ
Quoℚ≃Sigmaℚ = isoToEquiv Quoℚ-iso-Sigmaℚ

Quoℚ≡Sigmaℚ : Quo.ℚ ≡ Sigma.ℚ
Quoℚ≡Sigmaℚ = isoToPath Quoℚ-iso-Sigmaℚ
