{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.coHomZero-map where

open import Cubical.ZCohomology.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.ZCohomology.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.ZCohomology.KcompPrelims


{-
This module contains a proof that addition in K₀ is just regular integer addition.
There is a lot of pattern matching going on, so the proof gets annoyingly long, which
is why I placed it in a separate module.
-}

addLemma : (a b : Int) → a +ₖ b ≡ (a +ℤ b)
addLemma a b = (λ i → ΩKn+1→Kn (cong ∣_∣ (looper a) ∙ cong ∣_∣ (looper b)))
             ∙ (λ i → ΩKn+1→Kn (congFunct ∣_∣ (looper a) (looper b) (~ i)))
             ∙ (λ i → ΩKn+1→Kn (cong ∣_∣ (looperId a b i)))
             ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 zero) (a +ℤ b)
  where 
  lemma10000 : (n : ℕ) → looper (pos (suc n)) ≡ loop* ∙ looper (pos n)
  lemma10000 zero = sym (lUnit loop*) ∙ rUnit loop*
  lemma10000 (suc n) = (λ i → (lemma10000 n i) ∙ loop*) ∙ sym (assoc loop* (looper (pos n)) loop*)

  lemma10001 : (a : Int) → looper (sucInt a) ≡ loop* ∙ looper a
  lemma10001 (pos n) = lemma10000 n
  lemma10001 (negsuc zero) = sym (rCancel loop*)
  lemma10001 (negsuc (suc zero)) = lUnit (sym loop*)
                                 ∙ (λ i → rCancel loop* (~ i) ∙ (sym loop*))
                                 ∙ sym (assoc loop* (sym loop*) (sym loop*))
  lemma10001 (negsuc (suc (suc n))) = cong (λ x → x ∙ (sym loop*)) (lemma10001 (negsuc (suc n)))
                                    ∙ sym (assoc loop* (looper (negsuc n) ∙ sym loop*) (sym loop*))

  lemma10002 : (a : Int) → looper (predInt a) ≡ sym loop* ∙ looper a
  lemma10002 (pos zero) = rUnit (sym loop*)
  lemma10002 (pos (suc n)) = lUnit (looper (pos n))
                           ∙ (λ i → lCancel loop* (~ i) ∙ (looper (pos n)))
                           ∙ sym (assoc (sym loop*) loop* (looper (pos n)))
                           ∙ λ i → sym loop* ∙ lemma10000 n (~ i)
  lemma10002 (negsuc zero) = refl
  lemma10002 (negsuc (suc n)) = (λ i → (lemma10002 (negsuc n) i) ∙ sym loop*) ∙ sym (assoc (sym loop*) (looper (negsuc n)) (sym loop*))

  sucIntPredInt : (a : Int) → sucInt (predInt a) ≡ a
  sucIntPredInt (pos zero) = refl
  sucIntPredInt (pos (suc n)) = refl
  sucIntPredInt (negsuc n) = refl

  looperId : (a b : Int) → looper a ∙ looper b ≡ looper (a +ℤ b)
  looperId (pos zero) b = sym (lUnit (looper b)) ∙ λ i → looper (pos0+ b i)
  looperId (pos (suc n)) (pos zero) = sym (rUnit (looper (pos (suc n))))
  looperId (pos (suc n)) (pos (suc m)) = (λ i → (lemma10000 n i) ∙ looper (pos (suc m)))
                                   ∙ sym (assoc loop* (looper (pos n)) (looper (pos (suc m))))
                                   ∙ (λ i → loop* ∙ looperId (pos n) (pos (suc m)) i)
                                   ∙ sym (lemma10001 (sucInt (pos n +pos m)))
                                   ∙ λ i → looper (sucInt (sucInt+pos m (pos n) i))
  looperId (pos (suc n)) (negsuc zero) = sym (assoc (looper (pos n)) loop* (sym loop*)) ∙ (λ i → looper (pos n) ∙ (rCancel loop* i)) ∙ sym (rUnit (looper (pos n))) 
  looperId (pos (suc n)) (negsuc (suc m)) = (λ i → (looper (pos n) ∙ loop*) ∙ lemma10002 (negsuc m) i)
                                          ∙ sym (assoc (looper (pos n)) loop* (sym loop* ∙ looper (negsuc m)))
                                          ∙ (λ i → looper (pos n) ∙ assoc loop* (sym loop*) (looper (negsuc m)) i)
                                          ∙ (λ i → looper (pos n) ∙ rCancel loop* i ∙ looper (negsuc m))
                                          ∙ (λ i → looper (pos n) ∙ lUnit (looper (negsuc m)) (~ i))
                                          ∙ looperId (pos n) (negsuc m)
                                          ∙ λ i → looper (predInt+negsuc m (pos (suc n)) (~ i))
  looperId (negsuc zero) (pos zero) = sym (rUnit (sym loop*))
  looperId (negsuc zero) (pos (suc n)) = (λ i → (sym loop*) ∙ lemma10001 (pos n) i)
                                       ∙ assoc (sym loop*) loop* (looper (pos n))
                                       ∙ (λ i → lCancel loop* i ∙ looper (pos n))
                                       ∙ sym (lUnit (looper (pos n)))
                                       ∙ (λ i → looper (sucIntPredInt (pos n) (~ i)))
                                       ∙ λ i → looper (sucInt (negsuc0+ (pos n) i))
  looperId (negsuc zero) (negsuc zero) = refl
  looperId (negsuc zero) (negsuc (suc n)) = assoc (sym loop*) (looper (negsuc n)) (sym loop*) ∙
                                            (λ i → looperId (negsuc zero) (negsuc n) i ∙ sym loop*) ∙
                                            (λ i → looper (negsuc zero +negsuc n) ∙ sym loop*) ∙
                                            (λ i → looper (negsuc0+ (negsuc n) (~ i)) ∙ sym loop*) ∙
                                            λ i → looper (predInt (negsuc0+ (negsuc n) i)) 
  looperId (negsuc (suc n)) b = (λ i → lemma10002 (negsuc n) i ∙ looper b)
                              ∙ sym (assoc (sym loop*) (looper (negsuc n)) (looper b))
                              ∙ (λ i → sym loop* ∙ looperId (negsuc n) b i)
                              ∙ sym (lemma10002 (negsuc n +ℤ b)) 
                              ∙ λ i → looper (predInt+ (negsuc n) b i)
