{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-1 where


open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification hiding (elim)
open import Cubical.Data.Int hiding (_+_ ; _-_ ; +-comm )
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

open import Cubical.HITs.Pushout
open import Cubical.Data.HomotopyGroup
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

private
  0* : ℕ₋₂
  0* = ℕ→ℕ₋₂ 0

private
  Lemma861-fibId : ∀{ℓ} (n : ℕ₋₂) (k : ℕ) (f : A → B) →
                   (is- n -Connected f) →
                   (P : B → HLevel ℓ (((suc k) + (2+ n))))
                   (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) →
                   (pf : ((x : B) → isOfHLevel (((k) + (2+ n))) (fst a x ≡ fst b x))) → -- silly, but needed to be able to state the lemma
                   (a ≡ b) ≡ (fiber (indConFun {k = -2+ (k + (2+ n)) } f (λ x → ((fst a) x ≡ (fst b) x ) , pf x ))
                                    (λ x → ((snd a) x) ∙ (sym ((snd b) x))))
  Lemma861-fibId {A = A} {B = B} n k f isCon P l (g , p) (h , q)  pf = ua (compEquiv (helper1 l (g , p) (h , q)) (helper2 l (g , p) (h , q))) ∙
                                                                          (λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper3 l (g , p) (h , q) r j)) ∙
                                                                          λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper4 l (g , p) (h , q) r j)
      where
      helper1 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (a ≡ b) ≃ Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)
      helper1 l a b = invEquiv Σ≡

      helper2 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)) ≃ Σ ((x : B) → (fst a) x ≡ (fst b) x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)
      helper2 l (g , p) (h , q) = isoToEquiv (iso lrFun  rlFun (λ b → refl) λ b → refl) where
        lrFun : (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q) → Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q
        lrFun (a , b) = funExt⁻ a , b
        rlFun : (Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q) → (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q)
        rlFun (a , b) = (funExt a) , b

      helper3 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (r : (x : B) → (fst a) x ≡ (fst b) x) → (PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)) ≡ ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) )
      helper3 l (g , p) (h , q) r j = hcomp (λ k → λ{ (j = i0) → (PathP (λ i → (x : A) → r (f x) i ≡ l x) p λ x → (sym (lUnit (q x)) k ))
                                                    ; (j = i1) → throwAbout k})
                                            ((PathP (λ i → (x : A) → r (f x) (i ∧  ~ j) ≡ l x) p λ x → (λ i → r (f x) (~ j ∨ i)) ∙ (q x)))
          where
          throwAbout : (p ≡ λ x → r (f x) ∙ q x) ≡ ((x : A) → (((r (f x))) ≡ (p x) ∙ (sym (q x))))
          throwAbout = isoToPath (iso ((λ g x → transport (λ i → throwAboutHelper2 (sym (q x)) (p x) (r (f x)) i ) (funExt⁻ g x) ))
                                      (λ g → funExt λ x → transport (λ i → throwAboutHelper2 (sym (q x)) (p x) (r (f x)) (~ i) ) (g x))
                                      (λ b → funExt (λ x → transportTransport⁻ (throwAboutHelper2 (sym (q x)) (p x) (r (f x))) (b x)))
                                      λ b → λ j → funExt (λ x → (transport⁻Transport (throwAboutHelper2 (sym (q x)) (p x) (r (f x))) (λ i → b i x)) j))
            where

            symId : ∀{ℓ} {A : Type ℓ} (a b : A) → (a ≡ b) ≡ (b ≡ a)
            symId a b = isoToPath (iso sym sym (λ b → refl) λ b → refl)

            throwAboutHelper2 : ∀{ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p : a ≡ b) (q : a ≡ c) → (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r)
            throwAboutHelper2  {a = a} {b = b} = J (λ c r → (p : a ≡ b) (q : a ≡ c) →
                                                            (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r))
                                                   λ p q → (λ i → p ≡ rUnit q (~ i)) ∙
                                                           symId p q ∙ λ i → q ≡ (rUnit p i)

      helper4 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) →
                (r : (x : B) → (fst a) x ≡ (fst b) x) →
                ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) )
             ≡  ((λ (x : A) → r (f x)) ≡ (λ (x : A) → ((snd a) x) ∙ sym ((snd b) x)))
      helper4 l (h , q) (g , p) r = isoToPath (iso funExt funExt⁻ (λ b → refl) λ b → refl)


  Lemma861-fibId2 : ∀{ℓ} (n : ℕ₋₂) (k : ℕ) (f : A → B) →
                   (is-  n -Connected f) →
                   (P : B → HLevel ℓ ((suc k) + (2+ n))) →
                   (l : (a : A) → fst (P (f a))) →
                   (fiber (indConFun f P) l)
                  ≡ Σ ((b : B) → fst (P b)) λ g → ((a : A) → g (f a) ≡ l a)
  Lemma861-fibId2 n k f isCon P l = isoToPath (iso (λ p → fst p , funExt⁻ (snd p)) (λ p → fst p , funExt (snd p)) (λ b → refl) λ b → refl)

  Lemma861 : ∀{ℓ} (n : ℕ₋₂) (k : ℕ) (f : A → B) →
             (is- n -Connected f) →
             (P : B → HLevel ℓ (k + (2+ n))) →
             is- (-2+ k) -Truncated (indConFun {k = -2+ (k + (2+ n))} f P)
  Lemma861  {B = B} {ℓ = ℓ} n zero f iscon P = equiv-proof (conInd-i→ii f n iscon P)
    where
    helper : (n : ℕ₋₂) → -2+ (ℕ₋₂.n n + zero) ≡ n
    helper neg2 = refl
    helper neg1 = refl
    helper (ℕ→ℕ₋₂ n) i = ℕ→ℕ₋₂ (+-zero n i)
  {- Because of the different HLevels, we hve to repeat essentially the same proof three times... -}
  Lemma861 {A = A} {B = B} {ℓ = ℓ} neg2 (suc zero) f iscon P l = transport (λ i → isOfHLevel (suc (zero))
                                                                            (Lemma861-fibId2 neg2 (zero) f iscon P l (~ i)))
                                                                          λ a b → transport (λ i → isOfHLevel (zero)
                                                                                            (Lemma861-fibId neg2 (zero) f iscon P l a b
                                                                                                            (λ x → ((snd (P x)) (fst a x) (fst b x)) ,
                                                                                                              (λ y → isOfHLevelSuc 1 (snd (P x))
                                                                                                                                     (fst a x) (fst b x) _ _)) (~ i)))
                                                                                            ((Lemma861 neg2 (zero) f iscon
                                                                                                       ((λ x → ((fst a) x ≡ (fst b) x ) ,
                                                                                                        ((snd (P x)) (fst a x) (fst b x) ,
                                                                                                         (λ y → isOfHLevelSuc 1 (snd (P x))
                                                                                                                                (fst a x) (fst b x) _ _)) )))
                                                                                              λ z → (snd a z) ∙ sym (snd b z)) .fst
  Lemma861 {A = A} {B = B} {ℓ = ℓ} (-1+ n) (suc zero) f iscon P l = transport (λ i → isOfHLevel (suc (zero))
                                                                               (Lemma861-fibId2 (-1+ n) (zero) f iscon P l (~ i)))
                                                                             λ a b → transport (λ i → isOfHLevel (zero)
                                                                                               (Lemma861-fibId (-1+ n) (zero) f iscon P l a b
                                                                                                               (λ x → snd (P x) (fst a x) (fst b x)) (~ i)))
                                                                                               ((Lemma861 (-1+ n) (zero) f iscon
                                                                                                          ((λ x → ((fst a) x ≡ (fst b) x ) ,
                                                                                                            (snd (P x) (fst a x) (fst b x)) )))
                                                                                                 λ z → (snd a z) ∙ sym (snd b z)) .fst


  Lemma861 {A = A} {B = B} {ℓ = ℓ} n (suc (suc k)) f iscon P l = transport (λ i → isOfHLevel (suc (suc k))
                                                                            (Lemma861-fibId2 n (suc k) f iscon P l (~ i)))
                                                                          λ a b → transport (λ i → isOfHLevel (suc k)
                                                                                            (Lemma861-fibId n (suc k) f iscon P l a b
                                                                                                              (λ x → (snd (P x)) (fst a x) (fst b x)) (~ i)))
                                                                                            ((Lemma861 n (suc k) f iscon
                                                                                                       ((λ x → ((fst a) x ≡ (fst b) x ) ,
                                                                                                        (snd (P x)) (fst a x) (fst b x) )))
                                                                                             λ z → ((snd a z) ∙ sym (snd b z)))

{- The following more general versions are more useful -}
Lemma861Gen : ∀{ℓ} (n : ℕ₋₂) (k : ℕ) (expr : ℕ₋₂ → ℕ → ℕ) →
              ((expr n k) ≡ (k + (2+ n))) →
              (f : A → B) →
              (is- n -Connected f) →
              (P : B → HLevel ℓ (expr n k)) →
              is- (-2+ k) -Truncated (indConFun {k = -2+ (expr n k)} f P)
Lemma861Gen {A = A} {B = B} {ℓ = ℓ} n k expr path f iscon = transport (λ i → helper i) (Lemma861 n k f iscon)
  where
    helper : ((P : B → HLevel ℓ (k + (2+ n))) → is- -2+ k -Truncated (indConFun f P)) ≡ ((P : B → HLevel ℓ (expr n k)) → is- -2+ k -Truncated (indConFun f P))
    helper i = ((P : B → HLevel ℓ (path (~ i))) → is- -2+ k -Truncated (indConFun f P))

Lemma861GenNats : ∀{ℓ} (n k : ℕ) (expr : ℕ → ℕ → ℕ) →
                ((expr n k) ≡ k + (2+ ℕ→ℕ₋₂ n) ) →
                (f : A → B) →
                (is- (ℕ→ℕ₋₂ n) -Connected f) →
                (P : B → HLevel ℓ (expr n k)) →
                is- (-2+ k) -Truncated (indConFun {k = -2+ (expr n k)} f P)
Lemma861GenNats {A = A} {B = B} {ℓ = ℓ} n k expr path f iscon = transport (λ i → helper (~ i)) (Lemma861 (ℕ→ℕ₋₂ n) k f iscon)
  where
  helper : ((P : B → HLevel ℓ (expr n k)) → is- -2+ k -Truncated (indConFun f P)) ≡ ((P : B → HLevel ℓ (k + (2+ ℕ→ℕ₋₂ n))) → is- -2+ k -Truncated (indConFun f P))
  helper i = ((P : B → HLevel ℓ (path i)) → is- -2+ k -Truncated (indConFun f P))
