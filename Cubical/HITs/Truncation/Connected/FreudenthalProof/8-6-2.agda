{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-2 where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.Prelim
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-1
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.Data.Nat


private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


private
  transpHelper : {a b c : A} (r : b ≡ c) (q : a ≡ b) (p : a ≡ c) →
                 PathP (λ i → a ≡ r i) q p →
                 q ∙ r ≡ p
  transpHelper {a = a} {b = b} = J (λ c r →  (q : a ≡ b) (p : a ≡ c) → PathP (λ i → a ≡ r i) q p → q ∙ r ≡ p) λ p q path → sym (rUnit p) ∙ path

  pt-map : (A : Pointed ℓ) → Unit → typ A
  pt-map A x = pt A

  conOfpt-map : (A : Pointed ℓ) (n : ℕ) → (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) → is- (pred₋₂ (ℕ→ℕ₋₂ n)) -Connected (pt-map A)
  conOfpt-map A n conA = Lemma7-5-11 (pred₋₂ (ℕ→ℕ₋₂ n)) (transport (λ i → (is- pmId n (~ i) -ConnectedType (typ A))) conA)

  module prelims (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
                 (conA : is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A))
                 (conB : is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B))
                 (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m))))
                 (f : ((a : (typ A)) → fst (P a (pt B))))
                 (g : ((b : (typ B)) → fst (P (pt A) b)))  (p : f (pt A) ≡ g (pt B))
         where
         Q : (typ A) → Type (ℓ-max ℓ ℓ')
         Q a = Σ ((b : (typ B)) → fst (P a b )) λ k → f a ≡ k (pt B)

         f-map : (a : typ A) → ((b : typ B) → fst (P a b)) → fst (P a (pt B))
         f-map a g = indConFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n +  m))} (pt-map B) (P a) g tt



         QisFib : (a : typ A) → Q a  ≡ fiber (indConFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + m))} (pt-map B) (P a)) λ tt → (f a)
         QisFib a = helper ∙
                     isoToPath (iso (λ x → (fst x) , (funExt (λ y → snd x))) (λ x → (fst x) ,
                                    (cong (λ x → x tt) (snd x)))
                                    (λ x → refl)
                                    λ x → refl)
           where
           helper : Q a ≡ fiber (f-map a) (f a)
           helper = isoToPath (iso (λ x → (x .fst) , (sym (x .snd))) (λ b → (fst b) , (sym (snd b))) (λ a → refl) λ b → refl)

Lemma8-6-2 : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ) →
            (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) →
            (is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B)) →
            (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m)))) →
            (f : ((a : (typ A)) → fst (P a (pt B)))) →
            (g : ((b : (typ B)) → fst (P (pt A) b))) →
            (p : f (pt A) ≡ g (pt B)) →
            Σ ((a : typ A) → (b : typ B) → fst (P a b))
              λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b))
                       λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)

Lemma8-6-2 {ℓ = ℓ} {ℓ' = ℓ'} A B n zero conA conB P f g p =
          (λ a b → ((typesQ (pt A) .fst) a) .fst b) ,
          ((((λ a → sym ((typesQ (pt A)) .fst a .snd)))) ,
           (λ b → cong (λ x → (x .fst) b) (((typesQ) (pt A)) .snd))) ,
          (sym (transpHelper _ _ _ (cong (λ x → x .snd) (((typesQ) (pt A)) .snd))))
  where
  helper : (a : typ A) → isOfHLevel (suc n) (fiber (indConFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + zero))} (pt-map B) (P a)) λ tt → (f a))
  helper a = Lemma861Gen neg1 (suc n) (λ x y → (2+ ℕ→ℕ₋₂ (predℕ y + zero))) (natHelper n) (pt-map B) (conOfpt-map B zero conB) (P a) (λ tt → f a)
    where
    natHelper : (n : ℕ) → (2+ ℕ→ℕ₋₂ (n + zero)) ≡ suc (n + (2+ neg1))
    natHelper zero = refl
    natHelper (suc n) = cong (λ x → suc x) (natHelper n)

  conOfQ : (a : typ A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.Q A B n zero conA conB P f g p a)
  conOfQ a = transport (λ i → isOfHLevel (2+ pred₋₂ (ℕ→ℕ₋₂ n)) (prelims.QisFib A B n zero conA conB P f g p a (~ i)))
                       (transport (λ i → isOfHLevel (natHelper n (~ i)) (prelims.QisFib A B n zero conA conB P f g p a i1))
                                  (helper a))
    where
    natHelper : (n : ℕ) → (2+ pred₋₂ (ℕ→ℕ₋₂ n)) ≡ (suc n)
    natHelper zero = refl
    natHelper (suc n) = refl

  typesQ : (a : typ A) → Σ ((a : (typ A)) → (prelims.Q A B n zero conA conB P f g p a)) λ ℓ → ℓ (pt A) ≡ (g , p)
  typesQ a  = (fst (conInd-i→iii (pt-map A)
                                 (pred₋₂ (ℕ→ℕ₋₂ n))
                                 (conOfpt-map A n conA)
                                 (λ a → (prelims.Q A B n (zero) conA conB P f g p a , conOfQ a )))
                   (λ x → (g , p))) ,
              cong (λ f → f tt)
                   (snd (conInd-i→iii (pt-map A)
                                      (pred₋₂ (ℕ→ℕ₋₂ n))
                                      (conOfpt-map A n conA)
                                      (λ a → (prelims.Q A B n (zero) conA conB P f g p a , conOfQ a )))
                        (λ x → (g , p)))

Lemma8-6-2 {ℓ = ℓ} {ℓ' = ℓ'} A B n (suc m) conA conB P f g p =
          (λ a b → ((typesQ (pt A) .fst) a) .fst b) ,
          ((((λ a → sym ((typesQ (pt A)) .fst a .snd)))) ,
           (λ b → cong (λ x → (x .fst) b) (((typesQ) (pt A)) .snd))) ,
          (sym (transpHelper _ _ _ (cong (λ x → x .snd) (((typesQ) (pt A)) .snd))))
  where
  helper : (a : typ A) → isOfHLevel (suc n) (fiber (indConFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} (pt-map B) (P a)) λ tt → (f a))
  helper a = Lemma861GenNats m (suc n) (λ x y → 2+ ℕ→ℕ₋₂ (n + suc m)) (natHelper n m) (pt-map B) (conOfpt-map B (suc m) conB) (P a) λ tt → (f a)
    where
    natHelper : (n m : ℕ) → (2+ ℕ→ℕ₋₂ (n + suc m)) ≡ suc (n + (2+ ℕ→ℕ₋₂ m))
    natHelper zero m = refl
    natHelper (suc n) m = cong (λ x → suc x) (natHelper n m)

  conOfQ : (a : typ A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.Q A B n (suc m) conA conB P f g p a)
  conOfQ a = transport (λ i → isOfHLevel (natHelper n i) (prelims.Q A B n (suc m) conA conB P f g p a))
                       (transport (λ i → isOfHLevel (suc n)
                                  (prelims.QisFib A B n (suc m) conA conB P f g p a (~ i))) (helper a))
    where
    natHelper : (n : ℕ) → (suc n) ≡ (2+ ((pred₋₂ (ℕ→ℕ₋₂ n))))
    natHelper zero = refl
    natHelper (suc n) = refl

  typesQ : (a : typ A) → Σ ((a : (typ A)) → (prelims.Q A B n (suc m) conA conB P f g p a)) λ ℓ → ℓ (pt A) ≡ (g , p)
  typesQ a  = (fst (conInd-i→iii (pt-map A)
                                 (pred₋₂ (ℕ→ℕ₋₂ n))
                                 (conOfpt-map A n conA)
                                 (λ a → (prelims.Q A B n (suc m) conA conB P f g p a , conOfQ a )))
                                 (λ x → (g , p))) ,
              cong (λ f → f tt)
                   (snd (conInd-i→iii (pt-map A)
                                      (pred₋₂ (ℕ→ℕ₋₂ n))
                                      (conOfpt-map A n conA)
                                      (λ a → (prelims.Q A B n (suc m) conA conB P f g p a , conOfQ a )))
                                      (λ x → (g , p)))
