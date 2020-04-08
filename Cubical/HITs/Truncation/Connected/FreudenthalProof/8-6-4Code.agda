{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-4Code where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.Prelim
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-2
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Prod
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification hiding (elim)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

open import Cubical.Data.HomotopyGroup
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

σ : A → A → typ (Ω ((Susp A) , north))
σ a x = merid x ∙ sym (merid a)

{- To show that σ is 2n-connected we define CODE (see proof in the HoTT book). -}


{- We first need to show that (a variant of) the canceller function defined in FreudenthalProof.Prelim is an equivalence -}
abstract
  isEquivCancel : ∀ {ℓ} {A : Type ℓ}{a : A} (n : ℕ) (q : north ≡ south) →
                   isEquiv {A = ∥ fiber (λ y → σ a y)
                           (q ∙ sym (merid a)) ∥ ℕ→ℕ₋₂ (n + n)}
                           {B = ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                           (elim (λ _ → isOfHLevelTrunc (2 + (n + n) ))
                                λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣)
  isEquivCancel {a = a} n q = isoToEquiv (iso
                                        ((elim (λ _ → isOfHLevelTrunc (2 + (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                        (elim (λ _ → isOfHLevelTrunc (2 + (n + n))) λ s → ∣ (fst s) , cancellerInv (λ i → (merid a) (~ i)) (merid (fst s)) q (snd s) ∣)
                                        (λ b → elim {B = λ b → ((elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                                                        λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                                              ((elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                                                        λ s → ∣ (fst s) , cancellerInv (sym (merid a)) (merid (fst s)) q (snd s) ∣) b)
                                                         ≡ b}
                                                   (λ x →  isOfHLevelSuc _ (isOfHLevelTrunc (2 + (n + n)) _ x))
                                                   (λ b i → ∣ fst b , cancellerSection (sym (merid a)) (merid (fst b)) q (snd b) i ∣) b)
                                         (λ b → elim {B = λ b → ((elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                                                        λ b → ∣ (fst b) , cancellerInv (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                                                ((elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                                                        λ s → ∣ (fst s) , canceller (sym (merid a)) (merid (fst s)) q (snd s) ∣) b)
                                                         ≡ b}
                                                    (λ x → isOfHLevelSuc (suc (n + n)) (isOfHLevelTrunc (2 + (n + n)) _ x))
                                                    (λ b i → ∣ fst b , cancellerRetract (sym (merid a)) (merid (fst b)) q (snd b) i ∣) b)) .snd

{- CODE will be defined by means of univalence applied to an equivalence
∥ fiber (λ y → σ a y) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n)) ≃ ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)).
To define this, it suffices to define the following map -}
sufMap : (n : ℕ) (c a x₂ : A)
          (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)
          (q : north ≡ south) →
          (merid x₂  ∙ sym (merid a))
        ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
sufMap {A = A} n c a x₂ iscon q = Lemma8-6-2 (A , a) (A , a) n n iscon iscon
                                              (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                                         isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevelTrunc (2 + (n + n)))
                                              (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣)
                                              (λ x r → ∣ x , switcher (merid a) q (merid x) r ∣)
                                              (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) q
                                                                                                         (canceller (sym (merid a))
                                                                                                                    (merid a) q x ) x i) ) ∣)) .fst x₂ c

{- We define the function -}
RlFun : (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) →
         (∥ fiber (λ y → σ a y) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))) →
         ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
RlFun  a c n iscon  q = elim (λ x → isOfHLevelTrunc ((2 + (n + n))))
                             λ r → sufMap n c a (fst r) iscon q (snd r)

-------------

{- To show RlFun is an equivalence, we need the following identity -}
RlFunId : (a : A) (n : ℕ)
          (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)
          (q : north ≡ south)
          (b : fiber (λ y → σ a y) (q ∙ sym (merid a))) →
          (RlFun a a n iscon q ∣ b ∣) ≡ ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b)∣
RlFunId {A = A} a n iscon q b = cong (λ x → x (snd b))
                                     (proj₁ (((Lemma8-6-2 (A , a) (A , a) n n iscon iscon
                                                          (λ x₂ c → (((merid x₂  ∙ sym (merid a))
                                                                     ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) ,
                                                                     isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevelTrunc (2 + (n + n))))
                                                          (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣)
                                                          (λ b s → ∣ b , switcher (merid a) q (merid b) s ∣)
                                                          (funExt (λ x → λ j → ∣ (refl j) , (switcherCancellerIdGeneral (merid a) q
                                                                                                                        (canceller (sym (merid a))
                                                                                                                                   (merid a) q x ) x j) ∣)))
                                                .snd) .fst)
                                              (fst b))

{- We show that RlFun is an equivalence for q : north ≡ south -}
baseCase : (a : A) (n : ℕ)
            (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)
            (q : north ≡ south) →
            isEquiv (RlFun a a n iscon q)
baseCase {A = A} a n iscon q = transport (λ i → isEquiv (helper (~ i)))
                                         (isEquivCancel n q )
  where
  helper : RlFun a a n iscon q
         ≡ elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
               λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣
  helper = funExt (elim {B = λ y → RlFun a a n iscon q y
                                ≡ (elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                       λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) y }
                  ((λ z y p → (isOfHLevelSuc (suc (n + n)) ((isOfHLevelTrunc {A = (fiber merid q)} (2 + (n + n)))
                                                            (RlFun a a n iscon q z)
                                                            ((elim (λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                                  λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b))
                                                                                              q (snd b) ∣) z) )) y p))
                  (RlFunId a n iscon q))

{- By induction for connected functions, the previous lemma is enough to show that RlFun is an equivalence -}
RlFunEquiv : (a c : A) (n : ℕ)
              (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)
              (q : north ≡ south) →
              isEquiv (RlFun a c n iscon q)
RlFunEquiv {A = A} a c n iscon q = fst (conInd-i→iii {A = Unit} {B = A} (λ x → a) (-1+ n)
                                                      (Lemma7-5-11 _ iscon)
                                                      λ c → (isEquiv (RlFun a c n iscon q)) ,
                                                             transport (λ i → isOfHLevel (natHelper n i) (isEquiv (RlFun a c n iscon q)))
                                                                       (isOfHLevelPlus {A = isEquiv (RlFun a c n iscon q)} n
                                                                                       (isPropIsEquiv (RlFun a c n iscon q))))
                                        (λ _ → baseCase a n iscon q)
                                        c
  where
  natHelper : (n : ℕ) → n + 1 ≡ (2+ (-1+ n))
  natHelper zero = refl
  natHelper (suc n) = cong (λ x → suc x) (natHelper n)

{- We will also need the following function to get things on the right form -}
abstract
  helperFun : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
             ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
             (q : x ≡ x) →
             transport (λ i₁ → Type ℓ') (A q)
           ≡ B (transport (λ i → x ≡ p i) q )
  helperFun {ℓ' = ℓ'} {x = x} = J (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                          ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
                                          (q : x ≡ x) →
                                          transport (λ i₁ → Type ℓ') (A q)
                                        ≡ B (transport (λ i → x ≡ p i) q ) )
                                 λ {A} {B} k q → transportRefl (A q) ∙
                                                 cong (λ x → A x) (rUnit q) ∙
                                                 k q ∙
                                                 cong (λ x → B x) (sym (transportRefl q))

  helperFunRefl : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X}
                          {A : x ≡ x → Type ℓ'}
                          {B : x ≡ x → Type ℓ'} →
                          helperFun {X = X} (refl {x = x}) {A = A} {B = B}
                        ≡ λ k q → transportRefl (A q) ∙
                                  cong (λ x → A x) (rUnit q) ∙
                                  k q ∙
                                  cong (λ x → B x) (sym (transportRefl q))
  helperFunRefl {ℓ' = ℓ'} {x = x} {A = A} {B = B} = cong (λ x → x {A} {B})
                                                        (JRefl (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                                                        ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
                                                                        (q : x ≡ x) →
                                                                        transport (λ i₁ → Type ℓ') (A q)
                                                                      ≡ B (transport (λ i → x ≡ p i) q ) )
                                λ {A} {B} k q → transportRefl (A q) ∙
                                                cong (λ x → A x) (rUnit q) ∙
                                                k q ∙
                                                cong (λ x → B x) (sym (transportRefl q)))

  {- For now things do not compute properly, so we use an abstract version of univalence-}

  ua' : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
  ua' = ua

  ua'Cancel : ∀ {A B : Type ℓ} → (X : A ≃ B) → transport (λ i → ua' X i ) ≡ (fst X)
  ua'Cancel X = funExt λ x → uaβ X x

{- We finally define CODE -}
CODE : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
CODE {A = A} a n iscon north p = (∥ fiber (λ y → σ a y) p ∥ (ℕ→ℕ₋₂ (n + n)))
CODE {ℓ} {A = A} a n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
CODE {ℓ} {A = A} a n iscon (merid c i) = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ a y) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296-fun {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ a y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (helperFun {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ a y) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua' (RlFun a c n iscon q , RlFunEquiv a c n iscon q)))) i
-------------------------

{- We will need the following identites to prove that σ is 2n-connected -}
sufMapId : (n : ℕ) (a x1 : A)
            (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
            sufMap n x1 a a iscon (merid x1)
          ≡ λ r → ∣ x1 , switcher (merid a) (merid x1) (merid x1) r ∣
sufMapId {A = A} n a x1 iscon = (proj₂ (Lemma8-6-2 (A , a) (A , a) n n iscon iscon
                                                    (λ x₂ c → ((merid x₂  ∙ sym (merid a))
                                                            ≡ ((merid x1) ∙ sym (merid c)) →
                                                              ∥ Σ A (λ x → merid x ≡ (merid x1)) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                                              isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevelTrunc (2 +  (n + n)))
                                                    (λ x r → ∣ x , canceller (sym (merid a)) (merid x) (merid x1) r ∣)
                                                    (λ x r → ∣ x , switcher (merid a) (merid x1) (merid x) r ∣)
                                                    (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) (merid x1)
                                                                                                               (canceller (sym (merid a)) (merid a)
                                                                                                                          (merid x1) x ) x i) ) ∣)) .snd .fst) x1)

sufMapId2 :  (n : ℕ) (a x1 : A)
              (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
              sufMap n a a x1 iscon (merid x1) refl ≡ ∣ x1 , canceller (sym (merid a)) (merid x1) (merid x1) refl ∣
sufMapId2 {A = A} n a x1 iscon i = (proj₁ (Lemma8-6-2 (A , a) (A , a) n n iscon iscon
                                                       (λ x₂ c → ((merid x₂  ∙ sym (merid a))
                                                                ≡ ((merid x1) ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ (merid x1)) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                                                 isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevelTrunc (2 + (n + n)))
                                                       (λ x r → ∣ x , canceller (sym (merid a)) (merid x) (merid x1) r ∣)
                                                       (λ x r → ∣ x , switcher (merid a) (merid x1) (merid x) r ∣)
                                                       (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) (merid x1)
                                                                                                                  (canceller (sym (merid a)) (merid a) (merid x1) x)
                                                                                                                  x i) ) ∣))
                                                       .snd .fst) x1) i
                                            refl
