{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.Prelim where

open import Cubical.HITs.Truncation.Connected.Base 
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

-- some cong stuff --
congComp2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a b c : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) →
              (cong f p ∙ cong f q) ≡ cong f (p ∙ q)
congComp2  {A = A}{a = a} {b = b} {c = c} f p q = J (λ b p → (c : A) (q : b ≡ c) → (cong f p ∙ cong f q) ≡ cong f (p ∙ q))
                                                      (λ c → J (λ c q → (λ i → f a) ∙ (λ i → f (q i)) ≡ (λ i → f ((refl ∙ q) i)))
                                                                 ((λ j → rUnit (refl {x = f a}) (~ j)) ∙
                                                                 λ j i → f ((lUnit (refl {x = a}) j) i)))
                                                      p c q 

congComp3 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a b c d : A} (f : A → B) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) →
           (cong f p ∙ cong f q) ∙ cong f r ≡ cong f (p ∙ q ∙ r)
congComp3  {A = A}{a = a} {b = b} {c = c} {d = d} f p q r =
          J (λ b p → (c d : A) (q : b ≡ c) (r : c ≡ d) → (cong f p ∙ cong f q) ∙ cong f r ≡ cong f (p ∙ q ∙ r))
            (λ c d → J (λ c q → (r : c ≡ d) → ((λ i → f (refl i)) ∙ (λ i → f (q i))) ∙ (λ i → f (r i)) ≡ (λ i → f ((refl ∙ q ∙ r) i)))
                                (J (λ d r → ((λ i → f a) ∙ (λ i → f a)) ∙ (λ i → f (r i)) ≡ (λ i → f (((λ _ → a) ∙ refl ∙ r) i)))
                                   ((λ j → rUnit (rUnit (λ i → f a) (~ j)  ) (~ j) ) ∙
                                    λ j i → f ( (lUnit (lUnit (λ _ → a) j) j)   i)  )))
               p c d q r

--- ℕ₋₂ stuff ---

{-
_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m
-}
pmId : (n : ℕ) → suc₋₂ (pred₋₂ (ℕ→ℕ₋₂ n)) ≡ (ℕ→ℕ₋₂ n)
pmId zero = refl
pmId (suc n) = refl

{-
minusId : (n : ℕ) → n - n ≡ 0
minusId zero = refl
minusId (suc n) = minusId n

-assocHelp : {a b : ℕ} → ((a + b) - b) ≡ a
-assocHelp {zero} {zero} = refl
-assocHelp {zero} {suc b} = -assocHelp {zero} {b}
-assocHelp {suc a} {zero} i = suc (+-zero a i)
-assocHelp {suc a} {suc b} = (λ i → ((+-suc a b i) - b)) ∙ (λ i → ((suc (+-comm a b i)) - b)) ∙
                             (λ i → (+-suc b a (~ i)) - b) ∙ ((λ i → ((+-comm b (suc a) i) - b))) ∙
                             -assocHelp {suc a} {b}
-}
-------------------
{- Functions used in definitions of Code -}
canceller : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q
canceller {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q)

cancellerReflCase : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → canceller refl p q ≡ λ id → (rUnit p) ∙ id ∙ sym (rUnit q)
cancellerReflCase {a = a} {b = b} p q = cong (λ x → x p q) (JRefl (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q)) 

cancellerInv : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r
cancellerInv {a = a} {b = b} = J (λ c r → (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r) λ p q id → sym (rUnit p) ∙ id ∙ rUnit q

cancellerInvReflCase : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → cancellerInv refl p q ≡ λ id → sym (rUnit p) ∙ id ∙ rUnit q
cancellerInvReflCase {a = a} {b = b} p q = cong (λ x → x p q) (JRefl (λ c r → (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r) λ p q id → sym (rUnit p) ∙ id ∙ rUnit q) 

cancellerSection :  ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → section (canceller r p q) (cancellerInv r p q) 
cancellerSection {a = a} {b = b} {c = c} = J (λ c r → (p q : a ≡ b) → section (canceller r p q) (cancellerInv r p q) ) λ p q → transport (λ i → section (cancellerReflCase p q (~ i)) (cancellerInvReflCase p q (~ i))) (λ b → assoc (rUnit p) ((λ i → rUnit p (~ i)) ∙ b ∙ rUnit q) (λ i → rUnit q (~ i)) ∙
                          (λ i → ((assoc (rUnit p) (sym (rUnit p)) (b ∙ rUnit q)) i) ∙ (λ i → rUnit q (~ i))) ∙
                          (λ i → ((rCancel (rUnit p) i) ∙ (b ∙ rUnit q)) ∙ (sym (rUnit q))) ∙
                          (λ i → lUnit (b ∙ rUnit q) (~ i) ∙ (sym (rUnit q))) ∙
                          (sym (assoc b (rUnit q) (sym (rUnit q)))) ∙
                          (λ i → b ∙ (rCancel (rUnit q) i)) ∙
                          sym (rUnit b))

cancellerRetract :  ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → retract (canceller r p q) (cancellerInv r p q) 
cancellerRetract {a = a} {b = b} {c = c} = J (λ c r → (p q : a ≡ b) → retract (canceller r p q) (cancellerInv r p q) ) λ p q → transport (λ i → retract (cancellerReflCase p q (~ i)) (cancellerInvReflCase p q (~ i))) λ b → assoc (sym (rUnit p)) ((λ i → rUnit p (i)) ∙ b ∙ (sym (rUnit q))) (rUnit q) ∙
                          (λ i → ((assoc (sym (rUnit p)) (rUnit p) (b ∙ sym (rUnit q))) i) ∙ (rUnit q)) ∙
                          (λ i → ((lCancel (rUnit p) i) ∙ (b ∙ sym (rUnit q))) ∙ ((rUnit q))) ∙
                          (λ i → (lUnit (b ∙ sym (rUnit q)) (~ i)) ∙ (rUnit q)) ∙
                          (sym (assoc b (sym (rUnit q)) (rUnit q))) ∙
                          (λ i → b ∙ (rCancel (sym (rUnit q)) i)) ∙
                          sym (rUnit b)
  

cancellerIsEquiv : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → isEquiv (canceller r p q)
cancellerIsEquiv {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r → ((p q : a ≡ b) → isEquiv (canceller r p q))) λ p q → transport (λ i → isEquiv (cancellerHelp p q (~ i))) (helper p q)
  where
  helper : (p q  : a ≡ b) → isEquiv (λ id → ((rUnit p) ∙ id ∙ sym (rUnit q)))
  helper p q = isoToEquiv (iso ((λ id → ((rUnit p) ∙ id ∙ sym (rUnit q)))) (λ id → sym (rUnit p) ∙ id ∙ rUnit q)
                          ((λ b → assoc (rUnit p) ((λ i → rUnit p (~ i)) ∙ b ∙ rUnit q) (λ i → rUnit q (~ i)) ∙
                          (λ i → ((assoc (rUnit p) (sym (rUnit p)) (b ∙ rUnit q)) i) ∙ (λ i → rUnit q (~ i))) ∙
                          (λ i → ((rCancel (rUnit p) i) ∙ (b ∙ rUnit q)) ∙ (sym (rUnit q))) ∙
                          (λ i → lUnit (b ∙ rUnit q) (~ i) ∙ (sym (rUnit q))) ∙
                          (sym (assoc b (rUnit q) (sym (rUnit q)))) ∙
                          (λ i → b ∙ (rCancel (rUnit q) i)) ∙
                          sym (rUnit b)))
                          λ b → assoc (sym (rUnit p)) ((λ i → rUnit p (i)) ∙ b ∙ (sym (rUnit q))) (rUnit q) ∙
                          (λ i → ((assoc (sym (rUnit p)) (rUnit p) (b ∙ sym (rUnit q))) i) ∙ (rUnit q)) ∙
                          (λ i → ((lCancel (rUnit p) i) ∙ (b ∙ sym (rUnit q))) ∙ ((rUnit q))) ∙
                          (λ i → (lUnit (b ∙ sym (rUnit q)) (~ i)) ∙ (rUnit q)) ∙
                          (sym (assoc b (sym (rUnit q)) (rUnit q))) ∙
                          (λ i → b ∙ (rCancel (sym (rUnit q)) i)) ∙
                          sym (rUnit b)) .snd

  cancellerHelp : (p q : a ≡ b) → canceller refl p q ≡ λ id → (rUnit p) ∙ id ∙ sym (rUnit q)
  cancellerHelp  p q = cong (λ x → x p q) (JRefl (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q))

switcher : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p : a ≡ b) (q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q
switcher {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {a} (λ b p → ((q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q))
                                 (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → refl ∙ (sym refl) ≡ q ∙ (sym r) → r ≡ q) λ r id → (lUnit r) ∙ cong (λ x → x ∙ r) ((rUnit (refl) ∙ id ∙ (sym (lUnit (sym r)))))  ∙ (lCancel r))
                                 -- ((λ j → (λ i → (lUnit (sym r) j) (~ i) ))) ∙ cong (λ x → sym x) (sym id) ∙ ((λ j → (λ i → (sym (rUnit (refl {x = a})) j) (~ i) ))))
cancellerRefl : ∀ {ℓ} {A : Type ℓ} {a : A} → canceller {a = a} {b = a} {c = a} refl refl refl ≡ λ id → rUnit refl ∙ id ∙ sym (rUnit refl)
cancellerRefl {ℓ} {A} {a} = cong (λ x → x refl refl) (JRefl (λ c r → (p q : a ≡ a) → p ∙ r ≡ q ∙ r → p ≡ q) λ p q id → rUnit p ∙ id ∙ sym (rUnit q))

switcherRefl : ∀ {ℓ} {A : Type ℓ} {a : A} → switcher (refl {x = a}) refl refl ≡ λ id → ((lUnit (refl {x = a})) ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl))
switcherRefl {ℓ} {A} {a} = cong (λ x → x refl refl) (JRefl {ℓ} {A} {a} ((λ b p → ((q r : a ≡ a) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q))) (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → refl ∙ (sym refl) ≡ q ∙ (sym r) → r ≡ q) λ r id → (lUnit r) ∙ cong (λ x → x ∙ r) ((rUnit (refl) ∙ id ∙ (sym (lUnit (sym r)))))  ∙ (lCancel r))) ∙
               cong (λ x → x refl) (JRefl {ℓ} {A} {a} (λ c q → (r : a ≡ c) → (λ _ → a) ∙ (λ i → a) ≡ q ∙ (λ i → r (~ i)) → r ≡ q) (λ r id → lUnit r ∙ (λ i → (rUnit (λ _ → a) ∙ id ∙ (λ i₁ → lUnit (λ i₂ → r (~ i₂)) (~ i₁))) i ∙ r) ∙ lCancel r))


switcherCancellerId : ∀ {ℓ} {A : Type ℓ} {a : A} (id : (refl {x = a}) ∙ refl ≡ refl ∙ refl) → canceller (refl {x = a}) refl refl id ≡ switcher refl refl refl id
switcherCancellerId id = (λ i → (cancellerRefl i) id) ∙ sym (finalReflPath id)  ∙ λ i → (switcherRefl (~ i)) id
  where
  finalReflPath : {a : A} → (id : refl ∙ refl ≡ refl ∙ refl ) → ((lUnit (refl {x = a})) ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl)) ≡ (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))
  finalReflPath {a = a} id j = hcomp (λ k → λ{(j = i0) → refl {x = (lUnit (refl {x = a}))
                                                              ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id
                                                              ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl)} k
                                     ; (j = i1) → ((sym (lUnit ((cong (λ x → x)  (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ refl)))
                                                  ∙ (sym (rUnit ((cong (λ x → x)  (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))))))) k})
                             ((λ i → (lUnit (refl {x = a})) (i ∧ ~ j) ) ∙ (cong (λ x → (sym (rUnit x)) j)  (rUnit (refl {x = a})
                                                                        ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (λ i → (lCancel refl) (i ∨ j) ))


switcherCancellerIdGeneral : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → (p ≡ q) → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller (sym p) p q  P ≡ switcher p q p P
switcherCancellerIdGeneral {ℓ} {A} {a} {b} p q = J {ℓ} {a ≡ b} {p} (λ q _ → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller (sym p) p q  P ≡ switcher p q p P) (J {ℓ} {A} {a} (λ b p → (P : p ∙ (sym p) ≡ p ∙ (sym p)) → canceller (sym p) p p  P ≡ switcher p p p P) (λ P → switcherCancellerId P) p)

symTypeId : {a b : A} → (a ≡ b) ≡ (b ≡ a)
symTypeId {A = A} {a = a} {b = b} = isoToPath (iso sym sym (λ x → refl) λ x → refl)

-----------------------
{- Lemmas used in definitions of Code/Freudenthal proof -}
assocJ : ∀ {ℓ} {A : Type ℓ} {x y z w : A} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
         p ∙ q ∙ r ≡ (p ∙ q) ∙ r
assocJ {x = x} {y = y} {z = z} {w = w} = J (λ y p → (q : y ≡ z) (r : z ≡ w) → p ∙ q ∙ r ≡ (p ∙ q) ∙ r)
                                           (J (λ z q → (r : z ≡ w) → refl ∙ q ∙ r ≡ (refl ∙ q) ∙ r)
                                             (J (λ w r → (λ _ → x) ∙ refl ∙ r ≡ ((λ _ → x) ∙ refl) ∙ r)
                                                (((λ i → refl ∙ rCancel refl i)) ∙ rUnit (refl ∙ refl))))

assocJRefl : ∀ {ℓ} {A : Type ℓ} {x : A} → assocJ (λ _ → x) (λ _ → x) (λ _ → x) ≡ (λ i → refl ∙ rCancel refl i) ∙ (rUnit (refl ∙ refl))
assocJRefl {x = x} = (cong (λ x → x refl refl) (JRefl (λ y p → (q : y ≡ x) (r : x ≡ x) → p ∙ q ∙ r ≡ (p ∙ q) ∙ r)
                                                     (J (λ z q → (r : z ≡ x) → refl ∙ q ∙ r ≡ (refl ∙ q) ∙ r)
                                                        (J (λ w r → (λ _ → x) ∙ refl ∙ r ≡ ((λ _ → x) ∙ refl) ∙ r)
                                                          ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)))))) ∙
                      cong (λ x → x refl)  (JRefl (λ z q → (r : z ≡ x) → refl ∙ q ∙ r ≡ (refl ∙ q) ∙ r)
                                                        (J (λ w r → (λ _ → x) ∙ refl ∙ r ≡ ((λ _ → x) ∙ refl) ∙ r)
                                                          ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)))) ∙
                      JRefl (λ w r → (λ _ → x) ∙ refl ∙ r ≡ ((λ _ → x) ∙ refl) ∙ r)
                             ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl))



transpFunct : ∀ {ℓ ℓ'} {A : Type ℓ} {x y z : A} {B : A → Type ℓ'} (p : x ≡ y) (q : y ≡ z) (u : B x) →
              transport (λ i → B (q i)) (transport (λ i → B (p i)) u) ≡ transport (λ i → B ((p ∙ q) i)) u 
transpFunct {A = A} {x = x} {y = y} {z = z} {B = B} p =
                    J (λ y p → (z : A) (q : y ≡ z) (u : B x) →
                               transport (λ i → B (q i)) (transport (λ i → B (p i)) u) ≡ transport (λ i → B ((p ∙ q) i)) u)
                      (λ z → J (λ z q → (u : B x) →
                                        transport (λ i → B (q i)) (transport (λ i → B (refl {x = x} i)) u) ≡ transport (λ i → B ((refl ∙ q) i)) u)
                               (λ u → transportRefl ((transport (λ i → B x) u)) ∙
                                      λ j → transport (λ i → B ((lUnit ((λ _ → x)) j) i)) u) {z})
                       p z

transpFunctRefl : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} {B : A → Type ℓ'}  (u : B x) →
                  transpFunct {A = A} {B = B} (λ _ → x) (λ _ → x) u ≡
                  (transportRefl ((transport (λ i → B x) u)) ∙
                  λ j → transport (λ i → B ((lUnit ((λ _ → x)) j) i)) u)
transpFunctRefl {A = A} {x = x} {B = B} u =
                        (λ i →  JRefl (λ y p → (z : A) (q : y ≡ z) (u : B x) →
                                               transport (λ i → B (q i)) (transport (λ i → B (p i)) u) ≡ transport (λ i → B ((p ∙ q) i)) u)
                                      (λ z p u → J (λ z q → (u : B x) →
                                                            transport (λ i → B (q i)) (transport (λ i → B (refl {x = x} i)) u) ≡ transport (λ i → B ((refl ∙ q) i)) u)
                                                   (λ u → transportRefl ((transport (λ i → B x) u)) ∙
                                                          λ j → transport (λ i → B ((lUnit ((λ _ → x)) j) i)) u) p u ) i x refl u)
                         ∙ cong (λ x → x u) (JRefl (λ z q → (u : B x) →
                                                            transport (λ i → B (q i)) (transport (λ i → B (refl {x = x} i)) u) ≡ transport (λ i → B ((refl ∙ q) i)) u)
                                                   (λ u → transportRefl ((transport (λ i → B x) u)) ∙
                                                          λ j → transport (λ i → B ((lUnit ((λ _ → x)) j) i)) u)) 

cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q

{- (2.9.4) in the HoTT Book -}
Lemma294 : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x1 x2 : X} (p : x1 ≡ x2) (f : A (x1) → B (x1)) → transport (λ i → A (p i) → B (p i)) f ≡ λ x → transport (λ i → B (p i)) (f (transport (λ i → A (p (~ i))) x))
Lemma294 {A = A} {B = B} {x1 = x1}  = J (λ x2 p → (f : A (x1) → B (x1)) → transport (λ i → A (p i) → B (p i)) f ≡ λ x → transport (λ i → B (p i)) (f (transport (λ i → A (p (~ i))) x)) ) λ f → refl

Lemma294Refl : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x1 : X} (f : A (x1) → B (x1)) → Lemma294 {A = A} {B = B} (λ _ → x1) f ≡ refl
Lemma294Refl {A = A} {B = B} {x1 = x1} f = cong (λ g → g f) (JRefl (λ x2 p → (f : A (x1) → B (x1)) → transport (λ i → A (p i) → B (p i)) f ≡ λ x → transport (λ i → B (p i)) (f (transport (λ i → A (p (~ i))) x)) ) λ f → refl)

{- The (inverse) function from Lemma 2.9.6 in the HoTT book -}
abstract
  Lemma296-fun : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
                 (p : x ≡ y)
                 (f : (A x) → (B x))
                 (g : (A y) → (B y)) →
                 ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)) →
                 (transport (λ i → (A (p i)) → (B (p i))) f ≡ g)
  Lemma296-fun {x = x} {A = A} {B = B} p f g =
               J (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                          ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)) →
                          (transport (λ i → (A (p i)) → (B (p i))) f ≡ g))
                 (λ f g h → transportRefl f ∙ funExt λ z → sym (transportRefl (f z)) ∙
                                                           (h z) ∙
                                                           λ i → (g (transportRefl z i)))
                  p f g
  Lemma296-funRefl : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {x : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
                     (f : (A x) → (B x))
                     (g : (A x) → (B x)) → 
                     Lemma296-fun {A = A} {B = B} (refl {x = x}) f g
                   ≡ λ h → transportRefl f ∙ funExt λ z → sym (transportRefl (f z))  ∙
                                             (h z) ∙
                                             λ i → (g (transportRefl z i))
  Lemma296-funRefl {x = x} {A = A} {B = B} f g =
                   cong (λ h → h f g)
                        (JRefl (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                        ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)) →
                                        (transport (λ i → (A (p i)) → (B (p i))) f ≡ g))
                               (λ f g h → transportRefl f ∙ funExt λ z → sym (transportRefl (f z)) ∙
                                                                         (h z) ∙
                                                                         λ i → (g (transportRefl z i))))



Lemma296 : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a))
Lemma296 {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x}
                                                            (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)))
                                                            (λ f g → transport (λ i → reflTransport f g (~ i)) (reflCase f g))
  where
  reflTransport : (f g : A x → B x) → ((transport (λ i → A (refl {x = x} i) → B (refl {x = x} i)) f ≡ g) ≡ ((a : A x) → transport (λ i → B (refl {x = x} i)) (f a) ≡ g (transport (λ i → A (refl {x = x} i)) a))) ≡ ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflTransport f g j = (transportRefl f j ≡ g) ≡ ((a : A x) → transportRefl (f a) j ≡ g (transportRefl a j))

  reflCase : (f g : A x → B x) → ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflCase f g = isoToPath (iso (λ p → funExt⁻ p) (λ p → funExt p) (λ x → refl) λ x → refl)




-------------------- Some useful lemmas. Using J to prove them makes life a lot easier later ------------------------------
symDistr : {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ (sym q) ∙ (sym p)
symDistr {x = x} {z = z} = J (λ y p → (q : y ≡ z) → sym (p ∙ q) ≡ (sym q) ∙ (sym p))
                             (J (λ z q → sym (refl ∙ q) ≡ (sym q) ∙ (sym refl) )
                                refl)

toPathCancel : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} → (z : transp A i0 x ≡ y) → fromPathP (toPathP {A = A} {x = x} {y = y} z) ≡ z
toPathCancel {A = A} {x = x} {y = y} z = cong (λ x → fst x) (equiv-proof (toPathP-isEquiv A {x = x} {y = y}) (toPathP z) .snd (z , refl))


transportLemma : {a b : A} {B : (z : A) → Type ℓ'} (p : a ≡ b) (x : B a) (y : B b) → transport (λ i → B (p i)) x ≡ y → transport (λ i → B (p (~ i))) y ≡ x
transportLemma {a = a} {B = B} x y = J (λ b p → (x : B a) (y : B b) → transport (λ i → B (p i)) x ≡ y → transport (λ i → B (p (~ i))) y ≡ x)
                                       (λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x)
                                        x y 
transportLemmaRefl : {a : A} {B : (z : A) → Type ℓ'} → (x y : B a) →  transportLemma {B = B} (λ _ → a) ≡ λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x
transportLemmaRefl {ℓ} {A = A} {a = a} {B = B} x y = JRefl {ℓ} {A} {a} (λ b p → (x y : B a) → transport (λ i → B a) x ≡ y → transport (λ i → B a) y ≡ x)
                                       (λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x)

transpRCancel : (p : A ≡ B) (b : B) → transport p (transport⁻ p b) ≡ b
transpRCancel {A = A} = J (λ B p → (b : B) → transport p (transport⁻ p b) ≡ b) λ b → transportRefl (transport refl b) ∙ transportRefl b

transpRCancelRefl : (a : A) → transpRCancel refl a ≡ transportRefl (transport refl a) ∙ transportRefl a
transpRCancelRefl {A = A} a = cong (λ x → x a) (JRefl (λ A p → (a : A) → transport p (transport⁻ p a) ≡ a) λ b → transportRefl (transport refl b) ∙ transportRefl b)

pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma2Refl : ∀ {ℓ} {A : Type ℓ} {a : A} → pairLemma2 (refl {x = a}) ≡ (transportRefl refl)
pairLemma2Refl {ℓ} {A} {a} = JRefl (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (p : a1 ≡ b) (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma {A = A} {a1 = a1} {b = b} {c = c} p q = J (λ b p → (c : A) →  (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q )
                                                      (λ c q → pairLemma2 q ∙ lUnit q)
                                                      p c q

pairLemmaRefl : ∀ {ℓ} {A : Type ℓ} {a1 : A} (q : a1 ≡ a1) → pairLemma (λ _ → a1) q ≡ pairLemma2 q ∙ lUnit q
pairLemmaRefl {A = A} {a1 = a1} q = cong (λ x → x a1 q) (JRefl (λ b p → (c : A) →  (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q ) (λ c q → pairLemma2 q ∙ lUnit q))


pairLemma* : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (q : b ≡ c) (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma* {a1 = a1} {b = b}  = J (λ c q → (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q)
                                   λ p → transportRefl p ∙ rUnit p

pairLemma*Refl : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) → pairLemma* refl p ≡ transportRefl p ∙ rUnit p
pairLemma*Refl {a1 = a1} {b = b} p = cong (λ x → x p) (JRefl (λ c q → (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q)
                                                               λ p → transportRefl p ∙ rUnit p)

pairLemmaId : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (p : a1 ≡ b) (q : b ≡ c)  → pairLemma p q ≡ pairLemma* q p
pairLemmaId {ℓ} {A} {a1} {b} {c} = J (λ b p → (q : b ≡ c)  → pairLemma p q ≡ pairLemma* q p)
                                      (J (λ c q → pairLemma refl q ≡ pairLemma* q refl)
                                      (pairLemmaRefl refl ∙ sym (pairLemma*Refl refl ∙ λ k → (pairLemma2Refl (~ k)) ∙ rUnit refl)))

pairLemmaReflRefl : {a1 : A} → pairLemma (λ _ → a1) (λ _ → a1) ≡ (transportRefl refl) ∙ lUnit refl
pairLemmaReflRefl = pairLemmaRefl refl ∙ λ i → pairLemma2Refl i ∙ lUnit refl

substComposite-∙ : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
                     → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                     → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite-∙ {A = A} B p q u = transport (λ i → subst B (□≡∙ p q i) u ≡ subst B q (subst B p u)) (substComposite-□ B p q u)

inv-rUnit : ∀ {ℓ} {A : Type ℓ} (x : A) → (λ i → rUnit (rUnit (λ _ → x) (~ i)) i ) ≡ refl
inv-rUnit x = transport (λ i → PathP (λ j → (lCancel (λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i) j)
                                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                                 refl)
                    (helper x)
  where
  helper : ∀ {ℓ} {A : Type ℓ} (x : A) →
           PathP (λ i → ((λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) (~ k)) ∙
                          λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i)
                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                 refl
  helper x = compPathP (λ k i → rUnit (rUnit (λ _ → x) (~ i)) (i ∧ (~ k)))
                       λ k i → rUnit (λ _ → x) (~ i ∨ k)
