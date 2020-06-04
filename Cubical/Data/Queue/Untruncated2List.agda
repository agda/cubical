{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue.Untruncated2List where

open import Cubical.Foundations.Everything

open import Cubical.Foundations.SIP
open import Cubical.Structures.Queue

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Queue.1List

module _ (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 -- Untruncated 2Lists
 data Q : Type ℓ where
   Q⟨_,_⟩ : (xs ys : List A) → Q
   tilt : ∀ xs ys z → Q⟨ xs ++ [ z ] , ys ⟩ ≡ Q⟨ xs , ys ++ [ z ] ⟩

  -- enq into the first list, deq from the second if possible

 flushEq' : (xs ys : List A) → Q⟨ xs ++ ys , [] ⟩ ≡ Q⟨ xs , rev ys ⟩
 flushEq' xs [] = cong Q⟨_, [] ⟩ (++-unit-r xs)
 flushEq' xs (z ∷ ys) j =
   hcomp
     (λ i → λ
       { (j = i0) → Q⟨ ++-assoc xs [ z ] ys i , [] ⟩
       ; (j = i1) → tilt xs (rev ys) z i
       })
     (flushEq' (xs ++ [ z ]) ys j)

 flushEq : (xs ys : List A) → Q⟨ xs ++ rev ys , [] ⟩ ≡ Q⟨ xs , ys ⟩
 flushEq xs ys = flushEq' xs (rev ys) ∙ cong Q⟨ xs ,_⟩ (rev-rev ys)

 emp : Q
 emp = Q⟨ [] , [] ⟩

 enq : A → Q → Q
 enq a Q⟨ xs , ys ⟩ = Q⟨ a ∷ xs , ys ⟩
 enq a (tilt xs ys z i) = tilt (a ∷ xs) ys z i

 deqFlush : List A → Unit ⊎ (Q × A)
 deqFlush [] = inl tt
 deqFlush (x ∷ xs) = inr (Q⟨ [] , xs ⟩ , x)

 deq : Q → Unit ⊎ (Q × A)
 deq Q⟨ xs , [] ⟩ = deqFlush (rev xs)
 deq Q⟨ xs , y ∷ ys ⟩ = inr (Q⟨ xs , ys ⟩ , y)
 deq (tilt xs [] z i) = path i
   where
   path : deqFlush (rev (xs ++ [ z ])) ≡ inr (Q⟨ xs , [] ⟩ , z)
   path =
     cong deqFlush (rev-snoc xs z)
     ∙ cong (λ q → inr (q , z)) (sym (flushEq' [] xs))
 deq (tilt xs (y ∷ ys) z i) = inr (tilt xs ys z i , y)

 Raw : RawQueue
 Raw = (Q , emp , enq , deq)

 -- We construct an equivalence Q₁≃Q and prove that this is a queue-iso

 private
   module One = 1List A Aset
   open One renaming (Q to Q₁; emp to emp₁; enq to enq₁; deq to deq₁) using ()

 quot : Q₁ → Q
 quot xs = Q⟨ xs , [] ⟩

 eval : Q → Q₁
 eval Q⟨ xs , ys ⟩ = xs ++ rev ys
 eval (tilt xs ys z i) =
   hcomp
     (λ j → λ
       { (i = i0) → (xs ++ [ z ]) ++ rev ys
       ; (i = i1) → xs ++ rev-snoc ys z (~ j)
       })
     (++-assoc xs [ z ] (rev ys) i)

 quot∘eval : ∀ q → quot (eval q) ≡ q
 quot∘eval Q⟨ xs , ys ⟩ = flushEq xs ys
 quot∘eval (tilt xs ys z i) j =
   hcomp
     (λ k → λ
       { (i = i0) →
         compPath-filler (flushEq' (xs ++ [ z ]) (rev ys)) (cong Q⟨ xs ++ [ z ] ,_⟩ (rev-rev ys)) k j
       ; (i = i1) → helper k
       ; (j = i0) →
         Q⟨ compPath-filler (++-assoc xs [ z ] (rev ys)) (cong (xs ++_) (sym (rev-snoc ys z))) k i , [] ⟩
       ; (j = i1) → tilt xs (rev-rev ys k) z i
       })
     flushEq'-filler
   where
   flushEq'-filler : Q
   flushEq'-filler =
     hfill
       (λ i → λ
         { (j = i0) → Q⟨ ++-assoc xs [ z ] (rev ys) i , [] ⟩
         ; (j = i1) → tilt xs (rev (rev ys)) z i
         })
       (inS (flushEq' (xs ++ [ z ]) (rev ys) j))
       i

   helper : I → Q
   helper k =
     hcomp
       (λ l → λ
         { (j = i0) → Q⟨ xs ++ rev-snoc ys z (l ∧ ~ k) , [] ⟩
         ; (j = i1) → Q⟨ xs , rev-rev-snoc ys z l k ⟩
         ; (k = i0) → flushEq' xs (rev-snoc ys z l) j
         ; (k = i1) → flushEq xs (ys ++ [ z ]) j
         })
       (compPath-filler (flushEq' xs (rev (ys ++ [ z ]))) (cong Q⟨ xs ,_⟩ (rev-rev (ys ++ [ z ]))) k j)

 eval∘quot : ∀ xs → eval (quot xs) ≡ xs
 eval∘quot = ++-unit-r

 -- We get our desired equivalence
 quotEquiv : Q₁ ≃ Q
 quotEquiv = isoToEquiv (iso quot eval quot∘eval eval∘quot)

 -- Now it only remains to prove that this is a queue-iso
 quot∘emp : quot emp₁ ≡ emp
 quot∘emp = refl

 quot∘enq : ∀ x xs → quot (enq₁ x xs) ≡ enq x (quot xs)
 quot∘enq x xs = refl

 quot∘deq : ∀ xs → deq-map-forward quot (deq₁ xs) ≡ deq (quot xs)
 quot∘deq [] = refl
 quot∘deq (x ∷ []) = refl
 quot∘deq (x ∷ x' ∷ xs) =
   deq-map-forward-∘ quot (enq₁ x) (deq₁ (x' ∷ xs))
   ∙ sym (deq-map-forward-∘ (enq x) quot (deq₁ (x' ∷ xs)))
   ∙ cong (deq-map-forward (enq x)) (quot∘deq (x' ∷ xs))
   ∙ lemma x x' (rev xs)
   where
   lemma : ∀ x x' ys
     → deq-map-forward (enq x) (deqFlush (ys ++ [ x' ]))
       ≡ deqFlush ((ys ++ [ x' ]) ++ [ x ])
   lemma x x' [] i = inr (tilt [] [] x i , x')
   lemma x x' (y ∷ ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)

 quotEquiv-is-queue-iso : raw-queue-iso One.Raw Raw quotEquiv
 quotEquiv-is-queue-iso = quot∘emp , quot∘enq , quot∘deq

 -- And we get a path between the raw 1Lists and 2Lists
 Raw-1≡2 : One.Raw ≡ Raw
 Raw-1≡2 = sip RawQueue-is-SNS _ _ (quotEquiv , quotEquiv-is-queue-iso)

 -- We derive the axioms for 2List from those for 1List
 WithLaws : Queue
 WithLaws = Q , str Raw , subst (uncurry queue-axioms) Raw-1≡2 (snd (str One.WithLaws))

 -- In particular, the untruncated queue type is a set
 isSetQ : isSet Q
 isSetQ = str WithLaws .snd .fst

 WithLaws-1≡2 : One.WithLaws ≡ WithLaws
 WithLaws-1≡2 = sip Queue-is-SNS _ _ (quotEquiv , quotEquiv-is-queue-iso)

 Finite : FiniteQueue
 Finite = Q , str WithLaws , subst (uncurry finite-queue-axioms) WithLaws-1≡2 (snd (str One.Finite))
