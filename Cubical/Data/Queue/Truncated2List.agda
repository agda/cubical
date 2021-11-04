{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Queue.Truncated2List where

open import Cubical.Foundations.Everything

open import Cubical.Foundations.SIP
open import Cubical.Structures.Queue

open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.Data.Queue.1List

module Truncated2List {ℓ} (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 data Q : Type ℓ where
   Q⟨_,_⟩ : (xs ys : List A) → Q
   tilt : ∀ xs ys z → Q⟨ xs ++ [ z ] , ys ⟩ ≡ Q⟨ xs , ys ++ [ z ] ⟩
   trunc : (q q' : Q) (α β : q ≡ q') → α ≡ β

 multitilt : (xs ys zs : List A) → Q⟨ xs ++ rev zs , ys ⟩ ≡ Q⟨ xs , ys ++ zs ⟩
 multitilt xs ys [] = cong₂ Q⟨_,_⟩ (++-unit-r xs) (sym (++-unit-r ys))
 multitilt xs ys (z ∷ zs) =
   cong (λ ws → Q⟨ ws , ys ⟩) (sym (++-assoc xs (rev zs) [ z ]))
   ∙ tilt (xs ++ rev zs) ys z
   ∙ multitilt xs (ys ++ [ z ]) zs
   ∙ cong (λ ws → Q⟨ xs , ws ⟩) (++-assoc ys [ z ] zs)

  -- enq into the first list, deq from the second if possible

 emp : Q
 emp = Q⟨ [] , [] ⟩

 enq : A → Q → Q
 enq a Q⟨ xs , ys ⟩ = Q⟨ a ∷ xs , ys ⟩
 enq a (tilt xs ys z i) = tilt (a ∷ xs) ys z i
 enq a (trunc q q' α β i j) =
   trunc _ _ (cong (enq a) α) (cong (enq a) β) i j

 deqFlush : List A → Maybe (Q × A)
 deqFlush [] = nothing
 deqFlush (x ∷ xs) = just (Q⟨ [] , xs ⟩ , x)

 deq : Q → Maybe (Q × A)
 deq Q⟨ xs , [] ⟩ = deqFlush (rev xs)
 deq Q⟨ xs , y ∷ ys ⟩ = just (Q⟨ xs , ys ⟩ , y)
 deq (tilt xs [] z i) = path i
   where
   path : deqFlush (rev (xs ++ [ z ])) ≡ just (Q⟨ xs , [] ⟩ , z)
   path =
     cong deqFlush (rev-++ xs [ z ])
     ∙ cong (λ q → just (q , z)) (sym (multitilt [] [] (rev xs)))
     ∙ cong (λ ys → just (Q⟨ ys , [] ⟩ , z)) (rev-rev xs)
 deq (tilt xs (y ∷ ys) z i) = just (tilt xs ys z i , y)
 deq (trunc q q' α β i j) =
   isOfHLevelMaybe 0
     (isSetΣ trunc λ _ → Aset)
     (deq q) (deq q') (cong deq α) (cong deq β)
    i j

 Raw : RawQueue
 Raw = (Q , emp , enq , deq)

 -- We construct an equivalence to 1Lists and prove this is an equivalence of queue structures

 private
   module One = 1List A Aset
   open One renaming (Q to Q₁; emp to emp₁; enq to enq₁; deq to deq₁) using ()

 quot : Q₁ → Q
 quot xs = Q⟨ xs , [] ⟩

 eval : Q → Q₁
 eval Q⟨ xs , ys ⟩ = xs ++ rev ys
 eval (tilt xs ys z i) = path i
   where
   path : (xs ++ [ z ]) ++ rev ys ≡ xs ++ rev (ys ++ [ z ])
   path =
     ++-assoc xs [ z ] (rev ys)
     ∙ cong (_++_ xs) (sym (rev-++ ys [ z ]))
 eval (trunc q q' α β i j) = -- truncated case
   isOfHLevelList 0 Aset (eval q) (eval q') (cong eval α) (cong eval β) i j

 quot∘eval : ∀ q → quot (eval q) ≡ q
 quot∘eval Q⟨ xs , ys ⟩ = multitilt xs [] ys
 quot∘eval (tilt xs ys z i) = -- truncated case
   isOfHLevelPathP'
     {A = λ i → quot (eval (tilt xs ys z i)) ≡ tilt xs ys z i}
     0
     (trunc _ _)
     (multitilt (xs ++ [ z ]) [] ys) (multitilt xs [] (ys ++ [ z ]))
     .fst i
 quot∘eval (trunc q q' α β i j) = -- truncated case
   isOfHLevelPathP'
     {A = λ i →
       PathP (λ j → quot (eval (trunc q q' α β i j)) ≡ trunc q q' α β i j)
         (quot∘eval q) (quot∘eval q')}
     0
     (isOfHLevelPathP' 1 (isOfHLevelSuc 2 trunc _ _) _ _)
     (cong quot∘eval α) (cong quot∘eval β)
     .fst i j

 eval∘quot : ∀ xs → eval (quot xs) ≡ xs
 eval∘quot = ++-unit-r

 -- We get our desired equivalence
 quotEquiv : Q₁ ≃ Q
 quotEquiv = isoToEquiv (iso quot eval quot∘eval eval∘quot)

 -- Now it only remains to prove that this is an equivalence of queue structures
 quot∘emp : quot emp₁ ≡ emp
 quot∘emp = refl

 quot∘enq : ∀ x xs → quot (enq₁ x xs) ≡ enq x (quot xs)
 quot∘enq x xs = refl

 quot∘deq : ∀ xs → deqMap quot (deq₁ xs) ≡ deq (quot xs)
 quot∘deq [] = refl
 quot∘deq (x ∷ []) = refl
 quot∘deq (x ∷ x' ∷ xs) =
   deqMap-∘ quot (enq₁ x) (deq₁ (x' ∷ xs))
   ∙ sym (deqMap-∘ (enq x) quot (deq₁ (x' ∷ xs)))
   ∙ cong (deqMap (enq x)) (quot∘deq (x' ∷ xs))
   ∙ lemma x x' (rev xs)
   where
   lemma : ∀ x x' ys
     → deqMap (enq x) (deqFlush (ys ++ [ x' ]))
       ≡ deqFlush ((ys ++ [ x' ]) ++ [ x ])
   lemma x x' [] i = just (tilt [] [] x i , x')
   lemma x x' (y ∷ ys) i = just (tilt [] (ys ++ [ x' ]) x i , y)


 quotEquivHasQueueEquivStr : RawQueueEquivStr One.Raw Raw quotEquiv
 quotEquivHasQueueEquivStr = quot∘emp , quot∘enq , quot∘deq

 -- And we get a path between the raw 1Lists and 2Lists
 Raw-1≡2 : One.Raw ≡ Raw
 Raw-1≡2 = sip rawQueueUnivalentStr _ _ (quotEquiv , quotEquivHasQueueEquivStr)

 -- We derive the axioms for 2List from those for 1List
 WithLaws : Queue
 WithLaws = Q , str Raw , subst (uncurry QueueAxioms) Raw-1≡2 (snd (str One.WithLaws))

 WithLaws-1≡2 : One.WithLaws ≡ WithLaws
 WithLaws-1≡2 = sip queueUnivalentStr _ _ (quotEquiv , quotEquivHasQueueEquivStr)

 Finite : FiniteQueue
 Finite = Q , str WithLaws , subst (uncurry FiniteQueueAxioms) WithLaws-1≡2 (snd (str One.Finite))
