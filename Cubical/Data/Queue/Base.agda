{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue.Base where

open import Cubical.Foundations.Everything

open import Cubical.Foundations.SIP
open import Cubical.Structures.Queue

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Sigma

module _ (A : Type ℓ) (Aset : isSet A) where
 open Queues-on A Aset

 -- following Cavallo we can now define Raw1Lists and Raw2Lists as Queues on A
 -- and prove that there is a queue-iso between them, this then gives us a path
 Raw1List : RawQueue
 Raw1List = (Q , emp , enq , deq)
  where
   Q = List A
   emp = []
   enq = _∷_
   deq : Q → Unit ⊎ (Q × A)
   deq [] = inl tt
   deq (x ∷ []) = inr ([] , x)
   deq (x ∷ x' ∷ xs) = deq-map-forward (enq x) (deq (x' ∷ xs))

 -- for later convenience
 Q₁ = typ Raw1List
 emp₁ = str Raw1List .fst
 enq₁ = str Raw1List .snd .fst
 deq₁ = str Raw1List .snd .snd

 1List : Queue
 1List = (Q₁ , str Raw1List , isSetQ , refl , deq-enq , isInjDeq)
  where
   S = str Raw1List

   isSetQ : isSet Q₁
   isSetQ = isOfHLevelList 0 Aset

   deq-enq : ∀ a q → deq₁ (enq₁ a q) ≡ inr (returnOrEnq S a (deq₁ q))
   deq-enq a [] = refl
   deq-enq a (x ∷ []) = refl
   deq-enq a (x ∷ x' ∷ xs) =
     subst
       (λ t →
         deq-map-forward (enq₁ a) (deq-map-forward (enq₁ x) t)
         ≡ inr (returnOrEnq S a (deq-map-forward (enq₁ x) t)))
       (deq-enq x' xs ⁻¹)
       refl

   isInjReturnOrEnq : ∀ a a' qr qr'
     → returnOrEnq S a qr ≡ returnOrEnq S a' qr'
     → (a ≡ a') × (qr ≡ qr')
   isInjReturnOrEnq a a' (inl _) (inl _) p = cong snd p , refl
   isInjReturnOrEnq a a' (inl _) (inr (q' , b')) p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (inr (q , b)) (inl _) p =
     ⊥.rec (lower (ListPath.encode _ _ (cong fst p)))
   isInjReturnOrEnq a a' (inr (q , b)) (inr (q' , b')) p =
     fst c , cong inr (ΣPathP (ListPath.decode _ _ (snd c) , cong snd p))
     where
     c = ListPath.encode _ _ (cong fst p)

   isInjDeq-lemma : ∀ q q' → SumPath.Cover (deq₁ q) (deq₁ q') → q ≡ q'
   isInjDeq-lemma [] [] _ = refl
   isInjDeq-lemma [] (y ∷ q') c =
     ⊥.rec (lower (subst (SumPath.Cover (inl tt)) (deq-enq y q') c))
   isInjDeq-lemma (x ∷ q) [] c =
     ⊥.rec (lower (subst (λ r → SumPath.Cover r (inl tt)) (deq-enq x q) c))
   isInjDeq-lemma (x ∷ q) (y ∷ q') c =
     cong₂ _∷_ (fst p) (isInjDeq-lemma q q' (SumPath.encode _ _ (snd p)))
     where
     p : (x ≡ y) × (deq₁ q ≡ deq₁ q')
     p =
       isInjReturnOrEnq _ _ _ _
         (lower (subst (uncurry SumPath.Cover) (ΣPathP (deq-enq x q , deq-enq y q')) c))

   isInjDeq : ∀ q q' → deq₁ q ≡ deq₁ q' → q ≡ q'
   isInjDeq _ _ p = isInjDeq-lemma _ _ (SumPath.encode _ _ p)


 -- Now for 2Lists
 data Q₂ : Set ℓ where
   Q₂⟨_,_⟩ : (xs ys : List A) → Q₂
   tilt : ∀ xs ys z → Q₂⟨ xs ++ [ z ] , ys ⟩ ≡ Q₂⟨ xs , ys ++ [ z ] ⟩
   trunc : (q q' : Q₂) (α β : q ≡ q') → α ≡ β

 multitilt : (xs ys zs : List A) → Q₂⟨ xs ++ rev zs , ys ⟩ ≡ Q₂⟨ xs , ys ++ zs ⟩
 multitilt xs ys [] = cong₂ Q₂⟨_,_⟩ (++-unit-r xs) (sym (++-unit-r ys))
 multitilt xs ys (z ∷ zs) =
   cong (λ ws → Q₂⟨ ws , ys ⟩) (sym (++-assoc xs (rev zs) [ z ]))
   ∙ tilt (xs ++ rev zs) ys z
   ∙ multitilt xs (ys ++ [ z ]) zs
   ∙ cong (λ ws → Q₂⟨ xs , ws ⟩) (++-assoc ys [ z ] zs)


  -- enq into the first list, deq from the second if possible

 emp₂ : Q₂
 emp₂ = Q₂⟨ [] , [] ⟩

 enq₂ : A → Q₂ → Q₂
 enq₂ a Q₂⟨ xs , ys ⟩ = Q₂⟨ a ∷ xs , ys ⟩
 enq₂ a (tilt xs ys z i) = tilt (a ∷ xs) ys z i
 enq₂ a (trunc q q' α β i j) =
   trunc _ _ (cong (enq₂ a) α) (cong (enq₂ a) β) i j


 deq₂Flush : List A → Unit ⊎ (Q₂ × A)
 deq₂Flush [] = inl tt
 deq₂Flush (x ∷ xs) = inr (Q₂⟨ [] , xs ⟩ , x)

 deq₂ : Q₂ → Unit ⊎ (Q₂ × A)
 deq₂ Q₂⟨ xs , [] ⟩ = deq₂Flush (rev xs)
 deq₂ Q₂⟨ xs , y ∷ ys ⟩ = inr (Q₂⟨ xs , ys ⟩ , y)
 deq₂ (tilt xs [] z i) = path i
   where
   path : deq₂Flush (rev (xs ++ [ z ])) ≡ inr (Q₂⟨ xs , [] ⟩ , z)
   path =
     cong deq₂Flush (rev-++ xs [ z ])
     ∙ cong (λ q → inr (q , z)) (sym (multitilt [] [] (rev xs)))
     ∙ cong (λ ys → inr (Q₂⟨ ys , [] ⟩ , z)) (rev-rev xs)
 deq₂ (tilt xs (y ∷ ys) z i) = inr (tilt xs ys z i , y)
 deq₂ (trunc q q' α β i j) =
   isOfHLevelSum 0
     (isProp→isSet isPropUnit)
     (isSetΣ trunc λ _ → Aset)
     (deq₂ q) (deq₂ q') (cong deq₂ α) (cong deq₂ β)
    i j


 Raw2List : RawQueue
 Raw2List = (Q₂ , emp₂ , enq₂ , deq₂)

 -- We construct an equivalence Q₁≃Q₂ and prove that this is a queue-iso
 quot : Q₁ → Q₂
 quot xs = Q₂⟨ xs , [] ⟩

 eval : Q₂ → Q₁
 eval Q₂⟨ xs , ys ⟩ = xs ++ rev ys
 eval (tilt xs ys z i) = path i
   where
   path : (xs ++ [ z ]) ++ rev ys ≡ xs ++ rev (ys ++ [ z ])
   path =
     ++-assoc xs [ z ] (rev ys)
     ∙ cong (_++_ xs) (sym (rev-++ ys [ z ]))
 eval (trunc q q' α β i j) = -- truncated case
   isOfHLevelList 0 Aset (eval q) (eval q') (cong eval α) (cong eval β) i j




 quot∘eval : ∀ q → quot (eval q) ≡ q
 quot∘eval Q₂⟨ xs , ys ⟩ = multitilt xs [] ys
 quot∘eval (tilt xs ys z i) = -- truncated case
   isOfHLevelPathP'
     {A = λ i → quot (eval (tilt xs ys z i)) ≡ tilt xs ys z i}
     0
     (λ _ → trunc _ _)
     (multitilt (xs ++ [ z ]) [] ys) (multitilt xs [] (ys ++ [ z ]))
     .fst i
 quot∘eval (trunc q q' α β i j) = -- truncated case
   isOfHLevelPathP'
     {A = λ i →
       PathP (λ j → quot (eval (trunc q q' α β i j)) ≡ trunc q q' α β i j)
         (quot∘eval q) (quot∘eval q')}
     0
     (λ _ → isOfHLevelPathP' 1 (λ _ → isOfHLevelSuc 2 trunc _ _) _ _)
     (cong quot∘eval α) (cong quot∘eval β)
     .fst i j


 eval∘quot : ∀ xs → eval (quot xs) ≡ xs
 eval∘quot = ++-unit-r


 -- We get our desired equivalence
 quotEquiv : Q₁ ≃ Q₂
 quotEquiv = isoToEquiv (iso quot eval quot∘eval eval∘quot)

 -- Now it only remains to prove that this is a queue-iso
 quot∘emp : quot emp₁ ≡ emp₂
 quot∘emp = refl

 quot∘enq : ∀ x xs → quot (enq₁ x xs) ≡ enq₂ x (quot xs)
 quot∘enq x xs = refl


 quot∘deq : ∀ xs → deq-map-forward quot (deq₁ xs) ≡ deq₂ (quot xs)
 quot∘deq [] = refl
 quot∘deq (x ∷ []) = refl
 quot∘deq (x ∷ x' ∷ xs) =
   deq-map-forward-∘ quot (enq₁ x) (deq₁ (x' ∷ xs))
   ∙ sym (deq-map-forward-∘ (enq₂ x) quot (deq₁ (x' ∷ xs)))
   ∙ cong (deq-map-forward (enq₂ x)) (quot∘deq (x' ∷ xs))
   ∙ lemma x x' (rev xs)
   where
   lemma : ∀ x x' ys
     → deq-map-forward (enq₂ x) (deq₂Flush (ys ++ [ x' ]))
       ≡ deq₂Flush ((ys ++ [ x' ]) ++ [ x ])
   lemma x x' [] i = inr (tilt [] [] x i , x')
   lemma x x' (y ∷ ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)


 quotEquiv-is-queue-iso : raw-queue-iso Raw1List Raw2List quotEquiv
 quotEquiv-is-queue-iso = quot∘emp , quot∘enq , quot∘deq


 -- And we get a path between the raw 1Lists and 2Lists
 Path-Raw1List-Raw2List : Raw1List ≡ Raw2List
 Path-Raw1List-Raw2List = sip RawQueue-is-SNS Raw1List Raw2List (quotEquiv , quotEquiv-is-queue-iso)

 -- We derive the axioms for 2List from those for 1List
 2List : Queue
 2List = Q₂ , str Raw2List , subst (uncurry queue-axioms) Path-Raw1List-Raw2List (snd (str 1List))

 Path-1List-2List : 1List ≡ 2List
 Path-1List-2List = sip Queue-is-SNS 1List 2List (quotEquiv , quotEquiv-is-queue-iso)
