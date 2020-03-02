{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Queue.Base where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.Structures.InftyMagma using (funExtBinEquiv)

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Prod.Base hiding (_×_ ; map-×) renaming (_×Σ_ to _×_)
open import Cubical.Data.Prod.Properties


-- Developing Queues as a standard notion of structure, see
-- https://github.com/ecavallo/cubical/blob/queue/Cubical/Experiments/Queue.agda
-- for the original development

variable
 ℓ ℓ' : Level



-- We start fixing a set A on which we define what it means for a type Q to have
-- a Queue structure (wrt. A)
module Queues-on (A : Type ℓ) (Aset : isSet A) where
 -- A Queue structure has three components, the empty Queue, a push function and a pop function
 -- We first deal with push and pop as separate structures
 left-action-structure : Type ℓ → Type ℓ
 left-action-structure X = A → X → X

 Left-Action : Type (ℓ-suc ℓ)
 Left-Action = Σ (Type ℓ) λ X → left-action-structure X

 left-action-iso : (L M : Left-Action) → L .fst ≃ M .fst → Type ℓ
 left-action-iso (X , l) (Y , m) e = ∀ a x → e .fst (l a x) ≡ m a (e .fst x)

 Left-Action-is-SNS : SNS₁ {ℓ = ℓ} left-action-structure left-action-iso
 Left-Action-is-SNS l m = invEquiv funExtBinEquiv


 -- Now for the pop-map as a structure
 -- First, a few preliminary results that we will need later
 pop-map-forward : {X Y : Type ℓ} → (X → Y)
                  →  Unit ⊎ (X × A) → Unit ⊎ (Y × A)
 pop-map-forward f (inl tt) = inl tt
 pop-map-forward f (inr (x , a)) = inr (f x , a)


 pop-map-forward-∘ :{B C D : Type ℓ}
  (g : C → D) (f : B → C)
  → ∀ r → pop-map-forward {X = C} g (pop-map-forward f r) ≡ pop-map-forward (λ b → g (f b)) r
 pop-map-forward-∘ g f (inl tt) = refl
 pop-map-forward-∘ g f (inr (b , a)) = refl


 pop-map-lemma : {X : Type ℓ} → idfun (Unit ⊎ (X × A)) ≡ pop-map-forward (idfun X)
 pop-map-lemma {X = X} = funExt γ
  where
   γ : ∀ z → z ≡ pop-map-forward (idfun X) z
   γ (inl tt) = refl
   γ (inr xa) = refl



 pop-structure : Type ℓ → Type ℓ
 pop-structure X = X → Unit ⊎ (X × A)

 Pop : Type (ℓ-suc ℓ)
 Pop = Σ (Type ℓ) λ X → pop-structure X

 pop-iso : (P Q : Pop) → P .fst ≃ Q .fst → Type ℓ
 pop-iso (X , p) (Y , q) e = ∀ x → pop-map-forward (e .fst) (p x) ≡ q (e .fst x)

 Pop-is-SNS : SNS₁ {ℓ = ℓ} pop-structure pop-iso
 Pop-is-SNS {X = X} p q = invEquiv
                         (subst (λ f → (∀ x → f (p x) ≡ q x) ≃ (p ≡ q)) pop-map-lemma funExtEquiv)



 -- Now we can do Queues:
 queue-structure : Type ℓ → Type ℓ
 queue-structure Q = Q × (A → Q → Q) × (Q → Unit ⊎ (Q × A))

 Queue : Type (ℓ-suc ℓ)
 Queue = Σ (Type ℓ) λ Q → queue-structure Q

 queue-iso : (Q P : Queue) → Q .fst ≃ P .fst → Type ℓ
 queue-iso (Q₁ , emp₁ , push₁ , pop₁) (Q₂ , emp₂ , push₂ , pop₂) e =
            (e .fst emp₁ ≡ emp₂)
          × (∀ a q → e .fst (push₁ a q) ≡ push₂ a (e .fst q))
          × (∀ q → pop-map-forward (e .fst) (pop₁ q) ≡ pop₂ (e .fst q))



 Queue-is-SNS : SNS₂ {ℓ = ℓ} queue-structure queue-iso
 Queue-is-SNS = join-SNS pointed-structure pointed-iso pointed-is-SNS
             (λ X → (left-action-structure X) × (pop-structure X))
             (λ B C e →  (∀ a q → e .fst (B .snd .fst a q) ≡ C .snd .fst a (e .fst q))
                       × (∀ q → pop-map-forward (e .fst) (B .snd .snd q) ≡ C .snd .snd (e .fst q)))
               (join-SNS left-action-structure left-action-iso (SNS₁→SNS₂ _ _ Left-Action-is-SNS)
                         pop-structure         pop-iso         (SNS₁→SNS₂ _ _ Pop-is-SNS)        )




 -- Should we add further axioms for Queues?
 -- Some suggestions:
 queue-axioms : (Q : Type ℓ) → queue-structure Q → Type ℓ
 queue-axioms Q (emp , push , pop) =   (isSet Q)
                                     × (pop emp ≡ inl tt)
                                     × ∀ a → pop (push a emp) ≡ inr (emp , a)
                                     -- etc.



 -- following Cavallo we can now define 1Lists and 2Lists as Queues on A
 -- and prove that there is a queue-iso between them, this then gives us a path
 1List : Queue
 1List = (Q , emp , push , pop)
  where
   Q = List A
   emp = []
   push = _∷_
   pop : Q → Unit ⊎ (Q × A)
   pop [] = inl tt
   pop (x ∷ []) = inr ([] , x)
   pop (x ∷ x' ∷ xs) = pop-map-forward (push x) (pop (x' ∷ xs))

 -- for later convenience
 Q₁ = 1List .fst
 emp₁ = 1List .snd .fst
 push₁ = 1List .snd .snd .fst
 pop₁ = 1List .snd .snd .snd


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


  -- push into the first list, pop from the second if possible

 emp₂ : Q₂
 emp₂ = Q₂⟨ [] , [] ⟩

 push₂ : A → Q₂ → Q₂
 push₂ a Q₂⟨ xs , ys ⟩ = Q₂⟨ a ∷ xs , ys ⟩
 push₂ a (tilt xs ys z i) = tilt (a ∷ xs) ys z i
 push₂ a (trunc q q' α β i j) =
   trunc _ _ (cong (push₂ a) α) (cong (push₂ a) β) i j


 pop₂Flush : List A → Unit ⊎ (Q₂ × A)
 pop₂Flush [] = inl tt
 pop₂Flush (x ∷ xs) = inr (Q₂⟨ [] , xs ⟩ , x)

 pop₂ : Q₂ → Unit ⊎ (Q₂ × A)
 pop₂ Q₂⟨ xs , [] ⟩ = pop₂Flush (rev xs)
 pop₂ Q₂⟨ xs , y ∷ ys ⟩ = inr (Q₂⟨ xs , ys ⟩ , y)
 pop₂ (tilt xs [] z i) = path i
   where
   path : pop₂Flush (rev (xs ++ [ z ])) ≡ inr (Q₂⟨ xs , [] ⟩ , z)
   path =
     cong pop₂Flush (rev-++ xs [ z ])
     ∙ cong (λ q → inr (q , z)) (sym (multitilt [] [] (rev xs)))
     ∙ cong (λ ys → inr (Q₂⟨ ys , [] ⟩ , z)) (rev-rev xs)
 pop₂ (tilt xs (y ∷ ys) z i) = inr (tilt xs ys z i , y)
 pop₂ (trunc q q' α β i j) =
   isOfHLevelSum 0
     (isProp→isSet isPropUnit)
     (isOfHLevelΣ 2 trunc λ _ → Aset)
     (pop₂ q) (pop₂ q') (cong pop₂ α) (cong pop₂ β)
    i j


 2List : Queue
 2List = (Q₂ , emp₂ , push₂ , pop₂)




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

 quot∘push : ∀ x xs → quot (push₁ x xs) ≡ push₂ x (quot xs)
 quot∘push x xs = refl


 quot∘pop : ∀ xs → pop-map-forward quot (pop₁ xs) ≡ pop₂ (quot xs)
 quot∘pop [] = refl
 quot∘pop (x ∷ []) = refl
 quot∘pop (x ∷ x' ∷ xs) =
   pop-map-forward-∘ quot (push₁ x) (pop₁ (x' ∷ xs))
   ∙ sym (pop-map-forward-∘ (push₂ x) quot (pop₁ (x' ∷ xs)))
   ∙ cong (pop-map-forward (push₂ x)) (quot∘pop (x' ∷ xs))
   ∙ lemma x x' (rev xs)
   where
   lemma : ∀ x x' ys
     → pop-map-forward (push₂ x) (pop₂Flush (ys ++ [ x' ]))
       ≡ pop₂Flush ((ys ++ [ x' ]) ++ [ x ])
   lemma x x' [] i = inr (tilt [] [] x i , x')
   lemma x x' (y ∷ ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)


 quotEquiv-is-queue-iso : queue-iso 1List 2List quotEquiv
 quotEquiv-is-queue-iso = quot∘emp , quot∘push , quot∘pop


 -- And we get the desired Path
 Path-1List-2List : 1List ≡ 2List
 Path-1List-2List = SIP queue-structure queue-iso (SNS₂→SNS₄ Queue-is-SNS) 1List 2List .fst
                   (quotEquiv , quotEquiv-is-queue-iso)
