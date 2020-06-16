{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Queue.Untruncated2ListInvariant where

open import Cubical.Foundations.Everything
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Prod

module Untruncated2ListInvariant {ℓ} (A : Type ℓ) where

 -- Invariant
 Inv : List A → List A → Type ℓ
 Inv xs ys = ys ≡ [] → xs ≡ []

 Inv-isProp : (xs ys : List A) → isProp (Inv xs ys)
 Inv-isProp xs ys = λ p q → λ i Hf → list≡nil-isProp (p Hf) (q Hf) i

 Inv-ys≡ys' : {xs ys ys' : List A} → (p : ys ≡ ys') →
   (invL : Inv xs ys) → (invR : Inv xs ys') → PathP (λ i → Inv xs (p i)) invL invR
 Inv-ys≡ys' {xs = xs} p invL invR = isProp→PathP (λ i → Inv-isProp xs (p i)) invL invR

 inv-ys-cons : {xs ys : List A} {y : A} → Inv xs (y ∷ ys)
 inv-ys-cons contra = ⊥.rec (¬cons≡nil contra)

 inv-ys-snoc : {xs ys : List A} → {y : A} → Inv xs (ys ∷ʳ y)
 inv-ys-snoc contra = ⊥.rec (¬snoc≡nil contra)

 inv-xs-nil : {ys : List A} → Inv [] ys
 inv-xs-nil ys = refl

 inv-invalid : {xs : List A} {x : A} → Inv (xs ∷ʳ x) [] → ⊥
 inv-invalid inv = ¬snoc≡nil (inv refl)

 -- Queue
 data Q : Type ℓ where
   Q⟨_,_!_⟩ : (xs ys : List A) → (inv : Inv xs ys) → Q
   tilt : ∀ xs ys z l r → Q⟨ xs ++ [ z ] , ys ! l ⟩ ≡ Q⟨ xs , ys ++ [ z ] ! r ⟩

 Q-ys≡ys' : ∀ xs {ys ys' : List A} l r → (p : ys ≡ ys') → Q⟨ xs , ys ! l ⟩ ≡ Q⟨ xs , ys' ! r ⟩
 Q-ys≡ys' xs l r p i = Q⟨ xs , p i ! Inv-ys≡ys' p l r i ⟩

 flush-xs : ∀ xs ys l r → Q⟨ xs , ys ! l ⟩ ≡ Q⟨ [] , ys ++ rev xs ! r ⟩
 flush-xs xs ys l r = helper xs ys l r (snocView xs)
   where
     helper : ∀ xs ys l r → SnocView xs → Q⟨ xs , ys ! l ⟩ ≡ Q⟨ [] , ys ++ rev xs ! r ⟩
     helper .[] ys l r nil i = Q⟨ [] , ++-unit-r ys (~ i) ! Inv-ys≡ys' (++-unit-r ys ⁻¹) l r i  ⟩
     helper .(xs ∷ʳ x) ys l r (snoc x xs s) = move-x ∙ IH ∙ Q-ys≡ys' [] inv-xs-nil r lemma
       where
       move-x : Q⟨ xs ∷ʳ x , ys ! l ⟩ ≡ Q⟨ xs , ys ∷ʳ x ! inv-ys-snoc ⟩
       move-x = tilt xs ys x l inv-ys-snoc
       IH : Q⟨ xs , ys ∷ʳ x ! inv-ys-snoc ⟩ ≡ Q⟨ [] , (ys ∷ʳ x) ++ rev xs ! inv-xs-nil ⟩
       IH = helper xs (ys ∷ʳ x) inv-ys-snoc inv-xs-nil s
       lemma : (ys ∷ʳ x) ++ rev xs ≡ ys ++ rev (xs ∷ʳ x)
       lemma = ++-assoc ys (x ∷ []) (rev xs) ∙ cong (_++_ ys) (cons≡rev-snoc x xs)

 emp : Q
 emp = Q⟨ [] , [] ! inv-xs-nil ⟩

 enq : A → Q → Q
 enq a Q⟨ xs , [] ! inv ⟩ = Q⟨ xs , a ∷ [] ! inv-ys-cons ⟩
 enq a Q⟨ xs , y ∷ ys ! inv ⟩ = Q⟨ a ∷ xs , y ∷ ys ! inv-ys-cons ⟩
 enq a (tilt xs [] z l r i) = proof i
   where
   proof : Q⟨ xs ++ z ∷ [] , a ∷ [] ! inv-ys-cons ⟩ ≡ Q⟨ a ∷ xs , z ∷ [] ! inv-ys-cons ⟩
   proof = ⊥.rec (inv-invalid l)
 enq a (tilt xs (y ∷ ys) z l r i) = tilt (a ∷ xs) (y ∷ ys) z inv-ys-cons inv-ys-cons i

 deq : Q → Unit ⊎ (Q × A)
 deq Q⟨ xs , [] ! inv ⟩ = inl tt
 deq Q⟨ xs , y ∷ [] ! inv ⟩ = inr (Q⟨ [] , rev xs ! inv-xs-nil ⟩ , y)
 deq Q⟨ xs , y₁ ∷ y₂ ∷ ys ! inv ⟩ = inr (Q⟨ xs , y₂ ∷ ys ! inv-ys-cons ⟩ , y₁)
 deq (tilt xs [] z l r i) = proof i
   where
   proof : inl tt ≡ inr (Q⟨ [] , rev xs ! inv-xs-nil ⟩ , z)
   proof = ⊥.rec (inv-invalid l)
 deq (tilt xs (y ∷ []) z l r i) = inr (proof i , y)
   where
   proof : Q⟨ [] , rev (xs ∷ʳ z) ! inv-xs-nil ⟩ ≡ Q⟨ xs , z ∷ [] ! inv-ys-cons ⟩
   proof = Q-ys≡ys' [] inv-xs-nil inv-ys-cons (cons≡rev-snoc z xs ⁻¹) ∙ flush-xs xs (z ∷ []) inv-ys-cons inv-ys-cons ⁻¹
 deq (tilt xs (y₁ ∷ y₂ ∷ ys) z l r i) = inr ((tilt xs (y₂ ∷ ys) z inv-ys-cons inv-ys-cons i) , y₁)
