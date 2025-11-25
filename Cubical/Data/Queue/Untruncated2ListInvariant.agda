module Cubical.Data.Queue.Untruncated2ListInvariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Prod

module Untruncated2ListInvariant {ℓ} (A : Type ℓ) where

 -- Invariant
 Inv : List A → List A → Type ℓ
 Inv xs ys = ys ≡ [] → xs ≡ []

 isPropInv : (xs ys : List A) → isProp (Inv xs ys)
 isPropInv xs ys = isPropΠ λ _ → isPropXs≡[]

 Inv-ys≡ys' : {xs ys ys' : List A} → (p : ys ≡ ys') →
   (invL : Inv xs ys) → (invR : Inv xs ys') → PathP (λ i → Inv xs (p i)) invL invR
 Inv-ys≡ys' {xs = xs} p invL invR = isProp→PathP (λ i → isPropInv xs (p i)) invL invR

 inv-xs-∷ : {xs ys : List A} {y : A} → Inv xs (y ∷ ys)
 inv-xs-∷ contra = ⊥.rec (¬cons≡nil contra)

 inv-xs-∷ʳ : {xs ys : List A} → {y : A} → Inv xs (ys ∷ʳ y)
 inv-xs-∷ʳ contra = ⊥.rec (¬snoc≡nil contra)

 inv-[]-ys : {ys : List A} → Inv [] ys
 inv-[]-ys ys = refl

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
     helper .(xs ∷ʳ x) ys l r (snoc x xs s) = move-x ∙ IH ∙ Q-ys≡ys' [] inv-[]-ys r lemma
       where
       move-x : Q⟨ xs ∷ʳ x , ys ! l ⟩ ≡ Q⟨ xs , ys ∷ʳ x ! inv-xs-∷ʳ ⟩
       move-x = tilt xs ys x l inv-xs-∷ʳ
       IH : Q⟨ xs , ys ∷ʳ x ! inv-xs-∷ʳ ⟩ ≡ Q⟨ [] , (ys ∷ʳ x) ++ rev xs ! inv-[]-ys ⟩
       IH = helper xs (ys ∷ʳ x) inv-xs-∷ʳ inv-[]-ys s
       lemma : (ys ∷ʳ x) ++ rev xs ≡ ys ++ rev (xs ∷ʳ x)
       lemma = ++-assoc ys (x ∷ []) (rev xs) ∙ cong (ys ++_) (cons≡rev-snoc x xs)

 emp : Q
 emp = Q⟨ [] , [] ! inv-[]-ys ⟩

 enq : A → Q → Q
 enq a Q⟨ xs , [] ! inv ⟩ = Q⟨ xs , a ∷ [] ! inv-xs-∷ ⟩
 enq a Q⟨ xs , y ∷ ys ! inv ⟩ = Q⟨ a ∷ xs , y ∷ ys ! inv-xs-∷ ⟩
 enq a (tilt xs [] z l r i) = proof i
   where
   proof : Q⟨ xs ++ z ∷ [] , a ∷ [] ! inv-xs-∷ ⟩ ≡ Q⟨ a ∷ xs , z ∷ [] ! inv-xs-∷ ⟩
   proof = ⊥.rec (inv-invalid l)
 enq a (tilt xs (y ∷ ys) z l r i) = tilt (a ∷ xs) (y ∷ ys) z inv-xs-∷ inv-xs-∷ i

 deq : Q → Maybe (Q × A)
 deq Q⟨ xs , [] ! inv ⟩ = nothing
 deq Q⟨ xs , y ∷ [] ! inv ⟩ = just (Q⟨ [] , rev xs ! inv-[]-ys ⟩ , y)
 deq Q⟨ xs , y₁ ∷ y₂ ∷ ys ! inv ⟩ = just (Q⟨ xs , y₂ ∷ ys ! inv-xs-∷ ⟩ , y₁)
 deq (tilt xs [] z l r i) = proof i
   where
   proof : nothing ≡ just (Q⟨ [] , rev xs ! inv-[]-ys ⟩ , z)
   proof = ⊥.rec (inv-invalid l)
 deq (tilt xs (y ∷ []) z l r i) = just (proof i , y)
   where
   proof : Q⟨ [] , rev (xs ∷ʳ z) ! inv-[]-ys ⟩ ≡ Q⟨ xs , z ∷ [] ! inv-xs-∷ ⟩
   proof = Q-ys≡ys' [] inv-[]-ys inv-xs-∷ (cons≡rev-snoc z xs ⁻¹) ∙ flush-xs xs (z ∷ []) inv-xs-∷ inv-xs-∷ ⁻¹
 deq (tilt xs (y₁ ∷ y₂ ∷ ys) z l r i) = just ((tilt xs (y₂ ∷ ys) z inv-xs-∷ inv-xs-∷ i) , y₁)
