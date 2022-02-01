
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat renaming (zero to ℕzero ; suc to ℕsuc
                                      ;znots to ℕznots ; snotz to  ℕsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary

private
 variable
   ℓ ℓ' : Level
   A : Type ℓ


znots : ∀{k} {m : Fin k} → ¬ (zero ≡ (suc m))
znots {k} {m} x = subst (Fin.rec (Fin k) ⊥) x m

snotz : ∀{k} {m : Fin k} → ¬ ((suc m) ≡ zero)
snotz {k} {m} x = subst (Fin.rec ⊥ (Fin k)) x m

isPropFin0 : isProp (Fin 0)
isPropFin0 = Empty.rec ∘ ¬Fin0

isContrFin1 : isContr (Fin 1)
isContrFin1 .fst = zero
isContrFin1 .snd zero = refl

injSucFin : ∀ {n} { p q : Fin n} → suc p ≡ suc q → p ≡ q
injSucFin {ℕsuc ℕzero} {zero} {zero} pf = refl
injSucFin {ℕsuc (ℕsuc n)} pf = cong predFin pf


discreteFin : ∀{k} → Discrete (Fin k)
discreteFin zero zero = yes refl
discreteFin zero (suc y) = no znots
discreteFin (suc x) zero = no snotz
discreteFin (suc x) (suc y) with discreteFin x y
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (injSucFin q))

isSetFin : ∀{k} → isSet (Fin k)
isSetFin = Discrete→isSet discreteFin


weakenRespToℕ : ∀ {n} (i : Fin n) → toℕ (weakenFin i) ≡ toℕ i
weakenRespToℕ zero = refl
weakenRespToℕ (suc i) = cong ℕsuc (weakenRespToℕ i)

toℕ<n : ∀ {n} (i : Fin n) → toℕ i < n
toℕ<n {n = ℕsuc n} zero = n , +-comm n 1
toℕ<n {n = ℕsuc n} (suc i) = toℕ<n i .fst , +-suc _ _ ∙ cong ℕsuc (toℕ<n i .snd)

toFin : {n : ℕ} (m : ℕ) → m < n → Fin n
toFin {n = ℕzero} _ m<0 = Empty.rec (¬-<-zero m<0)
toFin {n = ℕsuc n} _ (ℕzero , _) = fromℕ n --in this case we have m≡n
toFin {n = ℕsuc n} m (ℕsuc k , p) = weakenFin (toFin m (k , cong predℕ p))

toFin0≡0 : {n : ℕ} (p : 0 < ℕsuc n) → toFin 0 p ≡ zero
toFin0≡0 (ℕzero , p) = subst (λ x → fromℕ x ≡ zero) (cong predℕ p) refl
toFin0≡0 {ℕzero} (ℕsuc k , p) = Empty.rec (ℕsnotz (+-comm 1 k ∙ (cong predℕ p)))
toFin0≡0 {ℕsuc n} (ℕsuc k , p) =
         subst (λ x → weakenFin x ≡ zero) (sym (toFin0≡0 (k , cong predℕ p))) refl

++FinAssoc : {n m k : ℕ} (U : FinVec A n) (V : FinVec A m) (W : FinVec A k)
           → PathP (λ i → FinVec A (+-assoc n m k i)) (U ++Fin (V ++Fin W)) ((U ++Fin V) ++Fin W)
++FinAssoc {n = ℕzero} _ _ _ = refl
++FinAssoc {n = ℕsuc n} U V W i zero = U zero
++FinAssoc {n = ℕsuc n} U V W i (suc ind) = ++FinAssoc (U ∘ suc) V W i ind

++FinRid : {n : ℕ} (U : FinVec A n) (V : FinVec A 0)
         → PathP (λ i → FinVec A (+-zero n i)) (U ++Fin V) U
++FinRid {n = ℕzero} U V = funExt λ i → Empty.rec (¬Fin0 i)
++FinRid {n = ℕsuc n} U V i zero = U zero
++FinRid {n = ℕsuc n} U V i (suc ind) = ++FinRid (U ∘ suc) V i ind

++FinElim : {P : A → Type ℓ'} {n m : ℕ} (U : FinVec A n) (V : FinVec A m)
          → (∀ i → P (U i)) → (∀ i → P (V i)) → ∀ i → P ((U ++Fin V) i)
++FinElim {n = ℕzero} _ _ _ PVHyp i = PVHyp i
++FinElim {n = ℕsuc n} _ _ PUHyp _ zero = PUHyp zero
++FinElim {P = P} {n = ℕsuc n} U V PUHyp PVHyp (suc i) =
          ++FinElim {P = P} (U ∘ suc) V (λ i → PUHyp (suc i)) PVHyp i

++FinPres∈ : {n m : ℕ} {α : FinVec A n} {β : FinVec A m} (S : ℙ A)
           → (∀ i → α i ∈ S) → (∀ i → β i ∈ S) → ∀ i → (α ++Fin β) i ∈ S
++FinPres∈ {n = ℕzero} S hα hβ i = hβ i
++FinPres∈ {n = ℕsuc n} S hα hβ zero = hα zero
++FinPres∈ {n = ℕsuc n} S hα hβ (suc i) = ++FinPres∈ S (hα ∘ suc) hβ i

-- sends i to n+i if toℕ i < m and to i∸n otherwise
-- then +Shuffle²≡id and over the induced path (i.e. in PathP (ua +ShuffleEquiv))
-- ++Fin is commutative, but how to go from there?
+Shuffle : (m n : ℕ) → Fin (m + n) → Fin (n + m)
+Shuffle m n i with <Dec (toℕ i) m
... | yes i<m = toFin (n + (toℕ i)) (<-k+ i<m)
... | no ¬i<m = toFin (toℕ i ∸ m)
                  (subst (λ x → toℕ i ∸ m < x) (+-comm m n) (≤<-trans (∸-≤ (toℕ i) m) (toℕ<n i)))


-- Proof that Fin n ⊎ Fin m ≃ Fin (n+m)
module FinSumChar where

 fun : (n m : ℕ) → Fin n ⊎ Fin m → Fin (n + m)
 fun ℕzero m (inr i) = i
 fun (ℕsuc n) m (inl zero) = zero
 fun (ℕsuc n) m (inl (suc i)) = suc (fun n m (inl i))
 fun (ℕsuc n) m (inr i) = suc (fun n m (inr i))

 invSucAux : (n m : ℕ) → Fin n ⊎ Fin m → Fin (ℕsuc n) ⊎ Fin m
 invSucAux n m (inl i) = inl (suc i)
 invSucAux n m (inr i) = inr i

 inv : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
 inv ℕzero m i = inr i
 inv (ℕsuc n) m zero = inl zero
 inv (ℕsuc n) m (suc i) = invSucAux n m (inv n m i)

 ret : (n m : ℕ) (i : Fin n ⊎ Fin m) → inv n m (fun n m i) ≡ i
 ret ℕzero m (inr i) = refl
 ret (ℕsuc n) m (inl zero) = refl
 ret (ℕsuc n) m (inl (suc i)) = subst (λ x → invSucAux n m x ≡ inl (suc i))
                                       (sym (ret n m (inl i))) refl
 ret (ℕsuc n) m (inr i) = subst (λ x → invSucAux n m x ≡ inr i) (sym (ret n m (inr i))) refl

 sec : (n m : ℕ) (i : Fin (n + m)) → fun n m (inv n m i) ≡ i
 sec ℕzero m i = refl
 sec (ℕsuc n) m zero = refl
 sec (ℕsuc n) m (suc i) = helperPath (inv n m i) ∙ cong suc (sec n m i)
  where
  helperPath : ∀ x → fun (ℕsuc n) m (invSucAux n m x) ≡ suc (fun n m x)
  helperPath (inl _) = refl
  helperPath (inr _) = refl

 Equiv : (n m : ℕ) → Fin n ⊎ Fin m ≃ Fin (n + m)
 Equiv n m = isoToEquiv (iso (fun n m) (inv n m) (sec n m) (ret n m))

 ++FinInl : (n m : ℕ) (U : FinVec A n) (W : FinVec A m) (i : Fin n)
          → U i ≡ (U ++Fin W) (fun n m (inl i))
 ++FinInl (ℕsuc n) m U W zero = refl
 ++FinInl (ℕsuc n) m U W (suc i) = ++FinInl n m (U ∘ suc) W i

 ++FinInr : (n m : ℕ) (U : FinVec A n) (W : FinVec A m) (i : Fin m)
          → W i ≡ (U ++Fin W) (fun n m (inr i))
 ++FinInr ℕzero (ℕsuc m) U W i = refl
 ++FinInr (ℕsuc n) m U W i = ++FinInr n m (U ∘ suc) W i

-- Proof that Fin n × Fin m ≃ Fin nm
module FinProdChar where

 open Iso
 sucProdToSumIso : (n m : ℕ) → Iso (Fin (ℕsuc n) × Fin m) (Fin m ⊎ (Fin n × Fin m))
 fun (sucProdToSumIso n m) (zero , j) = inl j
 fun (sucProdToSumIso n m) (suc i , j) = inr (i , j)
 inv (sucProdToSumIso n m) (inl j) = zero , j
 inv (sucProdToSumIso n m) (inr (i , j)) = suc i , j
 rightInv (sucProdToSumIso n m) (inl j) = refl
 rightInv (sucProdToSumIso n m) (inr (i , j)) = refl
 leftInv (sucProdToSumIso n m) (zero , j) = refl
 leftInv (sucProdToSumIso n m) (suc i , j) = refl

 Equiv : (n m : ℕ) → (Fin n × Fin m) ≃ Fin (n · m)
 Equiv ℕzero m = uninhabEquiv (λ x → ¬Fin0 (fst x)) ¬Fin0
 Equiv (ℕsuc n) m = Fin (ℕsuc n) × Fin m    ≃⟨ isoToEquiv (sucProdToSumIso n m) ⟩
                    Fin m ⊎ (Fin n × Fin m) ≃⟨ isoToEquiv (⊎Iso idIso (equivToIso (Equiv n m))) ⟩
                    Fin m ⊎ Fin (n · m)     ≃⟨ FinSumChar.Equiv m (n · m) ⟩
                    Fin (m + n · m)         ■
