
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset

open import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat renaming (zero to ℕzero ; suc to ℕsuc
                                      ;znots to ℕznots ; snotz to  ℕsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary

private
 variable
   ℓ : Level
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

-- or maybe more useful
-- ++FinShuffleComm : ∀ (m n : ℕ) (U : FinVec A m) (V : FinVec A n) (i : Fin (m + n))
--                  → (U ++Fin V) i ≡ (V ++Fin U) (+Shuffle m n i)
-- -- ++FinShuffleComm ℕzero n U V i = {!!} --  with (<Dec (toℕ i) ℕzero)
-- -- -- ... | x = ?
-- -- -- ... | no ¬i<0 = ?
-- -- ++FinShuffleComm (ℕsuc m) n U V zero = {!!}
-- -- ++FinShuffleComm (ℕsuc m) n U V (suc i) = {!!}
-- ++FinShuffleComm m n U V i with <Dec (toℕ i) m
-- ++FinShuffleComm ℕzero n U V i | yes i<0 = Empty.rec (¬-<-zero i<0)
-- ++FinShuffleComm (ℕsuc m) ℕzero U V zero | yes 0<m = cong U (sym (toFin0≡0 (<-k+ 0<m)))
-- ++FinShuffleComm (ℕsuc m) (ℕsuc n) U V zero | yes 0<m = {!!}
-- ++FinShuffleComm (ℕsuc m) n U V (suc i) | yes i+1<m+1 = ++FinShuffleComm m n (U ∘ suc) V i ∙ {!!}
-- -- ++FinShuffleComm (ℕsuc m) ℕzero U V (suc i) | yes _ = {!!}
-- -- ++FinShuffleComm (ℕsuc m) (ℕsuc n) U V (suc i) | yes i+1<m+1 =
-- --   ++FinShuffleComm m (ℕsuc n) (U ∘ suc) V i ∙ {!!}
-- ... | no y = {!!}
