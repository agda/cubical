
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Properties where

-- WARNING : fromℕ' is in triple ! => to clean !
-- sort file + mix with Fin folder

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
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe

open import Cubical.Relation.Nullary

open import Cubical.Structures.Pointed

private
 variable
   ℓ ℓ' : Level
   A : Type ℓ
   m n k : ℕ

toℕ<n : ∀ {n} (i : Fin n) → toℕ i < n
toℕ<n {n = ℕsuc n} zero = n , +-comm n 1
toℕ<n {n = ℕsuc n} (suc i) = toℕ<n i .fst , +-suc _ _ ∙ cong ℕsuc (toℕ<n i .snd)

znots : ∀{k} {m : Fin k} → ¬ (zero ≡ (suc m))
znots {k} {m} x = subst (Fin.rec (Fin k) ⊥) x m

znotsP : ∀ {k0 k1 : ℕ} {k : k0 ≡ k1} {m1 : Fin k1}
  → ¬ PathP (λ i → Fin (ℕsuc (k i))) zero (suc m1)
znotsP p = ℕznots (congP (λ i → toℕ) p)

snotz : ∀{k} {m : Fin k} → ¬ ((suc m) ≡ zero)
snotz {k} {m} x = subst (Fin.rec ⊥ (Fin k)) x m

snotzP : ∀ {k0 k1 : ℕ} {k : k0 ≡ k1} {m0 : Fin k0}
  → ¬ PathP (λ i → Fin (ℕsuc (k i))) (suc m0) zero
snotzP p = ℕsnotz (congP (λ i → toℕ) p)

-- alternative from
fromℕ' : (n : ℕ) → (k : ℕ) → (k < n) → Fin n
fromℕ' ℕzero k infkn = ⊥.rec (¬-<-zero infkn)
fromℕ' (ℕsuc n) ℕzero infkn = zero
fromℕ' (ℕsuc n) (ℕsuc k) infkn = suc (fromℕ' n k (pred-≤-pred infkn))

toFromId' : (n : ℕ) → (k : ℕ) → (infkn : k < n) → toℕ (fromℕ' n k infkn) ≡ k
toFromId' ℕzero k infkn = ⊥.rec (¬-<-zero infkn)
toFromId' (ℕsuc n) ℕzero infkn = refl
toFromId' (ℕsuc n) (ℕsuc k) infkn = cong ℕsuc (toFromId' n k (pred-≤-pred infkn))

fromToId' : (n : ℕ) → (k : Fin n ) → (r : toℕ k < n) → fromℕ' n (toℕ k) r ≡ k
fromToId' (ℕsuc n) zero r = refl
fromToId' (ℕsuc n) (suc k) r = cong suc (fromToId' n k (pred-≤-pred r))

inj-toℕ : {n : ℕ} → {k l : Fin n} → (toℕ k ≡ toℕ l) → k ≡ l
inj-toℕ {ℕsuc n}  {zero} {zero}   x = refl
inj-toℕ {ℕsuc n}  {zero} {suc l} x = ⊥.rec (ℕznots x)
inj-toℕ {ℕsuc n} {suc k} {zero}   x = ⊥.rec (ℕsnotz x)
inj-toℕ {ℕsuc n} {suc k} {suc l}  x = cong suc (inj-toℕ (injSuc x))

inj-cong : {n : ℕ} → {k l : Fin n} → (p : toℕ k ≡ toℕ l) → cong toℕ (inj-toℕ p) ≡ p
inj-cong p = isSetℕ _ _ _ _

isPropFin0 : isProp (Fin 0)
isPropFin0 = ⊥.rec ∘ ¬Fin0

isContrFin1 : isContr (Fin 1)
isContrFin1 .fst = zero
isContrFin1 .snd zero = refl

injSucFin : ∀ {n} {p q : Fin n} → suc p ≡ suc q → p ≡ q
injSucFin {ℕsuc ℕzero} {zero} {zero} pf = refl
injSucFin {ℕsuc (ℕsuc n)} pf = cong predFin pf

injSucFinP : ∀ {n0 n1 : ℕ} {pn : n0 ≡ n1} {p0 : Fin n0} {p1 : Fin n1}
  → PathP (λ i → Fin (ℕsuc (pn i))) (suc p0) (suc p1)
  → PathP (λ i → Fin (pn i)) p0 p1
injSucFinP {one} {one} {pn} {zero} {zero} sucp =
  transport (λ j → PathP (λ i → Fin (eqn j i)) zero zero) refl
  where eqn : refl ≡ pn
        eqn = isSetℕ one one refl pn
injSucFinP {one} {ℕsuc (ℕsuc n1)} {pn} {p0} {p1} sucp = ⊥.rec (ℕznots (injSuc pn))
injSucFinP {ℕsuc (ℕsuc n0)} {one} {pn} {p0} {p1} sucp = ⊥.rec (ℕsnotz (injSuc pn))
injSucFinP {ℕsuc (ℕsuc n0)} {ℕsuc (ℕsuc n1)} {pn} {p0} {p1} sucp =
  transport (λ j → PathP (λ i → Fin (eqn j i)) p0 p1) (
      congP (λ i → predFin) (
        transport (λ j → PathP (λ i → Fin (ℕsuc (eqn (~ j) i))) (suc p0) (suc p1)) sucp
      )
    )
  where pn' : 2 + n0 ≡ 2 + n1
        pn' = cong ℕsuc (injSuc pn)
        eqn : pn' ≡ pn
        eqn = isSetℕ (2 + n0) (2 + n1) pn' pn

discreteFin : ∀{k} → Discrete (Fin k)
discreteFin zero zero = yes refl
discreteFin zero (suc y) = no znots
discreteFin (suc x) zero = no snotz
discreteFin (suc x) (suc y) with discreteFin x y
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (injSucFin q))

isSetFin : ∀{k} → isSet (Fin k)
isSetFin = Discrete→isSet discreteFin

isWeaken? : ∀ {n} (p : Fin (ℕsuc n)) → Dec (Σ[ q ∈ Fin n ] p ≡ weakenFin q)
isWeaken? {ℕzero} zero = no λ (q , eqn) → case q of λ ()
isWeaken? {ℕsuc n} zero = yes (zero , refl)
isWeaken? {ℕsuc n} (suc p) with isWeaken? {n} p
... | yes (q , p≡wq) = yes (suc q , cong suc p≡wq)
... | no  p≢wq = no λ
  { (zero , sp≡wq) → snotz sp≡wq
  ; (suc q , sp≡wq) → p≢wq (q , cong predFin sp≡wq)
  }

data biEq {n : ℕ} (i j : Fin n) : Type where
  eq  :   i ≡ j → biEq i j
  ¬eq : ¬ i ≡ j → biEq i j

data triEq {n : ℕ} (i j a : Fin n) : Type where
  leq : a ≡ i → triEq i j a
  req : a ≡ j → triEq i j a
  ¬eq : (¬ a ≡ i) × (¬ a ≡ j) → triEq i j a

biEq? : (i j : Fin n) → biEq i j
biEq? i j = case (discreteFin i j) return (λ _ → biEq i j)
              of λ { (yes p) → eq p ; (no ¬p) → ¬eq ¬p }

triEq? : (i j a : Fin n) → triEq i j a
triEq? i j a =
  case (discreteFin a i) return (λ _ → triEq i j a) of
    λ { (yes p) → leq p
      ; (no ¬p) →
          case (discreteFin a j) return (λ _ → triEq i j a) of
            λ { (yes q) → req q
              ; (no ¬q) → ¬eq (¬p , ¬q) }}


weakenRespToℕ : ∀ {n} (i : Fin n) → toℕ (weakenFin i) ≡ toℕ i
weakenRespToℕ zero = refl
weakenRespToℕ (suc i) = cong ℕsuc (weakenRespToℕ i)

toFin : {n : ℕ} (m : ℕ) → m < n → Fin n
toFin {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
toFin {n = ℕsuc n} _ (ℕzero , _) = fromℕ n --in this case we have m≡n
toFin {n = ℕsuc n} m (ℕsuc k , p) = weakenFin (toFin m (k , cong predℕ p))

toFin0≡0 : {n : ℕ} (p : 0 < ℕsuc n) → toFin 0 p ≡ zero
toFin0≡0 (ℕzero , p) = subst (λ x → fromℕ x ≡ zero) (cong predℕ p) refl
toFin0≡0 {ℕzero} (ℕsuc k , p) = ⊥.rec (ℕsnotz (+-comm 1 k ∙ (cong predℕ p)))
toFin0≡0 {ℕsuc n} (ℕsuc k , p) =
         subst (λ x → weakenFin x ≡ zero) (sym (toFin0≡0 (k , cong predℕ p))) refl

genδ-FinVec : (n k : ℕ) → (a b : A) → FinVec A n
genδ-FinVec (ℕsuc n) ℕzero a b zero = a
genδ-FinVec (ℕsuc n) ℕzero a b (suc x) = b
genδ-FinVec (ℕsuc n) (ℕsuc k) a b zero = b
genδ-FinVec (ℕsuc n) (ℕsuc k) a b (suc x) = genδ-FinVec n k a b x

δℕ-FinVec : (n k : ℕ) → FinVec ℕ n
δℕ-FinVec n k = genδ-FinVec n k 1 0

-- WARNING : harder to prove things about
genδ-FinVec' : (n k : ℕ) → (a b : A) → FinVec A n
genδ-FinVec' n k a b x with discreteℕ (toℕ x) k
... | yes p = a
... | no ¬p = b

-- doing induction on toFin is awkward, so the following alternative
enum : (m : ℕ) → m < n → Fin n
enum {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
enum {n = ℕsuc n} 0 _ = zero
enum {n = ℕsuc n} (ℕsuc m) p = suc (enum m (pred-≤-pred p))

enum∘toℕ : (i : Fin n)(p : toℕ i < n) → enum (toℕ i) p ≡ i
enum∘toℕ {n = ℕsuc n} zero _ = refl
enum∘toℕ {n = ℕsuc n} (suc i) p t = suc (enum∘toℕ i (pred-≤-pred p) t)

toℕ∘enum : (m : ℕ)(p : m < n) → toℕ (enum m p) ≡ m
toℕ∘enum {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
toℕ∘enum {n = ℕsuc n} 0 _ = refl
toℕ∘enum {n = ℕsuc n} (ℕsuc m) p i = ℕsuc (toℕ∘enum m (pred-≤-pred p) i)

enumExt : {m m' : ℕ}(p : m < n)(p' : m' < n) → m ≡ m' → enum m p ≡ enum m' p'
enumExt p p' q i = enum (q i) (isProp→PathP (λ i → isProp≤ {m = ℕsuc (q i)}) p p' i)

enumInj : (p : m < k) (q : n < k) → enum m p ≡ enum n q → m ≡ n
enumInj p q path = sym (toℕ∘enum _ p) ∙ cong toℕ path ∙ toℕ∘enum _ q

enumIndStep :
    (P : Fin n → Type ℓ)
  → (k : ℕ)(p : ℕsuc k < n)
  → ((m : ℕ)(q : m < n)(q' : m ≤ k )     → P (enum m q))
  → P (enum (ℕsuc k) p)
  → ((m : ℕ)(q : m < n)(q' : m ≤ ℕsuc k) → P (enum m q))
enumIndStep P k p f x m q q' =
  case (≤-split q') return (λ _ → P (enum m q)) of
    λ { (inl r') → f m q (pred-≤-pred r')
      ; (inr r') → subst P (enumExt p q (sym r')) x }

enumElim :
    (P : Fin n → Type ℓ)
  → (k : ℕ)(p : k < n)(h : ℕsuc k ≡ n)
  → ((m : ℕ)(q : m < n)(q' : m ≤ k) → P (enum m q))
  → (i : Fin n) → P i
enumElim P k p h f i =
  subst P (enum∘toℕ i (toℕ<n i)) (f (toℕ i) (toℕ<n i)
    (pred-≤-pred (subst (λ a → toℕ i < a) (sym h) (toℕ<n i))))


++FinAssoc : {n m k : ℕ} (U : FinVec A n) (V : FinVec A m) (W : FinVec A k)
           → PathP (λ i → FinVec A (+-assoc n m k i)) (U ++Fin (V ++Fin W)) ((U ++Fin V) ++Fin W)
++FinAssoc {n = ℕzero} _ _ _ = refl
++FinAssoc {n = ℕsuc n} U V W i zero = U zero
++FinAssoc {n = ℕsuc n} U V W i (suc ind) = ++FinAssoc (U ∘ suc) V W i ind

++FinRid : {n : ℕ} (U : FinVec A n) (V : FinVec A 0)
         → PathP (λ i → FinVec A (+-zero n i)) (U ++Fin V) U
++FinRid {n = ℕzero} U V = funExt λ i → ⊥.rec (¬Fin0 i)
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


finSucMaybeIso : Iso (Fin (ℕ.suc n)) (Maybe (Fin n))
Iso.fun finSucMaybeIso zero = nothing
Iso.fun finSucMaybeIso (suc i) = just i
Iso.inv finSucMaybeIso nothing = zero
Iso.inv finSucMaybeIso (just i) = suc i
Iso.rightInv finSucMaybeIso nothing = refl
Iso.rightInv finSucMaybeIso (just i) = refl
Iso.leftInv finSucMaybeIso zero = refl
Iso.leftInv finSucMaybeIso (suc i) = refl

finSuc≡Maybe : Fin (ℕ.suc n) ≡ Maybe (Fin n)
finSuc≡Maybe = isoToPath finSucMaybeIso

finSuc≡Maybe∙ : (Fin (ℕ.suc n) , zero) ≡ Maybe∙ (Fin n)
finSuc≡Maybe∙ = pointed-sip _ _ ((isoToEquiv finSucMaybeIso) , refl)

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

-- Exhaustion of decidable predicate

∀Dec :
    (P : Fin m → Type ℓ)
  → (dec : (i : Fin m) → Dec (P i))
  → ((i : Fin m) → P i) ⊎ (Σ[ i ∈ Fin m ] ¬ P i)
∀Dec {m = 0} _ _ = inl λ ()
∀Dec {m = ℕsuc m} P dec = helper (dec zero) (∀Dec _ (dec ∘ suc))
  where
    helper :
        Dec (P zero)
      → ((i : Fin m) → P (suc i))  ⊎ (Σ[ i ∈ Fin m ] ¬ P (suc i))
      → ((i : Fin (ℕsuc m)) → P i) ⊎ (Σ[ i ∈ Fin (ℕsuc m) ] ¬ P i)
    helper (yes p) (inl q) = inl λ { zero → p ; (suc i) → q i }
    helper (yes _) (inr q) = inr (suc (q .fst) , q .snd)
    helper (no ¬p) _ = inr (zero , ¬p)

∀Dec2 :
    (P : Fin m → Fin n → Type ℓ)
  → (dec : (i : Fin m)(j : Fin n) → Dec (P i j))
  → ((i : Fin m)(j : Fin n) → P i j) ⊎ (Σ[ i ∈ Fin m ] Σ[ j ∈ Fin n ] ¬ P i j)
∀Dec2 {m = 0} {n = n} _ _ = inl λ ()
∀Dec2 {m = ℕsuc m} {n = n} P dec = helper (∀Dec (P zero) (dec zero)) (∀Dec2 (P ∘ suc) (dec ∘ suc))
  where
    helper :
        ((j : Fin n) → P zero j) ⊎ (Σ[ j ∈ Fin n ] ¬ P zero j)
      → ((i : Fin m)(j : Fin n) → P (suc i) j)  ⊎ (Σ[ i ∈ Fin m ] Σ[ j ∈ Fin n ] ¬ P (suc i) j)
      → ((i : Fin (ℕsuc m))(j : Fin n) → P i j) ⊎ (Σ[ i ∈ Fin (ℕsuc m) ] Σ[ j ∈ Fin n ] ¬ P i j)
    helper (inl p) (inl q) = inl λ { zero j → p j ; (suc i) j → q i j }
    helper (inl _) (inr q) = inr (suc (q .fst) , q .snd .fst , q .snd .snd)
    helper (inr p) _ = inr (zero , p)
