{-# OPTIONS --safe --postfix-projections #-}

module Cubical.Data.Fin.Recursive.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

import Cubical.Data.Empty as Empty
open Empty hiding (rec; elim)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open Sum using (_⊎_; _⊎?_; inl; inr)

open import Cubical.Data.Fin.Recursive.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    m n : ℕ
    A : Type ℓ
    x y : A

isPropFin0 : isProp (Fin 0)
isPropFin0 = isProp⊥

isContrFin1 : isContr (Fin 1)
isContrFin1 .fst = zero
isContrFin1 .snd zero = refl

Unit≡Fin1 : Unit ≡ Fin 1
Unit≡Fin1 = ua (const zero , ctr)
  where
  fibr : fiber (const zero) zero
  fibr = tt , refl

  fibr! : ∀ f → fibr ≡ f
  fibr! (tt , p) i .fst = tt
  fibr! (tt , p) i .snd = J (λ{ zero q → refl ≡ q }) refl p i

  ctr : isEquiv (const zero)
  ctr .equiv-proof zero .fst = fibr
  ctr .equiv-proof zero .snd = fibr!

module Cover where
  Cover : FinF A → FinF A → Type _
  Cover zero zero = Unit
  Cover (suc x) (suc y) = x ≡ y
  Cover _ _ = ⊥

  crefl : Cover x x
  crefl {x = zero} = _
  crefl {x = suc x} = refl

  cover : x ≡ y → Cover x y
  cover p = transport (λ i → Cover (p i0) (p i)) crefl

  predp : Path (FinF A) (suc x) (suc y) → x ≡ y
  predp {x = x} p = transport (λ i → Cover (suc x) (p i)) refl

  suc-predp-refl
    : Path (Path (FinF A) (suc x) (suc x))
        (λ i → suc (predp (λ _ → suc x) i)) refl
  suc-predp-refl {x = x} i j
    = suc (transportRefl (refl {x = x}) i j)

  suc-retract : (p : Path (FinF A) (suc x) (suc y)) → (λ i → suc (predp p i)) ≡ p
  suc-retract
    = J (λ{ (suc m) q → (λ i → suc (predp q i)) ≡ q ; zero _ → ⊥}) suc-predp-refl

  isEmbedding-suc : isEmbedding {B = FinF A} suc
  isEmbedding-suc w x = isoToIsEquiv theIso
    where
    open Iso
    theIso : Iso (w ≡ x) (suc w ≡ suc x)
    theIso .fun = cong suc
    theIso .inv p = predp p
    theIso .rightInv = suc-retract
    theIso .leftInv
      = J (λ _ q → transport (λ i → w ≡ q i) refl ≡ q) (transportRefl refl)

private
  zK : (p : Path (FinF A) zero zero) → p ≡ refl
  zK = J (λ{ zero q → q ≡ refl ; one _ → ⊥ }) refl

  isSetFinF : isSet A → isSet (FinF A)
  isSetFinF Aset zero zero p
    = J (λ{ zero q → p ≡ q ; _ _ → ⊥ }) (zK p)
  isSetFinF Aset (suc x) (suc y)
    = isOfHLevelRetract 1 Cover.predp (cong suc) Cover.suc-retract (Aset x y)
  isSetFinF Aset zero (suc _) p = Empty.rec (Cover.cover p)
  isSetFinF Aset (suc _) zero p = Empty.rec (Cover.cover p)

isSetFin : isSet (Fin m)
isSetFin {zero} = isProp→isSet isPropFin0
isSetFin {suc m} = isSetFinF isSetFin

discreteFin : Discrete (Fin m)
discreteFin {suc m} zero zero = yes refl
discreteFin {suc m} (suc i) (suc j) with discreteFin i j
... | yes p = yes (cong suc p)
... | no ¬p = no (¬p ∘ Cover.predp)
discreteFin {suc m} zero (suc _) = no Cover.cover
discreteFin {suc m} (suc _) zero = no Cover.cover

inject< : m < n → Fin m → Fin n
inject< {suc m} {suc n} _ zero = zero
inject< {suc m} {suc n} m<n (suc i) = suc (inject< m<n i)

inject≤ : m ≤ n → Fin m → Fin n
inject≤ {suc m} {suc n} _ zero = zero
inject≤ {suc m} {suc n} m≤n (suc i) = suc (inject≤ m≤n i)

any? : {P : Fin m → Type ℓ} → (∀ i → Dec (P i)) → Dec (Σ _ P)
any? {zero} P? = no fst
any? {suc m} P? with P? zero ⊎? any? (P? ∘ suc)
... | yes (inl p) = yes (zero , p)
... | yes (inr (i , p)) = yes (suc i , p)
... | no k = no λ where
  (zero , p) → k (inl p)
  (suc x , p) → k (inr (x , p))

_#_ : Fin m → Fin m → Type₀
_#_ {m = suc m} zero zero = ⊥
_#_ {m = suc m} (suc i) zero = Unit
_#_ {m = suc m} zero (suc j) = Unit
_#_ {m = suc m} (suc i) (suc j) = i # j

#→≢ : ∀{i j : Fin m} → i # j → ¬ i ≡ j
#→≢ {suc _} {zero} {suc j} _ = Cover.cover
#→≢ {suc _} {suc i} {zero} _ = Cover.cover
#→≢ {suc m} {suc i} {suc j} ap p = #→≢ ap (Cover.predp p)

≢→# : ∀{i j : Fin m} → ¬ i ≡ j → i # j
≢→# {suc m} {zero}  {zero}  ¬p = ¬p refl
≢→# {suc m} {zero}  {suc j}  _ = _
≢→# {suc m} {suc i} {zero}   _ = _
≢→# {suc m} {suc i} {suc j} ¬p = ≢→# {m} {i} {j} (¬p ∘ cong suc)

#-inject< : ∀{l : m < n} (i j : Fin m) → i # j → inject< {m} {n} l i # inject< l j
#-inject< {suc m} {suc n} zero    (suc _) _ = _
#-inject< {suc m} {suc n} (suc _) zero    _ = _
#-inject< {suc m} {suc n} (suc i) (suc j) a = #-inject< {m} {n} i j a

punchOut : (i j : Fin (suc m)) → i # j → Fin m
punchOut {suc m} zero (suc j) _ = j
punchOut {suc m} (suc i) zero _ = zero
punchOut {suc m} (suc i) (suc j) ap = suc (punchOut i j ap)

punchOut-inj
  : ∀{i j k : Fin (suc m)}
  → (i#j : i # j) (i#k : i # k)
  → punchOut i j i#j ≡ punchOut i k i#k
  → j ≡ k
punchOut-inj {suc m} {suc i} {zero} {zero} i#j i#k p = refl
punchOut-inj {suc m} {zero} {suc j} {suc k} i#j i#k p = cong suc p
punchOut-inj {suc m} {suc i} {suc j} {suc k} i#j i#k p
  = cong suc (punchOut-inj {m} {i} {j} {k} i#j i#k (Cover.predp p))
punchOut-inj {suc m} {suc i} {zero} {suc x} i#j i#k p
  = Empty.rec (Cover.cover p)
punchOut-inj {suc m} {suc i} {suc j} {zero} i#j i#k p
  = Empty.rec (Cover.cover p)

_⊕_ : (m : ℕ) → Fin n → Fin (m + n)
zero  ⊕ i = i
suc m ⊕ i = suc (m ⊕ i)

toFin : (n : ℕ) → Fin (suc n)
toFin zero = zero
toFin (suc n) = suc (toFin n)

toFin< : (m : ℕ) → m < n → Fin n
toFin< {suc n} zero 0<sn = zero
toFin< {suc n} (suc m) m<n = suc (toFin< m m<n)

inject<#toFin : ∀(i : Fin n) → inject< (≤-refl (suc n)) i # toFin n
inject<#toFin {suc n} zero = _
inject<#toFin {suc n} (suc i) = inject<#toFin {n} i

inject≤#⊕ : ∀(i : Fin m) (j : Fin n) → inject≤ (k≤k+n m) i # (m ⊕ j)
inject≤#⊕ {suc m} {suc n} zero    j = _
inject≤#⊕ {suc m} {suc n} (suc i) j = inject≤#⊕ i j

split : (m : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
split zero    j = inr j
split (suc m) zero = inl zero
split (suc m) (suc i) with split m i
... | inl k = inl (suc k)
... | inr j = inr j

pigeonhole
  : m < n
  → (f : Fin n → Fin m)
  → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (i # j) × (f i ≡ f j)
pigeonhole {zero} {suc n} m<n f = Empty.rec (f zero)
pigeonhole {suc m} {suc n} m<n f with any? (λ i → discreteFin (f zero) (f (suc i)))
... | yes (j , p) = zero , suc j , _ , p
... | no ¬p = let i , j , ap , p = pigeonhole {m} {n} m<n g
               in suc i , suc j , ap
                , punchOut-inj {i = f zero} (apart i) (apart j) p
  where
  apart : (i : Fin n) → f zero # f (suc i)
  apart i = ≢→# {suc m} {f zero} (¬p ∘ _,_ i)

  g : Fin n → Fin m
  g i = punchOut (f zero) (f (suc i)) (apart i)

Fin-inj₀ : m < n → ¬ Fin n ≡ Fin m
Fin-inj₀ m<n P with pigeonhole m<n (transport P)
... | i , j , i#j , p = #→≢ i#j i≡j
  where
  i≡j : i ≡ j
  i≡j = transport (λ k → transport⁻Transport P i k ≡ transport⁻Transport P j k)
          (cong (transport⁻ P) p)

Fin-inj : (m n : ℕ) → Fin m ≡ Fin n → m ≡ n
Fin-inj m n P with m ≟ n
... | eq p   = p
... | lt m<n = Empty.rec (Fin-inj₀ m<n (sym P))
... | gt n<m = Empty.rec (Fin-inj₀ n<m P)

module Isos where
  open Iso

  up : Fin m → Fin (m + n)
  up {m} = inject≤ (k≤k+n m)

  resplit-identᵣ₀ : ∀ m (i : Fin n) → Sum.⊎Path.Cover (split m (m ⊕ i)) (inr i)
  resplit-identᵣ₀ zero    i = lift refl
  resplit-identᵣ₀ (suc m) i with split m (m ⊕ i) | resplit-identᵣ₀ m i
  ... | inr j | p = p

  resplit-identᵣ : ∀ m (i : Fin n) → split m (m ⊕ i) ≡ inr i
  resplit-identᵣ m i = Sum.⊎Path.decode _ _ (resplit-identᵣ₀ m i)

  resplit-identₗ₀ : ∀ m (i : Fin m) → Sum.⊎Path.Cover (split {n} m (up i)) (inl i)
  resplit-identₗ₀ (suc m) zero = lift refl
  resplit-identₗ₀ {n} (suc m) (suc i)
    with split {n} m (up i) | resplit-identₗ₀ {n} m i
  ... | inl j | lift p = lift (cong suc p)

  resplit-identₗ : ∀ m (i : Fin m) → split {n} m (up i) ≡ inl i
  resplit-identₗ m i = Sum.⊎Path.decode _ _ (resplit-identₗ₀ m i)

  desplit-ident : ∀ m → (i : Fin (m + n)) → Sum.rec up (m ⊕_) (split m i) ≡ i
  desplit-ident zero i = refl
  desplit-ident (suc m) zero = refl
  desplit-ident (suc m) (suc i) with split m i | desplit-ident m i
  ... | inl j | p = cong suc p
  ... | inr j | p = cong suc p

  sumIso : Iso (Fin m ⊎ Fin n) (Fin (m + n))
  sumIso {m} .fun = Sum.rec up (m ⊕_)
  sumIso {m} .inv i = split m i
  sumIso {m} .rightInv i = desplit-ident m i
  sumIso {m} .leftInv (inr j) = resplit-identᵣ m j
  sumIso {m} .leftInv (inl i) = resplit-identₗ m i

sum≡ : Fin m ⊎ Fin n ≡ Fin (m + n)
sum≡ = isoToPath Isos.sumIso
