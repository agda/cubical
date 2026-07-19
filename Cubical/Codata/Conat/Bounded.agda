{-# OPTIONS --cubical --no-import-sorts --guardedness #-}
module Cubical.Codata.Conat.Bounded where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Codata.Conat.Base
  renaming (zero to czero; suc to csuc)
open import Cubical.Codata.Conat.Properties

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat as Nat
import Cubical.Data.Fin.Recursive as Fin

private variable ℓ : Level

_≺_ : ℕ → Conat → Type _
_≺′_ : ℕ → Conat′ → Type _

n ≺ c = n ≺′ force c
_ ≺′ czero = ⊥
zero  ≺′ csuc _ = Unit
suc n ≺′ csuc c = n ≺ c

isProp≺ : ∀ n c → isProp (n ≺ c)
isProp≺′ : ∀ n c → isProp (n ≺′ c)
isProp≺ n c = isProp≺′ n (force c)
isProp≺′ n           czero = isProp⊥
isProp≺′ zero    (csuc  _) = isPropUnit
isProp≺′ (suc n) (csuc c') = isProp≺ n c'

isPropDep≺ : ∀ c → isPropDep (_≺ c)
isPropDep≺ c = isOfHLevel→isOfHLevelDep 1 (λ n → isProp≺ n c) {_} {_}

isPropDep≺′ : ∀ c → isPropDep (_≺′ c)
isPropDep≺′ c = isOfHLevel→isOfHLevelDep 1 (λ n → isProp≺′ n c) {_} {_}

private
  apart : ℕ → ℕ → Type
  apart zero zero = ⊥
  apart (suc m) (suc n) = apart m n
  apart _ _ = Unit

  ≢→apart : (i j : ℕ) → ¬ i ≡ j → apart i j
  ≢→apart zero zero ¬p = ¬p refl
  ≢→apart (suc i) (suc j) ¬p = ≢→apart i j (¬p ∘ cong suc)
  ≢→apart zero (suc j) _ = _
  ≢→apart (suc i) zero _ = _

  apart→≢ : (i j : ℕ) → apart i j → ¬ i ≡ j
  apart→≢ (suc i) zero _ = snotz
  apart→≢ zero (suc j) _ = znots
  apart→≢ (suc i) (suc j) i#j = apart→≢ i j i#j ∘ cong predℕ

  isPropApart : ∀ m n → isProp (apart m n)
  isPropApart 0 0 = isProp⊥
  isPropApart (suc m) (suc n) = isPropApart m n
  isPropApart (suc _) 0 = isPropUnit
  isPropApart 0 (suc _) = isPropUnit

_#_ : ∀{P : ℕ → Type ℓ} → (l r : Σ ℕ P) → Type
(m , _) # (n , _) = apart m n

#→≢ : ∀{P : ℕ → Type ℓ} → (l r : Σ ℕ P) → l # r → ¬ l ≡ r
#→≢ (i , _) (j , _) d = apart→≢ i j d ∘ cong fst

isProp# : ∀{P : ℕ → Type ℓ} (l r : Σ ℕ P) → isProp (l # r)
isProp# (m , _) (n , _) = isPropApart m n

isProp#Depᵣ : ∀{P : ℕ → Type ℓ} (r : Σ ℕ P) → isPropDep (_# r)
isProp#Depᵣ r = isOfHLevel→isOfHLevelDep 1 (λ l → isProp# l r) {_} {_}

Bounded : Conat → Type
Bounded m = Σ[ n ∈ ℕ ] n ≺ m

Bounded′ : Conat′ → Type
Bounded′ m = Σ[ n ∈ ℕ ] n ≺′ m

discreteB′ : ∀ m → (i j : Bounded′ m) → (i ≡ j) ⊎ (i # j)
discreteB′ m (i , i≺m) (j , j≺m) with discreteℕ i j
... | yes p = inl λ i → p i , isPropDep≺′ m i≺m j≺m p i
... | no ¬p = inr (≢→apart i j ¬p)

≺∞ : ∀ n → n ≺ ∞
≺∞ zero = _
≺∞ (suc n) = ≺∞ n

Σ≺∞≃ℕ : Bounded ∞ ≃ ℕ
Σ≺∞≃ℕ = isoToEquiv λ where
    .fun → fst
    .inv n → n , ≺∞ n
    .rightInv _ → refl
    .leftInv (n , p) i → λ where
      .fst → n
      .snd → isProp≺ n ∞ (≺∞ n) p i
  where open Iso

Σ≺∞≡ℕ : Bounded ∞ ≡ ℕ
Σ≺∞≡ℕ = ua Σ≺∞≃ℕ

_≺?_ : ∀ n c → Dec (n ≺ c)
n ≺? c with force c
_     ≺? c |  czero = no (idfun ⊥)
zero  ≺? c | csuc d = yes _
suc n ≺? c | csuc d = n ≺? d

≺-pred : ∀ n c → suc n ≺ c → n ≺ c
≺-pred n c sn≺c with force c
≺-pred    zero c sn≺c | csuc d = _
≺-pred (suc n) c sn≺c | csuc d = ≺-pred n d sn≺c

≺?-yes : ∀ n c → (p : n ≺ c) → n ≺? c ≡ yes p
≺?-yes n c p with force c
≺?-yes   zero  c p | csuc c' = refl
≺?-yes (suc n) c p | csuc c' = ≺?-yes n c' p

∀≺-same : ∀ m n → (∀ k → (k ≺ m) ≡ (k ≺ n)) → m ≡ n
∀≺-same m n ∀≺ i .force with force m | force n
... |  czero |  czero = czero
... | csuc o | csuc p = csuc (∀≺-same o p (∀≺ ∘ suc) i)
... | csuc o |  czero
  = Empty.rec {A = csuc o ≡ czero} (transport (∀≺ 0) _) i
... |  czero | csuc p
  = Empty.rec {A = czero ≡ csuc p} (transport⁻ (∀≺ 0) _) i

Bounded→Fin : ∀ m → Bounded (embed m) → Fin.Fin m
Bounded→Fin (suc m) (0 , 0≺m) = Fin.zero
Bounded→Fin (suc m) (suc n , n≺m) = Fin.suc (Bounded→Fin m (n , n≺m))

module Untangle
    {m n}
    (f : Bounded′ (csuc m) → Bounded′ (csuc n))
    (g : Bounded′ (csuc n) → Bounded′ (csuc m))
    (rinv : section f g)
    (linv : retract f g)
  where
  bzro : ∀{k} → Bounded′ (csuc k)
  bzro = (zero , _)

  bsuc : ∀{k} → Bounded k → Bounded′ (csuc k)
  bsuc (l , l≺k) = (suc l , l≺k)

  #-f : ∀ v u → v # u → f v # f u
  #-f v u v#u with discreteB′ (csuc n) (f v) (f u)
  ... | inr fv#fu = fv#fu
  ... | inl fv≡fu
    = rec (#→≢ v u v#u (sym (linv v) ∙∙ cong g (fv≡fu) ∙∙ linv u))

  #-g : ∀ v u → v # u → g v # g u
  #-g v u v#u with discreteB′ (csuc m) (g v) (g u)
  ... | inr gv#gu = gv#gu
  ... | inl gv≡gu
    = rec (#→≢ v u v#u (sym (rinv v) ∙∙ cong f (gv≡gu) ∙∙ rinv u))

  #-fg : ∀ v u → v # u → f (g v) # f (g u)
  #-fg v u = #-f (g v) (g u) ∘ #-g v u

  #-gf : ∀ v u → v # u → g (f v) # g (f u)
  #-gf v u = #-g (f v) (f u) ∘ #-f v u

  default : ∀{k} → (v d : Bounded′ (csuc k)) → v # d → Bounded k
  default (suc l , l≺n) d _ = (l , l≺n)
  default (0 , _) (suc l , l≺n) _ = (l , l≺n)

  f- : Bounded m → Bounded n
  f- v = default (f (bsuc v)) (f bzro) (#-f (bsuc v) bzro _)

  g- : Bounded n → Bounded m
  g- v = default (g (bsuc v)) (g bzro) (#-g (bsuc v) bzro _)

  g-f-z : ∀ v u → g bzro ≡ bsuc v → g (bsuc u) ≡ bzro → g- u ≡ v
  g-f-z (l , l≺m) u p q with g (bsuc u) | g bzro | #-g (bsuc u) bzro _
  ... | zero , _ | suc k , k≺m | #gf = λ where
    i .fst → predℕ (p i .fst)
    i .snd → isPropDep≺ m k≺m l≺m (cong (predℕ ∘ fst) p) i
  ... | w@(suc k , k≺m) | dg | #gf = rec (snotz (cong fst q))

  g-f-s : ∀ v u → g (bsuc u) ≡ bsuc v → g- u ≡ v
  g-f-s (l , l≺m) u p with g (bsuc u) | #-g (bsuc u) bzro _
  ... | suc k , k≺m | #gf = λ where
    i .fst → predℕ (p i .fst)
    i .snd → isPropDep≺ m k≺m l≺m (cong (predℕ ∘ fst) p) i
  ... |  zero , k≺m | #gf = rec (znots (cong fst p))

  g-f- : ∀ v → g- (f- v) ≡ v
  g-f- v@(i , i≺m)
    with f (bsuc v) | linv (bsuc v) | #-f (bsuc v) bzro _
  ... | suc j , j≺m | p | #f = g-f-s v (j , j≺m) p
  ... | zero , _ | p | #f with f bzro | linv bzro
  ... | suc k , k≺n | q = g-f-z v (k , k≺n) p q

  f-g-z : ∀ v u → f bzro ≡ bsuc v → f (bsuc u) ≡ bzro → f- u ≡ v
  f-g-z (l , l≺n) u p q with f (bsuc u) | f bzro | #-f (bsuc u) bzro _
  ... | zero , _ | suc k , k≺n | #fg = λ where
    i .fst → predℕ (p i .fst)
    i .snd → isPropDep≺ n k≺n l≺n (cong (predℕ ∘ fst) p) i
  ... | w@(suc k , k≺m) | df | #fg = rec (snotz (cong fst q))

  f-g-s : ∀ v u → f (bsuc u) ≡ bsuc v → f- u ≡ v
  f-g-s (l , l≺n) u p with f (bsuc u) | #-f (bsuc u) bzro _
  ... | suc k , k≺n | _ = λ where
    i .fst → predℕ (p i .fst)
    i .snd → isPropDep≺ n k≺n l≺n (cong (predℕ ∘ fst) p) i
  ... |  zero , k≺m | _ = rec (znots (cong fst p))

  f-g- : ∀ v → f- (g- v) ≡ v
  f-g- v@(i , i≺n)
    with g (bsuc v) | rinv (bsuc v) | #-g (bsuc v) bzro _
  ... | suc j , j≺m | p | #g = f-g-s v (j , j≺m) p
  ... | zero , _ | p | #g with g bzro | rinv bzro
  ... | suc k , k≺m | q = f-g-z v (k , k≺m) p q

  open Iso
  iso- : Iso (Bounded m) (Bounded n)
  iso- .fun = f-
  iso- .inv = g-
  iso- .rightInv = f-g-
  iso- .leftInv = g-f-

untangled
  : ∀{m n}
  → Iso (Bounded′ (csuc m)) (Bounded′ (csuc n))
  → Iso (Bounded m) (Bounded n)
untangled isom = Untangle.iso- fun inv rightInv leftInv
  where open Iso isom

Bounded-inj-iso : ∀ m n → Iso (Bounded m) (Bounded n) → m ≡ n
Bounded-inj-iso m n theIso i .force with force m | force n
... | czero | czero = czero
... | csuc l | csuc r
  = csuc (Bounded-inj-iso l r (untangled theIso) i)
... | czero | csuc r
  = rec {A = czero ≡ csuc r} (Iso.inv theIso (zero , _) .snd) i
... | csuc l | czero
  = rec {A = csuc l ≡ czero} (Iso.fun theIso (zero , _) .snd) i

Bounded-inj : ∀ m n → Bounded m ≡ Bounded n → m ≡ n
Bounded-inj m n = Bounded-inj-iso m n ∘ pathToIso
