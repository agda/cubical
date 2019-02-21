{-# OPTIONS --cubical --safe #-}
module truncations where

open import Cubical.Data.Nat.Base
open import Cubical.Core.Prelude

isOfHLevel : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

isGroupoid : Set → Set
isGroupoid = isOfHLevel 3

isTwoGroupoid : Set → Set
isTwoGroupoid = isOfHLevel 4

data propTrunc (A : Set) : Set where
  pinc : A → propTrunc A
  pIsProp : isProp (propTrunc A)

propTruncElim : (A : Set) (B : (propTrunc A) → Set)
                (bP : (x : propTrunc A) → isProp (B x))
                (f : (x : A) → B (pinc x))
                (x : propTrunc A) → B x
propTruncElim A B bP f = proof
  where
  proof : (x : propTrunc A) → B x
  proof (pinc x) = f x
  proof (pIsProp x y i) = L i
    where
    pA = propTrunc A
    L0 = bP x
    C  = pIsProp x y
    B' : {x y : pA} → (p : x ≡ y) → Set
    B' {x} {y} p = (a : B x) → (b : B y) → PathP (λ i → B (p i)) a b 
    B0 : B' (λ j → C i0) ≡ B' (λ j → C j)
      -- it's B' (λ _ → x) ≡ B' C but we don't write it that way
    B0 i = B' (λ j → C (i ∧ j))
    L1 : B' C
    L1 = transport B0 L0
    L : PathP (λ i → B (pIsProp x y i)) (proof x) (proof y)
    L = L1 (proof x) (proof y)

data setTrunc (A : Set) : Set where
  tinc : A → setTrunc A
  tIsSet : isSet (setTrunc A)

setTruncElim : (A : Set) (B : (setTrunc A) → Set)
               (bS : (x : setTrunc A) → isSet (B x))
               (f : (x : A) → B (tinc x))
               (x : setTrunc A) → B x
setTruncElim A B bS f = proof
  where
  proof : (x : setTrunc A) → B x
  proof (tinc x) = f x
  proof (tIsSet x y p q i j) = L i j
    where
    sA = setTrunc A
    C = tIsSet x y p q
    M1 : {x y : sA} (p : x ≡ y) → B x → B y → Set
    M1 p a b = PathP (λ i → B (p i)) a b
    M2 : {x y : sA} {p q : x ≡ y} (r : p ≡ q) {a : B x} {b : B y}
       → (M1 p a b) → (M1 q a b) → Set
    M2 r {a = a} {b = b} c d = PathP (λ i → M1 (r i) a b) c d
    B' : {x y : sA} {p q : x ≡ y} (r : p ≡ q) → Set
    B' {x} {y} {p} {q} r = (a : B x) (b : B y) (c : M1 p a b) (d : M1 q a b)
                           → M2 r c d
    L0 = bS x -- : B' (λ i j → C i0 i0) 
    B0 B1 : I → Set
    B0 k = B' (λ i j → C i0 (j ∧ k))
    B1 k = B' (λ i j → C (i ∧ k) j)
    L1 = transport (λ i → B0 i) L0
    L2 = transport (λ i → B1 i) L1 -- : B' C
    L = L2 (proof x) (proof y) (λ i → proof (p i)) (λ i → proof (q i))

data groupoidTrunc (A : Set) : Set where
  tinc : A → groupoidTrunc A
  tIsGroupoid : isGroupoid (groupoidTrunc A)

groupoidTruncElim : (A : Set) (B : (groupoidTrunc A) → Set)
                    (bG : (x : groupoidTrunc A) → isGroupoid (B x))
                    (f : (x : A) → B (tinc x)) (x : groupoidTrunc A) → B x
groupoidTruncElim A B bG f = proof
  where
  proof : (x : groupoidTrunc A) → B x
  proof (tinc x) = f x
  proof (tIsGroupoid x y p q r s i j k) = L i j k
    where
    gA = groupoidTrunc A
    C = tIsGroupoid x y p q r s
    M1 : {x y : gA} (p : x ≡ y) → B x → B y → Set
    M1 p a b = PathP (λ i → B (p i)) a b
    M2 : {x y : gA} {p q : x ≡ y} (r : p ≡ q) {a : B x} {b : B y}
       → (M1 p a b) → (M1 q a b) → Set
    M2 r {a = a} {b = b} c d = PathP (λ i → M1 (r i) a b) c d
    M3 : {x y : gA} {p q : x ≡ y} {r s : p ≡ q} (u : r ≡ s)
         {a : B x} {b : B y} {c : M1 p a b} {d : M1 q a b}
         → (M2 r c d) → (M2 s c d) → Set
    M3 u {c = c} {d = d} e f = PathP (λ i → M2 (u i) c d) e f
    B' : {x y : gA} {p q : x ≡ y} {r s : p ≡ q} → (r ≡ s) → Set
    B' {x} {y} {p} {q} {r} {s} u =
      (a : B x) (b : B y) (c : M1 p a b) (d : M1 q a b)
      (e : M2 r c d) (f : M2 s c d) → M3 u e f
    L0 = bG x -- : B' (λ i j k → C i0 i0 i0)
    B0 B1 B2 : I → Set
    B0 i = B' (λ j0 j1 j2 → C i0 i0 (i ∧ j2))
    B1 i = B' (λ j0 j1 j2 → C i0 (i ∧ j1) j2)
    B2 i = B' (λ j0 j1 j2 → C (i ∧ j0) j1 j2)
    L1 = transport (λ i → B0 i) L0
    L2 = transport (λ i → B1 i) L1
    L3 = transport (λ i → B2 i) L2 -- : B' C
    L = L3 (proof x) (proof y)
           (λ i → proof (p i)) (λ i → proof (q i))
           (λ i j → proof (r i j)) (λ i j → proof (s i j))

data g2Trunc (A : Set) : Set where
  g2inc : A → g2Trunc A
  g2IsTwoGroupoid : isTwoGroupoid (g2Trunc A)

g2TruncElim : (A : Set) (B : (g2Trunc A) → Set)
              (bG : (x : g2Trunc A) → isTwoGroupoid (B x))
              (f : (x : A) → B (g2inc x)) (x : g2Trunc A) → B x
g2TruncElim A B bG f = proof
  where
  proof : (x : g2Trunc A) → B x
  proof (g2inc x) = f x
  proof (g2IsTwoGroupoid x y p q r s u v i j k l) = L i j k l
    where
    gA = g2Trunc A
    C = g2IsTwoGroupoid x y p q r s u v
    M1 : {x y : gA} (p : x ≡ y) → B x → B y → Set
    M1 p a b = PathP (λ i → B (p i)) a b
    M2 : {x y : gA} {p q : x ≡ y} (r : p ≡ q) {a : B x} {b : B y}
       → (M1 p a b) → (M1 q a b) → Set
    M2 r {a = a} {b = b} c d = PathP (λ i → M1 (r i) a b) c d
    M3 : {x y : gA} {p q : x ≡ y} {r s : p ≡ q} (u : r ≡ s)
         {a : B x} {b : B y} {c : M1 p a b} {d : M1 q a b}
         → (M2 r c d) → (M2 s c d) → Set
    M3 u {c = c} {d = d} e f = PathP (λ i → M2 (u i) c d) e f
    M4 : {x y : gA} {p q : x ≡ y} {r s : p ≡ q} {u v : r ≡ s} (w : u ≡ v)
         {a : B x} {b : B y} {c : M1 p a b} {d : M1 q a b}
         {e : M2 r c d} {f : M2 s c d}
         → (M3 u e f) → (M3 v e f) → Set
    M4 w {e = e} {f = f} g h = PathP (λ i → M3 (w i) e f) g h
    B' : {x y : gA} {p q : x ≡ y} {r s : p ≡ q} {u v : r ≡ s} → (u ≡ v) → Set
    B' {x} {y} {p} {q} {r} {s} {u} {v} w =
       (a : B x) (b : B y) (c : M1 p a b) (d : M1 q a b)
       (e : M2 r c d) (f : M2 s c d)
       (g : M3 u e f) (h : M3 v e f)
       → M4 w g h
    L0 = bG x -- : B' (λ i j k l → C i0 i0 i0 i0)
    B0 B1 B2 B3 : I → Set
    B0 i = B' (λ j0 j1 j2 j3 → C i0 i0 i0 (i ∧ j3))
    B1 i = B' (λ j0 j1 j2 j3 → C i0 i0 (i ∧ j2) j3)
    B2 i = B' (λ j0 j1 j2 j3 → C i0 (i ∧ j1) j2 j3)
    B3 i = B' (λ j0 j1 j2 j3 → C (i ∧ j0) j1 j2 j3)
    L1 = transport (λ i → B0 i) L0
    L2 = transport (λ i → B1 i) L1
    L3 = transport (λ i → B2 i) L2
    L4 = transport (λ i → B3 i) L3 -- : B' C
    L = L4 (proof x) (proof y)
           (λ i → proof (p i)) (λ i → proof (q i))
           (λ i j → proof (r i j)) (λ i j → proof (s i j))
           (λ i j k → proof (u i j k)) (λ i j k → proof (v i j k))
