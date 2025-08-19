{-# OPTIONS --cubical #-}
{-# OPTIONS --safe #-}

module Cubical.Algebra.Determinat.RingSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Vec.Base using (_∷_; [])
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.FinData
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Data.Nat.Order
open import Cubical.Tactics.CommRingSolver

module RingSum (ℓ : Level) (P' : CommRing ℓ) where

  R' = CommRing→Ring P'

  open RingStr (snd (CommRing→Ring P')) renaming ( is-set to isSetR)

  ∑ = Sum.∑ (CommRing→Ring P')

  R : Type ℓ
  R = ⟨ P' ⟩

  open  MonoidBigOp  (Ring→AddMonoid R')



  -- Compatability theorems
  ∑Compat : {n : ℕ} → (U V : FinVec R n) →
            ((i : Fin n) →  U i ≡ V i) → ∑ U ≡ ∑ V
  ∑Compat U V f = bigOpExt f

  ∑∑Compat : {n m : ℕ} → (U V : FinVec (FinVec R m) n) →
             ((i : Fin n) → (j : Fin m) →  U i j ≡ V i j) →
             ∑ (λ i → ∑ (λ j → U i j)) ≡ ∑ (λ i →  ∑ (λ j → V i j))
  ∑∑Compat U V Eq =
   ∑ (λ i → ∑ (U i))
   ≡⟨
     ∑Compat
       (λ i → ∑ (U i))
       (λ i → ∑ (V i))
       (λ i → ∑Compat (U i) (V i) (Eq i))
    ⟩
   ∑ (λ i → ∑ (V i))
   ∎

  -- Spliting a sum in the sum:
  ∑Split = Sum.∑Split R'

  ∑∑Split : {n m : ℕ} → (U V : Fin n → Fin m → R) →
    ∑ (λ i → ∑ (λ j → U i j + V i j))
    ≡
    ∑ (λ i → ∑ (λ j → U i j)) +
    ∑ (λ i → ∑ (λ j → V i j))
  ∑∑Split U V =
    ∑ (λ i → ∑ (λ j → U i j + V i j))
    ≡⟨
      ∑Compat
       (λ i → ∑ (λ j → U i j + V i j))
       (λ i → ∑ (λ j → U i j) + ∑ ( λ j →  V i j))
       (λ i → ∑Split (λ j → U i j) ( λ j →  V i j))
     ⟩
    ∑ (λ i → ∑ (λ j → U i j) + ∑ (λ j → V i j))
    ≡⟨ ∑Split (λ i → ∑ (λ j → U i j)) (λ i → ∑ (λ j → V i j)) ⟩
    (∑ (λ i → ∑ (U i)) + ∑ (λ i → ∑ (V i)))
    ∎

  -- Distributivity of the sum
  ∑DistR = Sum.∑Mulrdist (CommRing→Ring P')

  ∑DistL = Sum.∑Mulldist (CommRing→Ring P')

  -- Sum of Zeros is Zero
  ∑Zero : {n : ℕ} → (U : FinVec R n) → ((i : Fin n) → U i ≡ 0r) → ∑ U ≡ 0r
  ∑Zero {zero} U f = refl
  ∑Zero {suc n} U f =
    ∑ U
    ≡⟨ refl ⟩
    (U zero + ∑ (λ i → U (suc i)) )
    ≡⟨ cong (λ a → a +  ∑ (λ i → U (suc i))) (f zero) ⟩
    (0r + ∑ (λ i → U (suc i)))
    ≡⟨ +Comm 0r (∑ (λ i → U (suc i))) ⟩
    ∑ (λ i → U (suc i)) + 0r
    ≡⟨ +IdR (∑ (λ i → U (suc i))) ⟩
    ∑ (λ i → U (suc i))
    ≡⟨ ∑Zero {n} ((λ i → U (suc i))) (λ i → f (suc i))  ⟩
    0r ∎

  -- Summs are commutative
  ∑Comm : {n m : ℕ} → (U : FinVec (FinVec R m) n) →
    ∑ (λ i → ∑ (λ j → U i j )) ≡ ∑ (λ j → ∑ (λ i → U i j))
  ∑Comm {zero} {zero} U = refl
  ∑Comm {zero} {m} U =
    0r
    ≡⟨ sym (∑Zero (λ (j : Fin m) → 0r) (λ (j : Fin m) → refl)) ⟩
    ∑ (λ (j : Fin m) → 0r)
    ≡⟨ ∑Compat (λ j → 0r) (λ j → ∑ (λ i → U i j )) (λ j → refl)  ⟩
    ( (∑ λ j → ∑ (λ i → U i j )))
    ∎
  ∑Comm {n} {zero} U =
    ∑ (λ (i : Fin n) → 0r)
    ≡⟨ ∑Zero ( (λ (i : Fin n) → 0r)) ( (λ i → refl)) ⟩
    0r
    ∎
  ∑Comm {suc n} {suc m} U =
    ∑ (λ i → ∑ (U i))
    ≡⟨ refl ⟩
    ( ∑ (λ i → (U i zero  + ∑ λ j → (U i (suc j)))) )
    ≡⟨ bigOpSplit +Comm (λ i → U i zero) (λ i → ∑ λ j → (U i (suc j))) ⟩
    (∑ (λ i → (U i zero)) + ∑ λ i → (∑ λ j → (U i (suc j))))
    ≡⟨ cong (λ a → ∑ (λ i → (U i zero)) + a) (∑Comm λ i → ( λ j → (U i (suc j) ))) ⟩
    (∑ (λ i → U i zero) + ∑ (λ j → ∑ (λ i → U i (suc j))))
    ≡⟨ refl ⟩
    ∑ (λ j → ∑ (λ i → U i j))
    ∎

  -- Indikator function:  ind> i j = 1r if i>j and ind> i j = 0r else
  ind> : (i j : ℕ) → R
  ind> zero j = 0r
  ind> (suc i) zero = 1r
  ind> (suc i) (suc j) = ind> i j

  ind>prop : {n m : ℕ} → (A B : FinVec (FinVec R m) n) →
             ((i : Fin n) → (j : Fin m) → (toℕ j) <' (toℕ i) → A i j ≡ B i j) →
             (i : Fin n) → (j : Fin m) →
             (ind> (toℕ i) (toℕ j) · A i j) ≡ (ind> (toℕ i) (toℕ j) · B i j)
  ind>prop {m = suc m} A B f zero j = solve! P'
  ind>prop {m = suc m} A B f (suc i) zero =
    cong
      (λ a → 1r · a)
      (f (suc i) zero (s≤s z≤))
  ind>prop {m = suc m} A B f (suc i) (suc j) =
    ind>prop
      (λ i j → A (suc i) (suc j))
      (λ i j → B (suc i) (suc j))
      (λ i₁ j₁ le → f (suc i₁) (suc j₁)
      (s≤s le))
      i
      j

  ind>anti :  {n m : ℕ} → (A B : FinVec (FinVec R m) n) →
              ((i : Fin n) (j : Fin m) → (toℕ i) ≤' (toℕ j) → A i j ≡ B i j) →
              (i : Fin n) → (j : Fin m) →
              (1r + (- ind> (toℕ i) (toℕ j))) · A i j ≡ (1r + - (ind> (toℕ i) (toℕ j))) · B i j
  ind>anti {m = suc m} A B f zero j =
    cong
    (λ a → (1r + - 0r) · a)
    (f zero j z≤)
  ind>anti {m = suc m} A B f (suc i) zero = solve! P'
  ind>anti {m = suc m} A B f (suc i) (suc j) =
    ind>anti
      (λ i j → A (suc i) (suc j))
      (λ i j → B (suc i) (suc j))
      (λ i₁ j₁ le → f (suc i₁) (suc j₁) (s≤s le)) i j

  ind>Neg : (i j : ℕ) → (1r + - ind> (suc i) j) ≡ ind> j i
  ind>Neg i zero = +InvR 1r
  ind>Neg zero (suc j) = solve! P'
  ind>Neg (suc i) (suc j) = ind>Neg i j

  ind>Suc : (i j : ℕ) → ind> (suc i) j ≡ (1r + - ind> j i)
  ind>Suc i zero = solve! P'
  ind>Suc zero (suc j) = solve! P'
  ind>Suc (suc i) (suc j) = ind>Suc i j

  --Index Shift--
  ∑∑ShiftSuc : {n : ℕ} → (A : Fin (suc n) → Fin n → R) →
    ∑ (λ (i : Fin (suc n))  → ∑ ( λ j → ind> (toℕ i) (toℕ j)       · A i j))
    ≡
    ∑ (λ (i : Fin n)        → ∑ ( λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j))
  ∑∑ShiftSuc {zero} A = ∑Zero {one} (λ j → 0r) (λ j → refl)
  ∑∑ShiftSuc {suc n} A =
    ∑ {suc (suc n)}
      (λ i →
        ∑ (λ j → ind> (toℕ i) (toℕ j) · A i j))
    ≡⟨ refl ⟩
    ∑ {suc n}
      (λ j → ind> zero (toℕ j) · A zero j)
    + ∑ (λ i →
        ∑ (λ j →
          ind> (toℕ (suc i)) (toℕ j) · A (suc i) j))
    ≡⟨
      cong
       (λ a → a + ∑ (λ i →
                    ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j)))
       (∑Compat
         (λ j → ind> zero (toℕ j) · A zero j)
         (λ j → 0r)
         (λ j → solve! P'))
     ⟩
    ∑ {suc n} (λ j → 0r) +
    ∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j))
    ≡⟨
      cong
      (λ a → a + ∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j)))
      (∑Zero {suc n} (λ j → 0r) (λ j → refl)) ⟩
    0r + ∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j))
    ≡⟨
      +Comm
       0r
       (∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j)))
     ⟩
    ∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j)) + 0r
    ≡⟨
      +IdR
        (∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j)))
     ⟩
    ∑ (λ i → ∑ (λ j → ind> (toℕ (suc i)) (toℕ j) · A (suc i) j))
    ∎

  ∑∑ShiftWeak : {n : ℕ} → (A : Fin (suc n) → Fin n → R) →
    ∑ (λ (i : Fin (suc n)) → ∑ ( λ j → (1r + - ind> (toℕ i) (toℕ j)) · A i j))
    ≡
    ∑ (λ (i : Fin n) →
         ∑ ( λ j →
             (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) · A (weakenFin i) j))
  ∑∑ShiftWeak {zero} A =
    ∑Zero {one}
      (λ i → ∑ ( λ j → (1r + - ind> (toℕ i) (toℕ j)) · A i j))
      (λ i → refl)
  ∑∑ShiftWeak {suc n} A =
    (∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
      ∑
      (λ i → ∑ (λ j → (1r + - ind> (toℕ (suc i)) (toℕ j)) · A (suc i) j)))
    ≡⟨
      cong
        (λ a →  ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) + a)
        (∑Compat
          (λ i → ∑ (λ j → (1r + - ind> (toℕ (suc i)) (toℕ j)) · A (suc i) j))
          (λ i →
            (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero +
            ∑ (λ j → (1r + - ind> (toℕ (suc i)) (toℕ (suc j))) · A (suc i) (suc j)))
          (λ i → refl))
      ⟩
    ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
    ∑ (λ i →
         (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero +
           ∑ (λ j →
             (1r + - ind> (toℕ (suc i)) (toℕ (suc j))) · A (suc i) (suc j)))
    ≡⟨
      cong
      (λ a →  ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) + a)
      (∑Split
        (λ i →
          (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero)
          (λ i →
            ∑ (λ j →
                 (1r + - ind> (toℕ (suc i)) (toℕ (suc j)))
                 · A (suc i) (suc j))))
     ⟩
    (∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
      (∑ (λ i → (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero) +
       ∑
       (λ i →
          ∑ (λ j → (1r + - ind> (toℕ i) (toℕ j)) · A (suc i) (suc j)))))
    ≡⟨
      cong
       (λ a →
         ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
         (∑ (λ i →
           (1r + - ind> (toℕ (suc i)) zero) ·
           A (suc i) zero) + a))
       (∑∑ShiftWeak (λ i j →  A (suc i) (suc j)))
     ⟩
    (∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
      (∑ (λ i → (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero) +
       ∑
       (λ i →
          ∑
          (λ j →
             (1r + - ind> (toℕ (suc (weakenFin i))) (toℕ (suc j)))
             · A (suc (weakenFin i)) (suc j)))))
    ≡⟨
      cong
      (λ a →
        (∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
        (a +
         ∑ (λ i →
           ∑ (λ j →
             (1r + - ind> (toℕ (suc (weakenFin i))) (toℕ (suc j)))
             · A (suc (weakenFin i)) (suc j))))))
      (
        ∑ (λ i → (1r + - ind> (toℕ (suc i)) zero) · A (suc i) zero)
        ≡⟨ refl ⟩
        ∑ (λ i →
          (1r + - 1r) · A (suc i) zero)
        ≡⟨ ∑Compat (
           λ i → (1r + - 1r) · A (suc i) zero)
           (λ i → 0r)
           (λ i → solve! P')
         ⟩
        ∑ (λ (i : Fin (suc n)) → 0r)
        ≡⟨
          ∑Zero
            (λ (i : Fin (suc n)) → 0r)
            (λ i → refl)
         ⟩
        0r
        ≡⟨ sym (∑Zero (λ (i : Fin n) → 0r) (λ i → refl)) ⟩
        ∑ (λ (i : Fin  n) → 0r)
        ≡⟨ ∑Compat
           (λ (i : Fin  n) → 0r)
           (λ i → (1r + - 1r) · A (suc (weakenFin i)) zero)
           (λ i → solve! P')
         ⟩
        ∑ (λ i → (1r + - 1r) · A (suc (weakenFin i)) zero)∎
      )⟩
    (∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
      (∑
       (λ i →
          (1r + - ind> (toℕ (suc (weakenFin i))) zero) ·
          A (suc (weakenFin i)) zero)
       +
       ∑
       (λ i →
          ∑
          (λ j →
             (1r + - ind> (toℕ (suc (weakenFin i))) (toℕ (suc j))) ·
             A (suc (weakenFin i)) (suc j)))))
    ≡⟨
      cong
      (λ a → ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) + a)
      (sym
        (∑Split
        (λ i →
          (1r + - ind> (toℕ (suc (weakenFin i))) zero) ·
          A (suc (weakenFin i)) zero)
        (λ i → ∑ (λ j →
                 (1r + - ind> (toℕ (suc (weakenFin i))) (toℕ (suc j))) ·
                 A (suc (weakenFin i)) (suc j)))))
     ⟩
    ∑ (λ j → (1r + - ind> zero (toℕ j)) · A zero j) +
       ∑
       (λ i →
          ∑
          (λ j →
             (1r + - ind> (toℕ (suc (weakenFin i))) (toℕ j)) ·
             A (suc (weakenFin i)) j)) ∎
