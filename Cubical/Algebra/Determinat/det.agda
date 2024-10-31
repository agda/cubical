{-# OPTIONS --cubical #-}

module det where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Data.Bool
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order using (_<'Fin_; _≤'Fin_)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Semiring
open import Cubical.Data.Int.Base using (pos; negsuc)
open import Cubical.Data.Vec.Base using (_∷_; [])
open import Cubical.Data.Nat.Order
open import Cubical.Tactics.CommRingSolver
open import Minor
open import RingSum

module Determinat (ℓ : Level) (P' : CommRing ℓ) where

  open Minor.Minor ℓ
  open RingSum.RingSum ℓ P'
  open RingStr (snd (CommRing→Ring P')) renaming ( is-set to isSetR )

  CommRingR' : CommRingStr (R' .fst)
  CommRingR' =  commringstr 0r 1r _+_ _·_ -_ (CommRingStr.isCommRing (snd P'))

  -- Definition of the minor factor
  MF :  (i : ℕ) → R
  MF zero = 1r
  MF (suc i) = (- 1r) · (MF i)

  --Properties of the minor factor
  sumMF : (i j : ℕ) → MF (i +ℕ j) ≡ (MF i) · (MF j)
  sumMF zero j =
    MF j
    ≡⟨ sym (·IdL (MF j)) ⟩
    1r · (MF j)
    ≡⟨ refl ⟩
    (MF zero) · (MF j)∎
  sumMF (suc i) j =
    MF (suc i +ℕ j)
    ≡⟨ refl ⟩
    ((- 1r) · (MF (i +ℕ j)))
    ≡⟨ cong (λ x → (- 1r) · x) (sumMF  i j) ⟩
    ((- 1r) · ((MF i) · (MF j)))
    ≡⟨ ·Assoc _ _ _ ⟩
    ((- 1r) · (MF i)) · (MF j)
    ∎

  sucMFRev : (i : ℕ) → MF i ≡ (- 1r) · MF (suc i)
  sucMFRev i = solve! P'

  MFplusZero : {n : ℕ} → (i : Fin n) →   MF (toℕ i +ℕ zero) ≡ MF (toℕ i)
  MFplusZero i =
    MF (toℕ i +ℕ zero)
    ≡⟨ sumMF (toℕ i) zero ⟩
    (MF (toℕ i) · MF zero)
    ≡⟨ ·IdR (MF (toℕ i)) ⟩
    MF (toℕ i)
    ∎

  MFsucsuc :  {n m : ℕ} → (j : Fin n) → (k : Fin m) →
    MF (toℕ (suc j) +ℕ (toℕ (suc k))) ≡ MF (toℕ j +ℕ toℕ k)
  MFsucsuc j k =
    MF (toℕ (suc j) +ℕ toℕ (suc k))
    ≡⟨ sumMF (toℕ (suc j)) (toℕ (suc k)) ⟩
    (MF (toℕ (suc j)) · MF (toℕ (suc k)))
    ≡⟨ refl ⟩
    ((- 1r) · MF (toℕ j) · ((- 1r) · MF (toℕ k)) )
    ≡⟨ solve! P' ⟩
    ( MF (toℕ j) · MF ( toℕ k))
    ≡⟨ sym (sumMF (toℕ j) (toℕ k))⟩
    MF (toℕ j +ℕ toℕ k)
    ∎

  -- Other small lemmata
  +Compat : {a b c d : R} → a ≡ b → c ≡ d → a + c ≡ b + d
  +Compat {a} {b} {c} {d} eq1 eq2 =
   a + c
   ≡⟨ cong (λ x → x + c) eq1 ⟩
   b + c
   ≡⟨ cong (λ x → b + x) eq2 ⟩
   b + d
   ∎

  distributeOne : (a b : R) → b ≡ a · b + (1r + (- a)) · b
  distributeOne a b = solve! P'

  -- Definition of the determinat by using Laplace expansion
  det : ∀ {n} → FinMatrix R n n → R
  det {zero} M = 1r
  det {suc n} M = ∑ (λ j → (MF (toℕ j)) · (M zero j) · det {n} (minor zero j M))

  detComp : {n : ℕ} → (M N : FinMatrix R n n) → ((i j : Fin n) → M i j ≡ N i j ) → det M ≡ det N
  detComp {zero} M N f = refl
  detComp {suc n} M N f =
    ∑ (λ j → MF (toℕ j) · M zero j · det (minor zero j M))
    ≡⟨ ∑Compat (λ j → (MF (toℕ j)) · (M zero j) · det (minor zero j M))
               (λ j → (MF (toℕ j)) · (N zero j) · det (minor zero j M))
               (λ j → cong (λ a → (MF (toℕ j)) · a · det (minor zero j M)) (f zero j)) ⟩
    ∑ (λ j → MF (toℕ j) · N zero j · det (minor zero j M))
    ≡⟨ ∑Compat (λ j → (MF (toℕ j)) · (N zero j) · det (minor zero j M))
               (λ j → (MF (toℕ j)) · (N zero j) · det (minor zero j N))
               (λ j → cong (λ a → (MF (toℕ j)) · (N zero j) · a) (detComp (minor zero j M) (minor zero j N) (minorComp zero j M N f)) ) ⟩
    ∑ (λ j → MF (toℕ j) · N zero j · det (minor zero j N)) ∎

  -- Independence of the row in the Laplace expansion.
  detR : ∀ {n} → (k : Fin n) → FinMatrix R n n → R
  detR {suc n} k M = ∑ (λ j → (MF ((toℕ k) +ℕ (toℕ j))) · (M k j) · det {n} (minor k j M))

  DetRowAux1 : {n : ℕ} →
           (k i : Fin (suc (suc n))) →
           (j : Fin (suc n)) →
            (M : FinMatrix R  (suc (suc n)) (suc (suc n))) →
           MF ((toℕ k) +ℕ (toℕ i)) · M k i ·
           (MF (toℕ j) · minor k i M zero j ·
           det (minor zero j (minor k i M)))
           ≡
           ( MF ((toℕ k) +ℕ (toℕ i) +ℕ (toℕ j)) ·
           M k i · minor k i M zero j ·
           det (minor zero j (minor k i M)))
  DetRowAux1 k i j M =
     (MF (toℕ k +ℕ toℕ i) · M k i ·
       (MF (toℕ j) · minor k i M zero j ·
        det (minor zero j (minor k i M))))
     ≡⟨
       ·Assoc
         ( MF ((toℕ k) +ℕ (toℕ i)) · M k i)
         (MF (toℕ j) · minor k i M zero j)
         ( det (minor zero j (minor k i M)))
      ⟩
     (MF (toℕ k +ℕ toℕ i) · M k i · (MF (toℕ j) · minor k i M zero j) ·
       det (minor zero j (minor k i M)))
     ≡⟨
       cong
       (λ x → (x · det (minor zero j (minor k i M))))
       (·Assoc
         ( MF ((toℕ k) +ℕ (toℕ i)) · M k i)
         (MF (toℕ j))
         ( minor k i M zero j))
      ⟩
     (MF (toℕ k +ℕ toℕ i) · M k i · MF (toℕ j) · minor k i M zero j ·
       det (minor zero j (minor k i M)))
     ≡⟨
       cong
       (λ x → x ·  minor k i M zero j · det (minor zero j (minor k i M)))
       (sym (·Assoc (MF ((toℕ k) +ℕ (toℕ i))) ( M k i ) (MF (toℕ j))))
      ⟩
     (MF (toℕ k +ℕ toℕ i) · (M k i · MF (toℕ j)) · minor k i M zero j ·
       det (minor zero j (minor k i M)))
     ≡⟨
       cong
        ( λ x →
            MF ((toℕ k) +ℕ (toℕ i)) · x ·
            minor k i M zero j ·
            det (minor zero j (minor k i M)))
        (CommRingStr.·Comm  CommRingR' (M k i) ( MF (toℕ j)))
      ⟩
     MF (toℕ k +ℕ toℕ i) · (MF (toℕ j) · M k i)
     · minor k i M zero j
     · det (minor zero j (minor k i M))
     ≡⟨
       cong
        (λ x →
          x · minor k i M zero j · det (minor zero j (minor k i M)))
        (·Assoc (MF ((toℕ k) +ℕ (toℕ i))) ( MF (toℕ j)) (M k i))
       ⟩
     (MF (toℕ k +ℕ toℕ i) · MF (toℕ j) · M k i · minor k i M zero j ·
       det (minor zero j (minor k i M)))
     ≡⟨
       cong
       (λ x →
         x ·  M k i · minor k i M zero j
         · det (minor zero j (minor k i M)))
       (sym (sumMF (toℕ k +ℕ toℕ i) ( toℕ j)))
      ⟩
    (MF (toℕ k +ℕ toℕ i +ℕ toℕ j) · M k i · minor k i M zero j ·
      det (minor zero j (minor k i M)))
     ∎

  DetRowAux3a :
    {n : ℕ} → (k : Fin (suc n)) →
    (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑ (λ (i : Fin (suc (suc n)))  →
      ∑ (λ (j : Fin (suc n))  →
        ind> (toℕ i) (toℕ j) ·
        (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j)
        · M (suc k) i · minor (suc k) i M zero j
        · det (minor zero j (minor (suc k) i M)))))
    ≡
    ∑ (λ (i : Fin (suc n))  →
      ∑ (λ (j : Fin (suc n))  →
        ind> (toℕ (suc i)) (toℕ j) ·
        (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j)
        · M (suc k) (suc i) · minor (suc k) (suc i) M zero j
        · det (minor zero j (minor (suc k) (suc i) M)))))
  DetRowAux3a k M =
    ∑∑ShiftSuc
      (λ i j →
        (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j)
        · M (suc k) i · minor (suc k) i M zero j
        · det (minor zero j (minor (suc k) i M))))

  DetRowAux3b :     {n : ℕ} → (k : Fin (suc n)) →
    (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ i) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
            minor (suc k) i M zero j
            · det (minor zero j (minor (suc k) i M)))))
    ≡
     ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) · M (suc k) (weakenFin i) ·
            minor (suc k) (weakenFin i) M zero j
            · det (minor zero j (minor (suc k) (weakenFin i) M)))))
  DetRowAux3b k M =
    ∑∑ShiftWeak
      (λ i j →
        (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j)
        · M (suc k) i · minor (suc k) i M zero j
        · det (minor zero j (minor (suc k) i M))))

  DetRowAux4a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑ (λ i →
         ∑ (λ j →
           ind> (toℕ (suc i)) (toℕ j) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
           minor (suc k) (suc i) M zero j
           · det (minor zero j (minor (suc k) (suc i) M)))))
    ≡
    ∑ (λ i →
      ∑ (λ j →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
           M zero (weakenFin j)
           · det (minor k i (minor zero (weakenFin j) M)))))
  DetRowAux4a k M =
    ∑∑Compat
      (λ i j →
        ind> (toℕ (suc i)) (toℕ j) ·
        (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
        minor (suc k) (suc i) M zero j
        · det (minor zero j (minor (suc k) (suc i) M))))
      (λ i j → (1r + - ind> (toℕ j) (toℕ i)) ·
               (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
               M zero (weakenFin j)
               · det (minor k i (minor zero (weakenFin j) M))))
      λ i j →
       (
       ind> (toℕ (suc i)) (toℕ j) ·
         (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
          minor (suc k) (suc i) M zero j
          · det (minor zero j (minor (suc k) (suc i) M)))
       ≡⟨
         cong
          (λ a →
            a ·(MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j)
            · M (suc k) (suc i) · minor (suc k) (suc i) M zero j
            · det (minor zero j (minor (suc k) (suc i) M))))
          (ind>Suc (toℕ i) (toℕ j))
        ⟩
       (1r + - ind> (toℕ j) (toℕ i)) ·
         (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
          minor (suc k) (suc i) M zero j
          · det (minor zero j (minor (suc k) (suc i) M)))
       ≡⟨ ind>anti
          (λ j i →
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            minor (suc k) (suc i) M zero j
            · det (minor zero j (minor (suc k) (suc i) M))))
          (λ j i  →
            MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero (weakenFin j)
            · det (minor k i (minor zero (weakenFin j) M)))
          (λ j i le →
            (
              (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
               minor (suc k) (suc i) M zero j
               · det (minor zero j (minor (suc k) (suc i) M)))
              ≡⟨
                cong
                  (λ a →
                    (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j)
                     · M (suc k) (suc i)
                     · a
                     · det (minor zero j (minor (suc k) (suc i) M))))
                  (minorIdId (suc k) (suc i) zero j M (s≤s z≤) (s≤s le))
               ⟩
              (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
               M zero (weakenFin j)
               · det (minor zero j (minor (suc k) (suc i) M)))
              ≡⟨ cong
                 (λ a →
                   (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
                   M zero (weakenFin j) · a))
                 (detComp
                   (minor zero j (minor (suc k) (suc i) M))
                   (minor k i (minor (weakenFin zero) (weakenFin j) M))
                   λ i₁ j₁ →
                     minorComm0 k zero i j i₁ j₁ M z≤ le )
               ⟩
              (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
                M zero (weakenFin j)
                · det (minor k i (minor zero (weakenFin j) M)))
              ∎
             )
          )
          j
          i ⟩
       (1r + - ind> (toℕ j) (toℕ i)) ·
         (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
          M zero (weakenFin j)
          · det (minor k i (minor zero (weakenFin j) M)))
       ∎)

  toℕweakenFin : {n : ℕ} → (i : Fin n) → toℕ (weakenFin i) ≡ toℕ i
  toℕweakenFin zero = refl
  toℕweakenFin (suc i) = cong suc (toℕweakenFin i)

  weakenweakenFinLe : {n : ℕ} → (i : Fin (suc n)) → (j : Fin (suc n)) → toℕ i ≤' toℕ j → weakenFin i ≤'Fin weakenFin j
  weakenweakenFinLe {zero} zero zero le = le
  weakenweakenFinLe {suc n} zero zero le = le
  weakenweakenFinLe {suc n} zero (suc j) le = z≤
  weakenweakenFinLe {suc n} (suc i) (suc j) (s≤s le) = s≤s (weakenweakenFinLe {n} i j le)

  DetRowAux4b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · minor (suc k) (weakenFin i) M zero j
            · det (minor zero j (minor (suc k) (weakenFin i) M)))))
    ≡
    ∑
     (λ i →
        ∑
        (λ j →
             (ind> (suc (toℕ j)) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M))))))
  DetRowAux4b k M =
    ∑∑Compat
      (λ i j →
        (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
        (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
         M (suc k) (weakenFin i)
         · minor (suc k) (weakenFin i) M zero j
         · det (minor zero j (minor (suc k) (weakenFin i) M))))
         (λ z z₁ →
             ind> (suc (toℕ z₁)) (toℕ z) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin z) +ℕ toℕ z₁) ·
              M (suc k) (weakenFin z)
              · M (weakenFin zero) (suc z₁)
              · det (minor k z (minor zero (suc z₁) M))))
         λ i j →
           (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · minor (suc k) (weakenFin i) M zero j
              · det (minor zero j (minor (suc k) (weakenFin i) M)))
           ≡⟨
             cong
             (λ a →
               (1r + - ind> a (toℕ j)) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · minor (suc k) (weakenFin i) M zero j
              · det (minor zero j (minor (suc k) (weakenFin i) M))))
             (toℕweakenFin i)
            ⟩
           (1r + - ind> (toℕ i) (toℕ j)) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · minor (suc k) (weakenFin i) M zero j
              · det (minor zero j (minor (suc k) (weakenFin i) M)))
           ≡⟨ ind>anti
             (λ i j → (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · minor (suc k) (weakenFin i) M zero j
              · det (minor zero j (minor (suc k) (weakenFin i) M))))
             (λ i j → MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                        M (suc k) (weakenFin i)
                        · M (weakenFin zero) (suc j)
                        · det (minor k i (minor zero (suc j) M)))
             (λ i j le →
               ((MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                 M (suc k) (weakenFin i)
                 · minor (suc k) (weakenFin i) M zero j
                 · det (minor zero j (minor (suc k) (weakenFin i) M))))
               ≡⟨ cong
                  (λ a →
                    (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                    M (suc k) (weakenFin i) · a
                    · det (minor zero j (minor (suc k) (weakenFin i) M))))
                  (minorIdSuc
                    (suc k)
                    (weakenFin i)
                    zero
                    j
                    M
                    (s≤s z≤)
                    (weakenweakenFinLe i j le)) ⟩
               (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                 M (suc k) (weakenFin i)
                 · M (weakenFin zero) (suc j)
                 · det (minor zero j (minor (suc k) (weakenFin i) M)))
               ≡⟨ cong
                  (λ a →
                    MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                    M (suc k) (weakenFin i)
                    · M (weakenFin zero) (suc j) · a)
                  (detComp
                    (minor zero j (minor (suc k) (weakenFin i) M))
                    (minor k i (minor zero (suc j) M))
                    (λ i₁ j₁ →
                      minorComm1 k zero i j i₁ j₁ M z≤ le))
                   ⟩
               (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
                 M (suc k) (weakenFin i)
                 · M (weakenFin zero) (suc j)
                 · det (minor k i (minor zero (suc j) M)))
               ∎)
             i
             j ⟩
           (1r + - ind> (toℕ i) (toℕ j)) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M)))
           ≡⟨ cong
              (λ a →
                 a · (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M))))
              (sym (ind>Suc (toℕ j) (toℕ i)))
            ⟩
           (ind> (suc (toℕ j)) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M))))
           ∎


  DetRowAux5a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero (weakenFin j)
            · det (minor k i (minor zero (weakenFin j) M)))))
    ≡
    ∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M)))))
  DetRowAux5a k M = ∑Comm λ i j → (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero (weakenFin j)
            · det (minor k i (minor zero (weakenFin j) M)))

  DetRowAux5b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
     ∑
     (λ i →
        ∑
        (λ j →
           ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M)))))
     ≡
     ∑
       (λ j →
          ∑
          (λ i →
             ind> (suc (toℕ j)) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M)))))
  DetRowAux5b k M =
    ∑Comm (λ i j →
           ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M))))

  DetRowAux6a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M)))))
    ≡
    ∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero j
             · det (minor k i (minor zero j M)))))
  DetRowAux6a k M =
    ∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M)))))
    ≡⟨ ∑∑Compat
         (λ j i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M))))
         (λ j i →
            (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (weakenFin j)) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M))))
         (λ j i →
           cong (λ a →
                   (1r + - ind> a (toℕ i)) ·
                   (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ a) · M (suc k) (suc i) ·
                   M zero (weakenFin j)
                   · det (minor k i (minor zero (weakenFin j) M))))
                (sym (toℕweakenFin j)))
     ⟩
    ∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (weakenFin j)) ·
             M (suc k) (suc i)
             · M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M)))))
    ≡⟨ sym (∑∑ShiftWeak
      λ j i →
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) ·
             M (suc k) (suc i)
             · M zero j
             · det (minor k i (minor zero j M)))) ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · M (suc k) (suc j) ·
             M zero i
             · det (minor k j (minor zero i M)))))
    ∎

  DetRowAux6bAux : {n : ℕ} → (k : Fin (suc n)) → (i j : Fin (suc n)) →
    MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j)
    ≡
    MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (suc j))
  DetRowAux6bAux k i j =
    MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j)
    ≡⟨ sumMF (toℕ (suc k) +ℕ toℕ (weakenFin i)) (toℕ j) ⟩
    (MF (toℕ (suc k) +ℕ toℕ (weakenFin i)) · MF (toℕ j))
    ≡⟨ cong
       (λ a →
         a · MF (toℕ j))
       (sumMF (toℕ (suc k)) (toℕ (weakenFin i)))
     ⟩
    (MF (toℕ (suc k)) · MF (toℕ (weakenFin i)) · MF (toℕ j))
    ≡⟨ cong
       (λ a →
         MF (toℕ (suc k)) · (MF a ) · MF (toℕ j))
       (toℕweakenFin i)
     ⟩
    (MF (toℕ (suc k)) · MF (toℕ i) · MF (toℕ j))
    ≡⟨ sym
      (·Assoc
        (MF (toℕ (suc k)))
        (MF (toℕ i))
        (MF (toℕ j)))
     ⟩
    (MF (toℕ (suc k)) · (MF (toℕ i) · MF (toℕ j)))
    ≡⟨ cong
      (λ a →
        MF (toℕ (suc k)) · a)
      (solve! P') ⟩
    MF (toℕ (suc k)) · (MF (toℕ (suc i)) · MF (toℕ (suc j)))
    ≡⟨
      ·Assoc
        (MF (toℕ (suc k)))
        (MF (toℕ (suc i)))
        (MF (toℕ (suc j)))
     ⟩
    (MF (toℕ (suc k)) · MF (toℕ (suc i)) · MF (toℕ (suc j)))
    ≡⟨ cong
      (λ a → a · MF (toℕ (suc j)))
      (sym (sumMF (toℕ (suc k)) (toℕ (suc i))))
     ⟩
    (MF (toℕ (suc k) +ℕ toℕ (suc i)) · MF (toℕ (suc j)))
    ≡⟨ sym (sumMF (toℕ (suc k) +ℕ toℕ (suc i)) (toℕ (suc j))) ⟩
    MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (suc j))
    ∎

  DetRowAux6b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
     ∑
     (λ j →
        ∑
        (λ i →
           ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M)))))
     ≡
     ∑
       (λ j →
          ∑
          (λ i →
             ind> (toℕ j) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (weakenFin i)
              · M zero j
              · det (minor k i (minor zero j M)))))

  DetRowAux6b k M =
    ∑
      (λ i →
         ∑
         (λ i₁ →
            ind> (suc (toℕ i)) (toℕ i₁) ·
            (MF (toℕ (suc k) +ℕ toℕ (weakenFin i₁) +ℕ toℕ i) ·
             M (suc k) (weakenFin i₁)
             · M (weakenFin zero) (suc i)
             · det (minor k i₁ (minor zero (suc i) M)))))
    ≡⟨ ∑∑Compat
       (λ j i →
        ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M))))
      (λ j i →
        ind> (suc (toℕ j)) (toℕ i) ·
        (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (suc j)) ·
         M (suc k) (weakenFin i)
         · M (weakenFin zero) (suc j)
         · det (minor k i (minor zero (suc j) M))))
      (λ j i →
      (ind> (suc (toℕ j)) (toℕ i) ·
        (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
         M (suc k) (weakenFin i)
         · M (weakenFin zero) (suc j)
         · det (minor k i (minor zero (suc j) M))))
      ≡⟨ cong
         (λ a →
           ind> (suc (toℕ j)) (toℕ i) ·
             (a ·
             M (suc k) (weakenFin i)
             · M (weakenFin zero) (suc j)
             · det (minor k i (minor zero (suc j) M))))
         (DetRowAux6bAux k i j)
       ⟩
      (ind> (suc (toℕ j)) (toℕ i) ·
        (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (suc j)) ·
         M (suc k) (weakenFin i)
         · M (weakenFin zero) (suc j)
         · det (minor k i (minor zero (suc j) M))))
      ∎)
      ⟩
     ∑
       (λ j →
          ∑
          (λ i →
             ind> (suc (toℕ j)) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ (suc j)) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) (suc j)
              · det (minor k i (minor zero (suc j) M)))))
     ≡⟨ sym (∑∑ShiftSuc λ j i → (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M (weakenFin zero) j
              · det (minor k i (minor zero j M)))) ⟩
     ∑
       (λ j →
          ∑
          (λ i →
             ind> (toℕ j) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) ·
              M (suc k) (weakenFin i)
              · M zero j
              · det (minor k i (minor zero j M)))))
     ∎

  weakenFinLe : {n : ℕ} → (i : Fin (suc (suc n))) → (j : Fin (suc n)) → toℕ i ≤' toℕ j → i ≤'Fin weakenFin j
  weakenFinLe {zero} zero zero le = le
  weakenFinLe {zero} one zero ()
  weakenFinLe {zero} one (suc ()) le
  weakenFinLe {suc n} zero j le = z≤
  weakenFinLe {suc n} (suc i) (suc j) (s≤s le) = s≤s (weakenFinLe {n} i j le)

  DetRowAux7a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
     (λ j →
        ∑
        (λ i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero j
            · det (minor k i (minor zero j M)))))
    ≡
    ∑
     (λ j →
        ∑
        (λ i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M)))))

  DetRowAux7a k M =
    ∑∑Compat
      (λ j i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero j
            · det (minor k i (minor zero j M))))
      (λ j i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))
      (λ j i →
        ind>anti
          (λ j i → (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero j
            · det (minor k i (minor zero j M))))
          (λ j i → (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))
       (λ j i le →
         cong
         ( λ a → MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · a ·
            M zero j
            · det (minor k i (minor zero j M)))
         (sym (minorSucSuc zero j k i M z≤ (weakenFinLe j i le))))
       j
       i)

  DetRowAux7b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
       (λ j →
          ∑
          (λ i →
             ind> (toℕ j) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (weakenFin i)
              · M zero j
              · det (minor k i (minor zero j M)))))
    ≡
    ∑
      (λ j →
         ∑
         (λ i →
            ind> (toℕ j) (toℕ i) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
             M zero j
             · det (minor k i (minor zero j M)))))
  DetRowAux7b k M =
     ∑∑Compat
      (λ j i →
            ind> (toℕ j) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (weakenFin i)
              · M zero j
              · det (minor k i (minor zero j M))))
      (λ j i →
           (ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))
      (λ j i →
        ind>prop
          (λ j i →
          (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (weakenFin i) ·
            M zero j · det (minor k i (minor zero j M))))
          (λ j i →
          (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))
          (λ j i le →
            cong
            (λ a →
              MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · a ·
            M zero j · det (minor k i (minor zero j M)))
            (sym (minorSucId zero j k i M z≤ le)) )
          j
          i
      )

  DetRowAux8 : {n : ℕ} → (i : Fin (suc (suc n))) → (j k : Fin (suc n))
     → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
     MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j · M zero i · det (minor k j (minor zero i M))
     ≡
     MF (toℕ i) · M zero i · (MF (toℕ k +ℕ toℕ j) · minor zero i M k j · det (minor k j (minor zero i M)))
  DetRowAux8 i j k M =
    (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
      M zero i
      · det (minor k j (minor zero i M)))
    ≡⟨ cong
      (λ a →
        a · minor zero i M k j · M zero i · det (minor k j (minor zero i M)))
      (sumMF (toℕ (suc k) +ℕ toℕ (suc j)) ( toℕ i))
     ⟩
    (MF (toℕ (suc k) +ℕ toℕ (suc j)) · MF (toℕ i) · minor zero i M k j ·
      M zero i
      · det (minor k j (minor zero i M)))
    ≡⟨ cong
       (λ a → a · MF (toℕ i) · minor zero i M k j ·
         M zero i
         · det (minor k j (minor zero i M)))
       (sumMF (toℕ (suc k)) (toℕ (suc j)))
     ⟩
    (MF (toℕ (suc k)) · MF (toℕ (suc j)) · MF (toℕ i) ·
      minor zero i M k j
      · M zero i
      · det (minor k j (minor zero i M)))
    ≡⟨ cong
       (λ a →
         a · MF (toℕ i) ·
         minor zero i M k j
         · M zero i
         · det (minor k j (minor zero i M)))
       (solve! P')
     ⟩
    MF (toℕ k) · MF (toℕ j) · MF (toℕ i) ·
      minor zero i M k j
      · M zero i
      · det (minor k j (minor zero i M))
    ≡⟨ cong
       (λ a →
         a ·  MF (toℕ i) · minor zero i M k j
           · M zero i · det (minor k j (minor zero i M)))
       (sym (sumMF (toℕ k) (toℕ j))) ⟩
    (MF (toℕ k +ℕ toℕ j) · MF (toℕ i) · minor zero i M k j · M zero i ·
      det (minor k j (minor zero i M)))
    ≡⟨ cong
       (λ a → a · det (minor k j (minor zero i M)))
       (solve! P')
     ⟩
    ( MF (toℕ i) · M zero i · MF (toℕ k +ℕ toℕ j) · minor zero i M k j  ·
      det (minor k j (minor zero i M)))
    ≡⟨ sym
      (·Assoc
        (MF (toℕ i) · M zero i · MF (toℕ k +ℕ toℕ j))
        (minor zero i M k j)
        (det (minor k j (minor zero i M))))
     ⟩
    (MF (toℕ i) · M zero i · MF (toℕ k +ℕ toℕ j) ·
      (minor zero i M k j · det (minor k j (minor zero i M))))
    ≡⟨ sym (·Assoc (MF (toℕ i) · M zero i) (MF (toℕ k +ℕ toℕ j)) (minor zero i M k j · det (minor k j (minor zero i M)))) ⟩
    MF (toℕ i) · M zero i · (MF (toℕ k +ℕ toℕ j) ·
       (minor zero i M k j · det (minor k j (minor zero i M))))
    ≡⟨ cong
       (λ a → MF (toℕ i) · M zero i · a)
       (·Assoc (MF (toℕ k +ℕ toℕ j)) (minor zero i M k j) (det (minor k j (minor zero i M)))) ⟩
    (MF (toℕ i) · M zero i · (MF (toℕ k +ℕ toℕ j) ·
       minor zero i M k j · det (minor k j (minor zero i M))))
    ∎


  DetRow : ∀ {n} → (k : Fin n) → (M : FinMatrix R n n) →  (detR k M) ≡ (det M)
  DetRow {one} zero M = refl
  DetRow {suc (suc n)} zero M = refl
  DetRow {suc (suc n)} (suc k) M =
    detR (suc k) M
      ≡⟨ refl ⟩
      ∑
        (λ (i : Fin (suc (suc n))) →
          MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i · det (minor (suc k) i M))
      ≡⟨ refl ⟩
      ∑
        (λ i →
          MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i ·
          ∑
          (λ j →
             MF (toℕ j) · minor (suc k) i M zero j ·
             det (minor zero j (minor (suc k) i M))))
      ≡⟨ ∑Compat (λ i →
         MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i ·
         ∑
         (λ j →
            MF (toℕ j) · minor (suc k) i M zero j ·
            det (minor zero j (minor (suc k) i M))))
         ((λ i →
         ∑
         (λ j →
            MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i ·
            (MF (toℕ j) · minor (suc k) i M zero j ·
            det (minor zero j (minor (suc k) i M))))))
            (λ i → ∑DistR ( MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i)
            (λ j →
              MF (toℕ j) · minor (suc k) i M zero j ·
              det (minor zero j (minor (suc k) i M))))⟩
     ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ (suc k) +ℕ toℕ i) · M (suc k) i ·
            (MF (toℕ j) · minor (suc k) i M zero j ·
            det (minor zero j (minor (suc k) i M)))))
     ≡⟨
       ∑∑Compat
         (λ i j →
           MF (toℕ (suc k) +ℕ toℕ i) ·          M (suc k) i ·
           (MF (toℕ j) · minor (suc k) i M zero j ·
           det (minor zero j (minor (suc k) i M))))
         (λ i j →
           MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
           minor (suc k) i M zero j ·
           det (minor zero j (minor (suc k) i M)))
         (λ i j → DetRowAux1 (suc k) i j M)
      ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
            minor (suc k) i M zero j
            · det (minor zero j (minor (suc k) i M))))
     ≡⟨ ∑∑Compat
        (λ i j →
          MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
          minor (suc k) i M zero j · det (minor zero j (minor (suc k) i M)))
        (λ i j →
          ind> (toℕ i) (toℕ j) ·
            (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
             minor (suc k) i M zero j
             · det (minor zero j (minor (suc k) i M)))
           +
          (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
             minor (suc k) i M zero j
             · det (minor zero j (minor (suc k) i M))))
        (λ i j →
          distributeOne (ind> (toℕ i) (toℕ j))
          (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
          minor (suc k) i M zero j · det (minor zero j (minor (suc k) i M))))
    ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
             minor (suc k) i M zero j
             · det (minor zero j (minor (suc k) i M)))
            +
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
             minor (suc k) i M zero j
             · det (minor zero j (minor (suc k) i M)))))
   ≡⟨ ∑∑Split
       (λ i j →
         ind> (toℕ i) (toℕ j) ·
         (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
          minor (suc k) i M zero j
          · det (minor zero j (minor (suc k) i M))))
       (λ i j →
         (1r + - ind> (toℕ i) (toℕ j)) ·
         (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
          minor (suc k) i M zero j
          · det (minor zero j (minor (suc k) i M))))
     ⟩
   (∑
     (λ i →
        ∑
        (λ j →
           ind> (toℕ i) (toℕ j) ·
           (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
            minor (suc k) i M zero j
            · det (minor zero j (minor (suc k) i M)))))
     +
     ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ i) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ i +ℕ toℕ j) · M (suc k) i ·
            minor (suc k) i M zero j
            · det (minor zero j (minor (suc k) i M))))))
   ≡⟨ +Compat (DetRowAux3a k M) (DetRowAux3b k M) ⟩
   ∑
     (λ i →
        ∑
        (λ j →
           ind> (toℕ (suc i)) (toℕ j) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            minor (suc k) (suc i) M zero j
            · det (minor zero j (minor (suc k) (suc i) M)))))
    +
    ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · minor (suc k) (weakenFin i) M zero j
            · det (minor zero j (minor (suc k) (weakenFin i) M)))))
   ≡⟨ +Compat (DetRowAux4a k M) (DetRowAux4b k M) ⟩
   (∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero (weakenFin j)
            · det (minor k i (minor zero (weakenFin j) M)))))
     +
     ∑
     (λ i →
        ∑
        (λ j →
           ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M))))))
   ≡⟨ +Compat (DetRowAux5a k M) (DetRowAux5b k M) ⟩
   (∑
      (λ j →
         ∑
         (λ i →
            (1r + - ind> (toℕ j) (toℕ i)) ·
            (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
             M zero (weakenFin j)
             · det (minor k i (minor zero (weakenFin j) M))))) +
     ∑
     (λ j →
        ∑
        (λ i →
           ind> (suc (toℕ j)) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (weakenFin i) +ℕ toℕ j) ·
            M (suc k) (weakenFin i)
            · M (weakenFin zero) (suc j)
            · det (minor k i (minor zero (suc j) M))))))
   ≡⟨ +Compat (DetRowAux6a k M) (DetRowAux6b k M) ⟩
   ∑
     (λ j →
        ∑
        (λ i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (suc i) ·
            M zero j
            · det (minor k i (minor zero j M)))))
     +
     ∑
       (λ j →
          ∑
          (λ i →
             ind> (toℕ j) (toℕ i) ·
             (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · M (suc k) (weakenFin i)
              · M zero j
              · det (minor k i (minor zero j M)))))
   ≡⟨ +Compat (DetRowAux7a k M) (DetRowAux7b k M) ⟩
   (∑
     (λ j →
        ∑
        (λ i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M)))))
     +
     ∑
     (λ j →
        ∑
        (λ i →
           ind> (toℕ j) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))))
   ≡⟨ +Comm _  _ ⟩
    ∑
     (λ j →
        ∑
        (λ i →
           ind> (toℕ j) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M)))))
     +
     ∑
     (λ j →
        ∑
        (λ i →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M)))))
   ≡⟨ sym
      (∑∑Split
      (λ j i →
        ind> (toℕ j) (toℕ i) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M))))
      λ j i → (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc i) +ℕ toℕ j) · minor zero j M k i ·
            M zero j
            · det (minor k i (minor zero j M)))
      ) ⟩
   ∑
     (λ i →
        ∑
        (λ j →
           ind> (toℕ i) (toℕ j) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
            M zero i
            · det (minor k j (minor zero i M)))
           +
           (1r + - ind> (toℕ i) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
            M zero i
            · det (minor k j (minor zero i M)))))
   ≡⟨
     ∑∑Compat
     (λ i j →
         (
           ind> (toℕ i) (toℕ j) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
            M zero i
            · det (minor k j (minor zero i M)))
           +
           (1r + - ind> (toℕ i) (toℕ j)) ·
           (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
            M zero i
            · det (minor k j (minor zero i M)))))
     (λ z z₁ →
         MF (toℕ (suc k) +ℕ toℕ (suc z₁) +ℕ toℕ z) · minor zero z M k z₁ ·
         M zero z
         · det (minor k z₁ (minor zero z M)))
     (λ i j →
       sym
       (distributeOne
       (ind> (toℕ i) (toℕ j))
       (MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
         M zero i · det (minor k j (minor zero i M)))))
       ⟩
   ∑
     (λ i →
        ∑
        (λ j →
           MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
           M zero i
           · det (minor k j (minor zero i M))))
   ≡⟨
     ∑∑Compat
       (λ i j → MF (toℕ (suc k) +ℕ toℕ (suc j) +ℕ toℕ i) · minor zero i M k j ·
           M zero i
           · det (minor k j (minor zero i M)))
       (λ z z₁ →
           MF (toℕ z) · M zero z ·
           (MF (toℕ k +ℕ toℕ z₁) · minor zero z M k z₁ ·
            det (minor k z₁ (minor zero z M))))
       (λ i j → DetRowAux8 i j k M)
    ⟩
   ∑
     (λ i →
        ∑
        (λ j →
           MF (toℕ i) · M zero i · (MF (toℕ k +ℕ toℕ j) · minor zero i M k j
           · det (minor k j (minor zero i M)))))
   ≡⟨
     ∑Compat
     (λ i →
        ∑
        (λ j →
           MF (toℕ i) · M zero i · (MF (toℕ k +ℕ toℕ j) · minor zero i M k j
           · det (minor k j (minor zero i M)))))
     (λ i →
       MF (toℕ i) · M zero i ·
        ∑
        (λ j →
           MF (toℕ k +ℕ toℕ j) · minor zero i M k j
           · det (minor k j (minor zero i M))))
     (λ i → sym
            (∑DistR
              ( MF (toℕ i) · M zero i)
              (λ j → MF (toℕ k +ℕ toℕ j) · minor zero i M k j
                     · det (minor k j (minor zero i M)))))
    ⟩
   ∑
     (λ i →
       MF (toℕ i) · M zero i ·
        ∑
        (λ j →
           MF (toℕ k +ℕ toℕ j) · minor zero i M k j
           · det (minor k j (minor zero i M))))
   ≡⟨ ∑Compat
      (λ i →
       MF (toℕ i) · M zero i ·
        detR k (minor zero i M))
      (λ i →
       MF (toℕ i) · M zero i ·
        det (minor zero i M))
      (λ i →
        cong
          (λ a → MF (toℕ i) · M zero i · a)
          (DetRow k (minor zero i M)))
    ⟩
   ∑ (λ i → MF (toℕ i) · M zero i · det (minor zero i M))
   ∎

  --Laplace expansion along columns

  detC : ∀ {n} → (k : Fin n) → FinMatrix R n n → R
  detC  {suc n} k M = ∑ (λ i → (MF ((toℕ i) +ℕ (toℕ k))) · (M i k) · det {n} (minor i k M))

  DetRowColumnAux : {n : ℕ} →  (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
            (MF (toℕ j) · minor (suc i) zero M zero j ·
             det (minor zero j (minor (suc i) zero M)))))
    ≡
    ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ (suc j))· M zero (suc j) ·
            (MF (toℕ i +ℕ zero)· minor zero (suc j) M i zero  ·
             det (minor i zero (minor zero (suc j) M)))))

  DetRowColumnAux M =
   ∑∑Compat
     (λ i j →
          MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
          (MF (toℕ j) · minor (suc i) zero M zero j ·
          det (minor zero j (minor (suc i) zero M))))
     (λ i j →
          MF (toℕ (suc j))· M zero (suc j) ·
            (MF (toℕ i +ℕ zero)· minor zero (suc j) M i zero  ·
             det (minor i zero (minor zero (suc j) M))))
     (λ i j →
       (MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
         (MF (toℕ j) · minor (suc i) zero M zero j ·
          det (minor zero j (minor (suc i) zero M))))
       ≡⟨ cong
          (λ a →
             MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
             (MF (toℕ j) · a ·
             det (minor zero j (minor (suc i) zero M))))
          (minorIdSuc (suc i) zero zero j M (s≤s z≤) z≤)
        ⟩
        (MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
         (MF (toℕ j) · M zero (suc j) ·
          det (minor zero j (minor (suc i) zero M))))
       ≡⟨
         cong
         (λ a →
           MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
           (MF (toℕ j) · M zero (suc j) · a))
         (detComp
           (minor zero j (minor (suc i) zero M))
           (minor i zero (minor zero (suc j) M))
           (λ i₁ j₁ → (minorComm1 i zero zero j i₁ j₁ M z≤ z≤)))
        ⟩
       (MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
         (MF (toℕ j) · M zero (suc j) ·
          det (minor i zero (minor zero (suc j) M))))
       ≡⟨ ·Assoc (MF (toℕ (suc i) +ℕ zero) · M (suc i) zero) (MF (toℕ j) · M zero (suc j)) (det (minor i zero (minor zero (suc j) M))) ⟩
       MF (toℕ (suc i) +ℕ zero) · M (suc i) zero · (MF (toℕ j) · M zero (suc j)) ·
         det (minor i zero (minor zero (suc j) M))
       ≡⟨
        cong
          (λ a → a · M (suc i) zero ·
          (MF (toℕ j) · M zero (suc j)) ·
          det (minor i zero (minor zero (suc j) M)))
          (MF (toℕ (suc i) +ℕ zero)
          ≡⟨ sumMF (toℕ (suc i)) zero ⟩
          (MF (toℕ (suc i)) · MF zero)
          ≡⟨ solve! P' ⟩
          MF (toℕ (suc i))
          ∎)
        ⟩
        MF (toℕ (suc i)) · M (suc i) zero · (MF (toℕ j) · M zero (suc j)) ·
         det (minor i zero (minor zero (suc j) M))
       ≡⟨ cong
          (λ a →
              a ·
              det (minor i zero (minor zero (suc j) M)))
              (solve! P') ⟩
       MF (toℕ (suc j)) · M zero (suc j) ·
       MF (toℕ i) · M (suc i) zero ·
       det (minor i zero (minor zero (suc j) M))
       ≡⟨ sym (·Assoc (MF (toℕ (suc j)) · M zero (suc j) · MF (toℕ i)) (M (suc i) zero) (det (minor i zero (minor zero (suc j) M)))) ⟩
       (MF (toℕ (suc j)) · M zero (suc j) · MF (toℕ i) ·
         (M (suc i) zero · det (minor i zero (minor zero (suc j) M))))
       ≡⟨ sym (·Assoc (MF (toℕ (suc j)) · M zero (suc j)) (MF (toℕ i)) (M (suc i) zero · det (minor i zero (minor zero (suc j) M)))) ⟩
       (MF (toℕ (suc j)) · M zero (suc j) ·
         (MF (toℕ i) ·
          (M (suc i) zero · det (minor i zero (minor zero (suc j) M)))))
       ≡⟨ cong (λ a → MF (toℕ (suc j)) · M zero (suc j) · a)
       (·Assoc (MF (toℕ i)) (M (suc i) zero) (det (minor i zero (minor zero (suc j) M)))) ⟩
       MF (toℕ (suc j)) · M zero (suc j) ·
       (MF (toℕ i) · M (suc i) zero ·
        det (minor i zero (minor zero (suc j) M)))
       ≡⟨ refl ⟩
       (MF (toℕ (suc j)) · M zero (suc j) ·
         (MF (toℕ i) · minor zero (suc j) M i zero ·
          det (minor i zero (minor zero (suc j) M))))
       ≡⟨
         cong
         (λ a → (MF (toℕ (suc j)) · M zero (suc j) ·
         (a · minor zero (suc j) M i zero ·
          det (minor i zero (minor zero (suc j) M)))))
          (MF (toℕ i)
          ≡⟨ solve! P' ⟩
          (MF (toℕ i) · MF zero)
           ≡⟨ sym (sumMF (toℕ i) zero) ⟩
           MF (toℕ i +ℕ zero) ∎)
        ⟩
       (MF (toℕ (suc j)) · M zero (suc j) ·
         (MF (toℕ i +ℕ zero) · minor zero (suc j) M i zero ·
          det (minor i zero (minor zero (suc j) M))))
       ∎)

  -- The determinant can also be expanded along the first column.
  DetRowColumn : ∀ {n} →  (M : FinMatrix R (suc n) (suc n)) →
     detC zero M ≡ det M
  DetRowColumn {zero} M = refl
  DetRowColumn {suc n} M =
    detC zero M
    ≡⟨ refl ⟩
    ∑ (λ i → (MF ((toℕ i) +ℕ zero)) · (M i zero) · det {suc n} (minor i zero M))
    ≡⟨ refl ⟩
      1r · (M zero zero) · det  (minor zero zero M) +
      ∑ (λ i → (MF ((toℕ (suc i)) +ℕ zero)) · (M (suc i) zero) · det {suc n} (minor (suc i) zero M))
    ≡⟨ refl ⟩
    (1r · M zero zero · det (minor zero zero M) +
     ∑ (λ i →
      MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
      ∑ (λ j → MF (toℕ j) · minor (suc i) zero M zero j · det (minor zero j (minor (suc i) zero M)))))
    ≡⟨ +Compat
       refl
       (∑Compat
         (λ i → MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
               ∑ (λ j → MF (toℕ j) · minor (suc i) zero M zero j ·
               det (minor zero j (minor (suc i) zero M))))
         (λ i → ∑ (λ j → MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
                (MF (toℕ j) · minor (suc i) zero M zero j ·
               det (minor zero j (minor (suc i) zero M)))))
         (λ i → ∑DistR
                (MF (toℕ (suc i) +ℕ zero) · M (suc i) zero)
                (λ j → MF (toℕ j) · minor (suc i) zero M zero j · det (minor zero j (minor (suc i) zero M)))))
     ⟩
    1r · M zero zero · det (minor zero zero M) +
    ∑ (λ i →
      ∑ (λ j →
        MF (toℕ (suc i) +ℕ zero) · M (suc i) zero ·
        (MF (toℕ j) · minor (suc i) zero M zero j ·
        det (minor zero j (minor (suc i) zero M)))))
    ≡⟨ +Compat refl (DetRowColumnAux M) ⟩
    (1r · M zero zero · det (minor zero zero M) +
      ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ (suc j)) · M zero (suc j) ·
            (MF (toℕ i +ℕ zero) · minor zero (suc j) M i zero ·
             det (minor i zero (minor zero (suc j) M))))))
    ≡⟨ +Compat refl (∑Comm
                    λ i j →
                      MF (toℕ (suc j)) · M zero (suc j) ·
                      (MF (toℕ i +ℕ zero) · minor zero (suc j) M i zero ·
                      det (minor i zero (minor zero (suc j) M)))) ⟩
    (1r · M zero zero · det (minor zero zero M) +
      ∑
      (λ j →
         ∑
         (λ i →
            MF (toℕ (suc j)) · M zero (suc j) ·
            (MF (toℕ i +ℕ zero) · minor zero (suc j) M i zero ·
             det (minor i zero (minor zero (suc j) M))))))
    ≡⟨ +Compat
       refl
       (∑Compat (λ j →
         ∑
         (λ i →
            MF (toℕ (suc j)) · M zero (suc j) ·
            (MF (toℕ i +ℕ zero) · minor zero (suc j) M i zero ·
             det (minor i zero (minor zero (suc j) M)))))
        (λ j →
          MF (toℕ (suc j)) · M zero (suc j) ·
          ∑(λ i →
            (MF (toℕ i +ℕ zero) · M (suc i) zero ·
             det (minor i zero (minor zero (suc j) M)))))
        (λ j → sym (∑DistR (MF (toℕ (suc j)) · M zero (suc j))
          λ i → MF (toℕ i +ℕ zero) · M (suc i) zero ·
             det (minor i zero (minor zero (suc j) M))) )) ⟩
    (1r · M zero zero · det (minor zero zero M) +
      ∑
      (λ j →
         MF (toℕ (suc j)) · M zero (suc j) ·
         detC {suc n} zero (minor zero (suc j) M)))
    ≡⟨ +Compat
      refl
      (∑Compat
        (λ j →
         MF (toℕ (suc j)) · M zero (suc j) ·
         detC {suc n} zero (minor zero (suc j) M))
        (λ j →
         MF (toℕ (suc j)) · M zero (suc j) ·
           det (minor zero (suc j) M))
        (λ j → cong
           (λ a → MF (toℕ (suc j)) · M zero (suc j) · a)
           (DetRowColumn (minor zero (suc j) M))))
     ⟩
    (1r · M zero zero · det (minor zero zero M) +
      ∑
      (λ j →
         MF (toℕ (suc j)) · M zero (suc j) ·
           det (minor zero (suc j) M)))
    ≡⟨ refl ⟩
    det M
    ∎

  DetColumnAux1a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ (suc i)) (toℕ j) ·
            (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
              det (minor j zero (minor (suc i) (suc k) M))))))
    ≡
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
            (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
              det (minor i k (minor (weakenFin j) zero M))))))
  DetColumnAux1a k M =
    ∑∑Compat
      (λ i j → ind> (toℕ (suc i)) (toℕ j) ·
            (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
              det (minor j zero (minor (suc i) (suc k) M)))))
      (λ z z₁ →
          (1r + - ind> (toℕ (weakenFin z₁)) (toℕ z)) ·
          (MF (toℕ (suc z) +ℕ toℕ (suc k)) · M (suc z) (suc k) ·
           (MF (toℕ (weakenFin z₁) +ℕ zero) · M (weakenFin z₁) zero ·
            det (minor z k (minor (weakenFin z₁) zero M)))))
      (λ i j →
       (ind> (suc (toℕ i)) (toℕ j) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
           det (minor j zero (minor (suc i) (suc k) M)))))
       ≡⟨
        cong
        (λ a  → a · (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
              det (minor j zero (minor (suc i) (suc k) M)))))
        (ind>Suc (toℕ i) (toℕ j))
        ⟩
       (1r + - ind> (toℕ j) (toℕ i)) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
           det (minor j zero (minor (suc i) (suc k) M))))
       ≡⟨
         ind>anti
         (λ j i → (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
           det (minor j zero (minor (suc i) (suc k) M)))))
         (λ z z₁ →
             MF (toℕ (suc z₁) +ℕ toℕ (suc k)) · M (suc z₁) (suc k) ·
             (MF (toℕ z +ℕ zero) · M (weakenFin z) zero ·
              det (minor z₁ k (minor (weakenFin z) zero M))))
         (λ j i le →
           (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
              det (minor j zero (minor (suc i) (suc k) M))))
           ≡⟨ cong
             (λ a → (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · a  ·
              det (minor j zero (minor (suc i) (suc k) M)))))
             (minorIdId (suc i) (suc k) j zero M (s≤s le) (s≤s z≤))
            ⟩
           (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
           (MF (toℕ j +ℕ zero) · M (weakenFin j) zero ·
            det (minor j zero (minor (suc i) (suc k) M))))
           ≡⟨
              cong
              (λ a → (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
                      (MF (toℕ j +ℕ zero) · M (weakenFin j) zero · a)))
              (detComp
                (minor j zero (minor (suc i) (suc k) M))
                (minor i k (minor (weakenFin j) zero M))
                (λ i₁ j₁ →
                  minorComm0 i j k zero i₁ j₁ M le z≤))
            ⟩
           (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · M (weakenFin j) zero ·
              det (minor i k (minor (weakenFin j) zero M))))
           ∎)
         j
         i ⟩
       ((1r + - ind> (toℕ j) (toℕ i)) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ j +ℕ zero) · M (weakenFin j) zero ·
           det (minor i k (minor (weakenFin j) zero M)))))
       ≡⟨
         cong
         (λ a →
           (1r + - ind> (toℕ j) (toℕ i)) ·
           (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
           (a · M (weakenFin j) zero ·
           det (minor i k (minor (weakenFin j) zero M)))))
         (MF (toℕ j +ℕ zero)
         ≡⟨ sumMF (toℕ j) zero ⟩
         (MF (toℕ j) · MF zero)
         ≡⟨ cong (λ a → MF a · MF zero) ((toℕ j) ≡⟨ sym (toℕweakenFin j) ⟩ toℕ (weakenFin j) ∎) ⟩
         (MF (toℕ (weakenFin j)) · MF zero)
         ≡⟨ sym (sumMF (toℕ (weakenFin j)) zero) ⟩
         MF (toℕ (weakenFin j) +ℕ zero)
         ∎)
        ⟩
       (1r + - ind> (toℕ j) (toℕ i)) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
           det (minor i k (minor (weakenFin j) zero M))))
       ≡⟨
         cong
         (λ a → (1r + - ind> a (toℕ i)) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
           det (minor i k (minor (weakenFin j) zero M)))))
         (toℕ j ≡⟨ sym (toℕweakenFin j) ⟩ toℕ (weakenFin j) ∎)
        ⟩
       ((1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
         (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
          (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
           det (minor i k (minor (weakenFin j) zero M)))))
       ∎)


  DetColumnAux1b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
            (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
              det (minor j zero (minor (weakenFin i) (suc k) M))))))
    ≡
    ∑
      (λ i →
         ∑
         (λ z →
            ind> (toℕ (suc z)) (toℕ i) ·
            (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
             (MF (toℕ (suc z) +ℕ one) · M (suc z) zero ·
              det (minor i k (minor (suc z) zero M))))))
  DetColumnAux1b k M =
    ∑∑Compat
    (λ i j →
      (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
      (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
      (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
      det (minor j zero (minor (weakenFin i) (suc k) M)))))
      (λ z z₁ →
          ind> (toℕ (suc z₁)) (toℕ z) ·
          (MF (toℕ (weakenFin z) +ℕ toℕ (suc k)) · M (weakenFin z) (suc k) ·
           (MF (toℕ (suc z₁) +ℕ one) · M (suc z₁) zero ·
            det (minor z k (minor (suc z₁) zero M)))))
    (λ i j →
      ((1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
        (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
          det (minor j zero (minor (weakenFin i) (suc k) M)))))
      ≡⟨ cong
         (λ a → (1r + - ind> a (toℕ j)) ·
                (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
                (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
                det (minor j zero (minor (weakenFin i) (suc k) M)))))
         (toℕweakenFin i) ⟩
      ((1r + - ind> (toℕ i) (toℕ j)) ·
        (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
          det (minor j zero (minor (weakenFin i) (suc k) M)))))
      ≡⟨ ind>anti
         (λ i j → MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
                   (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
                   det (minor j zero (minor (weakenFin i) (suc k) M))))
         (λ i j → MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
                    (MF (toℕ j +ℕ zero) · M (suc j) zero ·
                     det (minor i k (minor (suc j) zero M))))
         (λ i j le →
           (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
              det (minor j zero (minor (weakenFin i) (suc k) M))))
           ≡⟨ cong
              (λ a →
                (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
                (MF (toℕ j +ℕ zero) · a ·
                det (minor j zero (minor (weakenFin i) (suc k) M)))))
              (minorSucId
                (weakenFin i)
                (suc k)
                j
                zero
                M
                (weakenweakenFinLe i j le)
                (s≤s z≤))
            ⟩
           (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
           (MF (toℕ j +ℕ zero) · M (suc j) zero ·
            det (minor j zero (minor (weakenFin i) (suc k) M))))
           ≡⟨
             cong
             (λ a →
               MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
               (MF (toℕ j +ℕ zero) · M (suc j) zero · a))
             (detComp
               (minor j zero (minor (weakenFin i) (suc k) M))
               (minor i k (minor (suc j) zero M))
               λ i₁ j₁ →
                 minorComm2
                 i
                 j
                 k
                 zero
                 i₁
                 j₁
                 M
                 le
                 z≤)
            ⟩
           (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
             (MF (toℕ j +ℕ zero) · M (suc j) zero ·
              det (minor i k (minor (suc j) zero M))))
           ∎)
         i
         j
       ⟩
      (1r + - ind> (toℕ i) (toℕ j)) ·
        (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ j +ℕ zero) · M (suc j) zero ·
          det (minor i k (minor (suc j) zero M))))
      ≡⟨ cong
        (λ a → a · (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ j +ℕ zero) · M (suc j) zero ·
          det (minor i k (minor (suc j) zero M)))))
        (sym (ind>Suc (toℕ j) (toℕ i))) ⟩
      (ind> (toℕ (suc j)) (toℕ i) ·
        (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ j +ℕ zero) · M (suc j) zero ·
          det (minor i k (minor (suc j) zero M)))))
      ≡⟨
        cong
         (λ a → (ind> (toℕ (suc j)) (toℕ i) ·
           (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
           (a · M (suc j) zero ·
           det (minor i k (minor (suc j) zero M))))))
         (MF (toℕ j +ℕ zero)
         ≡⟨ sumMF (toℕ j) zero ⟩
         (MF (toℕ j) · MF zero)
         ≡⟨ solve! P' ⟩
         (MF (toℕ (suc j)) · MF one)
         ≡⟨ sym (sumMF (toℕ (suc j)) one) ⟩
         MF (toℕ (suc j) +ℕ one)
         ∎)
       ⟩
      (ind> (toℕ (suc j)) (toℕ i) ·
        (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
         (MF (toℕ (suc j) +ℕ one) · M (suc j) zero ·
          det (minor i k (minor (suc j) zero M)))))
      ∎)

  DetColumnAux2a : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · M (suc j) (suc k) ·
             (MF (toℕ i +ℕ zero) · M i zero ·
              det (minor j k (minor i zero M))))))
   ≡
   ∑
     (λ i →
        ∑
        (λ j →
           (1r + - ind> (toℕ i) (toℕ j)) ·
           (MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))))

  DetColumnAux2a k M =
    ∑∑Compat
      (λ i j →
        (1r + - ind> (toℕ i) (toℕ j)) ·
        (MF (toℕ (suc j) +ℕ toℕ (suc k)) · M (suc j) (suc k) ·
        (MF (toℕ i +ℕ zero) · M i zero ·
        det (minor j k (minor i zero M)))))
      (λ z z₁ →
          (1r + - ind> (toℕ z) (toℕ z₁)) ·
          (MF (toℕ z +ℕ zero) · M z zero ·
           (MF (toℕ (suc z₁) +ℕ toℕ (suc k)) · minor z zero M z₁ k ·
            det (minor z₁ k (minor z zero M)))))
      (ind>anti
        (λ i j →
            MF (toℕ (suc j) +ℕ toℕ (suc k)) · M (suc j) (suc k) ·
            (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M))))
        (λ z z₁ →
            MF (toℕ z +ℕ zero) · M z zero ·
            (MF (toℕ (suc z₁) +ℕ toℕ (suc k)) · minor z zero M z₁ k ·
             det (minor z₁ k (minor z zero M))))
        (λ i j le →
          (MF (toℕ (suc j) +ℕ toℕ (suc k)) · M (suc j) (suc k) ·
          (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨ cong
             (λ a →
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · a ·
                 (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M)))))
             (sym
               (minorSucSuc i zero j k M (weakenFinLe i j le) z≤))
           ⟩
          (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
          (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨
            cong
            (λ a → (a · minor i zero M j k ·
                  (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M)))))
            (sumMF (toℕ (suc j))  (toℕ (suc k)))
           ⟩
          (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
          (MF (toℕ i +ℕ zero) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨
            cong
            (λ a → (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
                    (a · M i zero · det (minor j k (minor i zero M)))))
            (sumMF (toℕ i) zero)
           ⟩
          (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · MF zero · M i zero ·
             det (minor j k (minor i zero M))))
          ≡⟨ ·Assoc
             (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k)
             (MF (toℕ i) · MF zero · M i zero)
             (det (minor j k (minor i zero M))) ⟩
          (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · MF zero · M i zero)
            · det (minor j k (minor i zero M)))
          ≡⟨
            cong
            (λ a → a
            · det (minor j k (minor i zero M)))
            (solve! P')
           ⟩
           (MF (toℕ i) · MF zero · M i zero) ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k)
            · det (minor j k (minor i zero M))
          ≡⟨
            sym
            (·Assoc
              (MF (toℕ i) · MF zero · M i zero)
              (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k)
              (det (minor j k (minor i zero M))))
           ⟩
          MF (toℕ i) · MF zero · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M)))
          ≡⟨
            cong
            (λ a → (a · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M)))))
            (sym (sumMF (toℕ i) zero))
           ⟩
            (MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))
          ≡⟨
             cong
             (λ a → (MF (toℕ i +ℕ zero) · M i zero ·
              (a · minor i zero M j k · det (minor j k (minor i zero M)))))
             (sym (sumMF (toℕ (suc j)) (toℕ (suc k))))
           ⟩
          (MF (toℕ i +ℕ zero) · M i zero ·
          (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k · det (minor j k (minor i zero M))))

        ∎)
      )

  DetColumnAux2b : {n : ℕ} → (k : Fin (suc n)) → (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · M (weakenFin j) (suc k) ·
             (MF (toℕ i +ℕ one) · M i zero ·
              det (minor j k (minor i zero M))))))
   ≡
   ∑
     (λ i →
        ∑
        (λ j →
           ind> (toℕ i) (toℕ j) ·
           (MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))))
  DetColumnAux2b k M =
    ∑∑Compat
    (λ i j → ind> (toℕ i) (toℕ j) ·
            (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · M (weakenFin j) (suc k) ·
             (MF (toℕ i +ℕ one) · M i zero ·
              det (minor j k (minor i zero M)))))
    (λ z z₁ →
        ind> (toℕ z) (toℕ z₁) ·
        (MF (toℕ z +ℕ zero) · M z zero ·
         (MF (toℕ (suc z₁) +ℕ toℕ (suc k)) · minor z zero M z₁ k ·
          det (minor z₁ k (minor z zero M)))))
    (λ i j →
      ind>prop
        (λ i j → (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · M (weakenFin j) (suc k) ·
             (MF (toℕ i +ℕ one) · M i zero ·
              det (minor j k (minor i zero M)))))
        (λ z z₁ →
            MF (toℕ z +ℕ zero) · M z zero ·
            (MF (toℕ (suc z₁) +ℕ toℕ (suc k)) · minor z zero M z₁ k ·
             det (minor z₁ k (minor z zero M))))
        (λ i j le →
          (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · M (weakenFin j) (suc k) ·
          (MF (toℕ i +ℕ one) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨
            cong
            (λ a →
              (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · a ·
              (MF (toℕ i +ℕ one) · M i zero · det (minor j k (minor i zero M)))))
            (sym (minorIdSuc i zero j k M le z≤))
           ⟩
          (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i +ℕ one) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨
            cong
            (λ a → a · minor i zero M j k ·
            (MF (toℕ i +ℕ one) · M i zero · det (minor j k (minor i zero M))))
            (sumMF (toℕ (weakenFin j)) (toℕ (suc k)))
           ⟩
          (MF (toℕ (weakenFin j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i +ℕ one) · M i zero · det (minor j k (minor i zero M))))
          ≡⟨
            cong
            (λ a → MF (toℕ (weakenFin j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (a · M i zero · det (minor j k (minor i zero M))))
            (sumMF (toℕ i) one)
           ⟩
          (MF (toℕ (weakenFin j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · MF one · M i zero · det (minor j k (minor i zero M))))
          ≡⟨ cong
            (λ a → (MF (a) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · MF one · M i zero · det (minor j k (minor i zero M)))))
            (toℕweakenFin j) ⟩
           (MF (toℕ j) · MF (toℕ (suc k)) · minor i zero M j k ·
           (MF (toℕ i) · MF one · M i zero · det (minor j k (minor i zero M))))
          ≡⟨ ·Assoc
             (MF (toℕ j) · MF (toℕ (suc k)) · minor i zero M j k)
             (MF (toℕ i) · MF one · M i zero)
             (det (minor j k (minor i zero M))) ⟩
          (MF (toℕ j) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · MF one · M i zero)
            · det (minor j k (minor i zero M)))
          ≡⟨ cong
            (λ a  → a · det (minor j k (minor i zero M)))
            (solve! P') ⟩
           (MF one · MF (toℕ j) ·  MF (toℕ (suc k)) · minor i zero M j k ·
           (MF (toℕ i) ·  M i zero)
           · det (minor j k (minor i zero M)))
          ≡⟨
            cong
            (λ a → a · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) ·  M i zero)
            · det (minor j k (minor i zero M)))
            (sym (sumMF one (toℕ j)))
           ⟩
          (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
            (MF (toℕ i) · M i zero)
            · det (minor j k (minor i zero M)))
          ≡⟨
            cong
            (λ a → a ·  det (minor j k (minor i zero M)))
            (solve! P')
           ⟩
          (MF (toℕ i) · M i zero)
          · MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
           det (minor j k (minor i zero M))
          ≡⟨
            cong
            (λ a → ( a · M i zero)
          · MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
           det (minor j k (minor i zero M)))
            (solve! P') ⟩
          (MF (toℕ i) · MF zero · M i zero)
          · MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
           det (minor j k (minor i zero M))
          ≡⟨
            cong
            (λ a → a · det (minor j k (minor i zero M)))
            (solve! P')
           ⟩
          MF (toℕ i) · MF zero · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k)
            · det (minor j k (minor i zero M))
          ≡⟨ sym
            (·Assoc
            (MF (toℕ i) · MF zero · M i zero)
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k)
            (det (minor j k (minor i zero M)))) ⟩
           MF (toℕ i) · MF zero · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M)))
          ≡⟨
            cong
            (λ a → (a · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M)))))
            (sym (sumMF (toℕ i) zero))
           ⟩
            (MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j)) · MF (toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))
          ≡⟨
             cong
             (λ a → (MF (toℕ i +ℕ zero) · M i zero ·
              (a · minor i zero M j k · det (minor j k (minor i zero M)))))
             (sym (sumMF (toℕ (suc j)) (toℕ (suc k))))
           ⟩
          (MF (toℕ i +ℕ zero) · M i zero ·
          (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k · det (minor j k (minor i zero M))))
          ∎)
        i
        j)

  -- The determinant expanded along a column is independent of the chosen column.
  DetColumnZero : ∀ {n} → (k : Fin (suc n)) → (M : FinMatrix R (suc n) (suc n)) →
    detC k M ≡ detC zero M
  DetColumnZero {zero} zero M = refl
  DetColumnZero {suc n} zero M = refl
  DetColumnZero {suc n} (suc k) M =
    detC (suc k) M
    ≡⟨ refl ⟩
    ∑
      (λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) · det (minor i (suc k) M))
    ≡⟨ ∑Compat
       (λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) · det (minor i (suc k) M))
       (λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) · detC zero (minor i (suc k) M))
       (λ i → cong
              (λ a → MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) · a)
              (sym (DetRowColumn (minor i (suc k) M))))
     ⟩
    ∑
      (λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) · detC zero (minor i (suc k) M))
    ≡⟨ refl ⟩
    ∑
      (λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
         ∑
         (λ j →
            MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
            det (minor j zero (minor i (suc k) M))))
    ≡⟨ ∑Compat
       ((λ i →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
         ∑
         (λ j →
            MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
            det (minor j zero (minor i (suc k) M)))))
       (λ i → ∑
         (λ j →
         MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
            (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
            det (minor j zero (minor i (suc k) M)))))
       (λ i →
         ∑DistR ( MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k))
         (λ j →
            (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
            det (minor j zero (minor i (suc k) M)))))
     ⟩
    ∑
     (λ i →
       ∑
       (λ j →
          MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
          (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
          det (minor j zero (minor i (suc k) M)))))
    ≡⟨
      ∑∑Compat
      (λ i j →
          MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
          (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
          det (minor j zero (minor i (suc k) M))))
      (λ z z₁ →
          ind> (toℕ z) (toℕ z₁) ·
          (MF (toℕ z +ℕ toℕ (suc k)) · M z (suc k) ·
           (MF (toℕ z₁ +ℕ zero) · minor z (suc k) M z₁ zero ·
            det (minor z₁ zero (minor z (suc k) M))))
          +
          (1r + - ind> (toℕ z) (toℕ z₁)) ·
          (MF (toℕ z +ℕ toℕ (suc k)) · M z (suc k) ·
           (MF (toℕ z₁ +ℕ zero) · minor z (suc k) M z₁ zero ·
            det (minor z₁ zero (minor z (suc k) M)))))
      (λ i j →
        distributeOne
          (ind> (toℕ i) (toℕ j))
          (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
          (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
          det (minor j zero (minor i (suc k) M)))))
     ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M))))
            +
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M))))))
    ≡⟨ ∑∑Split
       (λ i j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M)))))
       (λ i j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M)))))
     ⟩
    (∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M))))))
      +
      ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M)))))))
    ≡⟨
      +Compat
      (∑∑ShiftSuc (λ i j  →
                  MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
                  (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
                  det (minor j zero (minor i (suc k) M)))))
      (∑∑ShiftWeak (λ i j  → MF (toℕ i +ℕ toℕ (suc k)) · M i (suc k) ·
             (MF (toℕ j +ℕ zero) · minor i (suc k) M j zero ·
              det (minor j zero (minor i (suc k) M)))))
     ⟩
    (∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ (suc i)) (toℕ j) ·
            (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (suc i) (suc k) M j zero ·
              det (minor j zero (minor (suc i) (suc k) M))))))
      +
      ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
            (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
             (MF (toℕ j +ℕ zero) · minor (weakenFin i) (suc k) M j zero ·
              det (minor j zero (minor (weakenFin i) (suc k) M)))))))
    ≡⟨ +Compat (DetColumnAux1a k M) (DetColumnAux1b k M) ⟩
    (
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
            (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
             (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
              det (minor i k (minor (weakenFin j) zero M))))))
      +
    ∑
    (λ i →
       ∑
       (λ z →
          ind> (toℕ (suc z)) (toℕ i) ·
          (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
          (MF (toℕ (suc z) +ℕ one) · M (suc z) zero ·
          det (minor i k (minor (suc z) zero M)))))))
    ≡⟨ +Compat
       (∑Comm (λ i j →
                 (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
                  (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
                  (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
                  det (minor i k (minor (weakenFin j) zero M))))))
       (∑Comm (λ i j →
                  ind> (toℕ (suc j)) (toℕ i) ·
                 (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
                 (MF (toℕ (suc j) +ℕ one) · M (suc j) zero ·
                   det (minor i k (minor (suc j) zero M))))))
     ⟩
      ∑
        (λ j →
           ∑
           (λ i →
              (1r + - ind> (toℕ (weakenFin j)) (toℕ i)) ·
              (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
               (MF (toℕ (weakenFin j) +ℕ zero) · M (weakenFin j) zero ·
                det (minor i k (minor (weakenFin j) zero M))))))
      +
      ∑
        (λ j →
           ∑
           (λ i →
              ind> (toℕ (suc j)) (toℕ i) ·
              (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
               (MF (toℕ (suc j) +ℕ one) · M (suc j) zero ·
                det (minor i k (minor (suc j) zero M))))))
    ≡⟨ +Compat
      (sym (∑∑ShiftWeak (λ j i → (MF (toℕ (suc i) +ℕ toℕ (suc k)) · M (suc i) (suc k) ·
                  (MF (toℕ j +ℕ zero) · M j zero ·
                  det (minor i k (minor j zero M)))))))
      (sym (∑∑ShiftSuc (λ j i → (MF (toℕ (weakenFin i) +ℕ toℕ (suc k)) · M (weakenFin i) (suc k) ·
               (MF (toℕ j +ℕ one) · M j zero ·
                det (minor i k (minor j zero M)))))))
    ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · M (suc j) (suc k) ·
             (MF (toℕ i +ℕ zero) · M i zero ·
              det (minor j k (minor i zero M))))))
    +
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ (weakenFin j) +ℕ toℕ (suc k)) · M (weakenFin j) (suc k) ·
             (MF (toℕ i +ℕ one) · M i zero ·
              det (minor j k (minor i zero M))))))
    ≡⟨ +Compat (DetColumnAux2a k M) (DetColumnAux2b k M) ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))
      +
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))
    ≡⟨ +Comm ( ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))) (∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))) ⟩
    (∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M))))))
      +
      ∑
      (λ i →
         ∑
         (λ j →
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M)))))))
    ≡⟨ sym (∑∑Split
      (λ i j →
              ind> (toℕ i) (toℕ j) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M)))))
      (λ i j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (MF (toℕ i +ℕ zero) · M i zero ·
               (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))
      ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M))))
            +
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M))))))
    ≡⟨ ∑∑Compat
       (λ i j →
            ind> (toℕ i) (toℕ j) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M))))
            +
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M)))))
       (λ i j →
            (MF (toℕ i +ℕ zero) · M i zero ·
             (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
              det (minor j k (minor i zero M)))))
       (λ i j → sym
                (distributeOne ( ind> (toℕ i) (toℕ j) )
                ((MF (toℕ i +ℕ zero) · M i zero ·
                (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
                det (minor j k (minor i zero M))))))) ⟩
    ∑
      (λ i →
         ∑
         (λ j →
            MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M)))))
    ≡⟨ ∑Compat
      ((λ i →
         ∑
         (λ j →
            MF (toℕ i +ℕ zero) · M i zero ·
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))))
      ((λ i →
        MF (toℕ i +ℕ zero) · M i zero ·
         ∑
         (λ j →
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))))
      (λ i →
        sym
        (∑DistR
        (MF (toℕ i +ℕ zero) · M i zero)
        (λ j →
            (MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
             det (minor j k (minor i zero M))))))
      ⟩
    ∑
      (λ i →
         MF (toℕ i +ℕ zero) · M i zero ·
         ∑
         (λ j →
            MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
            det (minor j k (minor i zero M))))
    ≡⟨ ∑Compat
       (λ i →
         MF (toℕ i +ℕ zero) · M i zero ·
         ∑
         (λ j →
            MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
            det (minor j k (minor i zero M))))
       (λ i →
         MF (toℕ i +ℕ zero) · M i zero ·
         ∑
         (λ j →
            MF (toℕ j +ℕ toℕ k) · minor i zero M j k ·
            det (minor j k (minor i zero M))))
       (λ i →
         cong
         (λ a → MF (toℕ i +ℕ zero) · M i zero · a)
         (∑Compat
           (λ j →
            MF (toℕ (suc j) +ℕ toℕ (suc k)) · minor i zero M j k ·
            det (minor j k (minor i zero M)))
           (λ j →
            MF (toℕ j +ℕ toℕ k) · minor i zero M j k ·
            det (minor j k (minor i zero M)))
            (λ j  →
              cong
              (λ a → a · minor i zero M j k ·
                 det (minor j k (minor i zero M)))
              (MFsucsuc j k) )
         ))⟩
     ∑
       (λ i →
          MF (toℕ i +ℕ zero) · M i zero ·
          ∑
          (λ j →
             MF (toℕ j +ℕ toℕ k) · minor i zero M j k ·
             det (minor j k (minor i zero M))))
    ≡⟨ refl ⟩
     ∑
      (λ i →
         MF (toℕ i +ℕ zero) · M i zero ·
         detC k (minor i zero M))
    ≡⟨ ∑Compat
       (λ i → MF (toℕ i +ℕ zero) · M i zero ·
         detC k (minor i zero M))
       (λ i → MF (toℕ i +ℕ zero) · M i zero ·
         detC zero (minor i zero M))
       (λ i → cong
              (λ a → MF (toℕ i +ℕ zero) · M i zero · a)
              (DetColumnZero k (minor i zero M))) ⟩
    ∑
      (λ i → MF (toℕ i +ℕ zero) · M i zero · detC zero (minor i zero M))
        ≡⟨ ∑Compat
       (λ i → MF (toℕ i +ℕ zero) · M i zero ·
         detC zero (minor i zero M))
       (λ i → MF (toℕ i +ℕ zero) · M i zero ·
         det (minor i zero M))
       (λ i → cong
              (λ a → MF (toℕ i +ℕ zero) · M i zero · a)
              (DetRowColumn (minor i zero M))) ⟩
    ∑ (λ i → MF (toℕ i +ℕ zero) · M i zero · det (minor i zero M))
    ≡⟨ refl ⟩
    detC zero M
    ∎

  -- The determinant expanded along a column is the regular determinant.
  DetColumn : ∀ {n} → (k : Fin (suc n)) → (M : FinMatrix R (suc n) (suc n)) →
    detC k M ≡ det M
  DetColumn k M =
   detC k M
   ≡⟨ DetColumnZero k M ⟩
   detC zero M
   ≡⟨ DetRowColumn M ⟩
   det M
   ∎

  open Coefficient (P')

  δ = KroneckerDelta.δ R'

  ∑Mul1r = Sum.∑Mul1r (CommRing→Ring P')
  ∑Mulr1 = Sum.∑Mulr1 (CommRing→Ring P')

  -- The determinant of the zero matrix is 0.
  detZero : {n : ℕ} → det {suc n} 𝟘 ≡ 0r
  detZero {n} =
    ∑Zero
      (λ i → MF (toℕ i) · 0r · det {n} (minor zero i 𝟘))
      (λ i →
       (MF (toℕ i) · 0r · det {n} (minor zero i 𝟘))
       ≡⟨
        cong
        (λ a → a · det {n} (minor zero i 𝟘))
        (solve! P')⟩
        0r · det (minor zero i 𝟘)
        ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring P') (det (minor zero i 𝟘)) ⟩
        0r
        ∎
        )

  --The determinant of the identity matrix is 1.
  detOne : {n : ℕ} → det {n} 𝟙 ≡ 1r
  detOne {zero} = refl
  detOne {suc n} =
    ∑ (λ i → MF (toℕ i) · 𝟙 (zero {n}) i · det {n} (minor zero i 𝟙))
    ≡⟨ refl ⟩
    ∑ (λ i → MF (toℕ i) · δ (zero {n}) i · det {n} (minor zero i 𝟙))
    ≡⟨ ∑Compat
      (λ i → MF (toℕ i) · δ (zero {n}) i · det {n} (minor zero i 𝟙))
      (λ i → δ (zero {n}) i · MF (toℕ i) · det {n} (minor zero i 𝟙))
      (λ i →
         cong
         (λ a → a · det {n} (minor zero i 𝟙))
         (solve! P'))
     ⟩
    ∑ (λ i → δ (zero {n}) i · MF (toℕ i) · det (minor zero i 𝟙))
    ≡⟨ ∑Compat
      (λ i → δ (zero {n}) i · MF (toℕ i) · det (minor zero i 𝟙))
      (λ i → δ (zero {n}) i · (MF (toℕ i) · det (minor zero i 𝟙)))
      (λ i → sym (·Assoc _ _ _)) ⟩
    ∑ (λ i → δ (zero {n}) i · (MF (toℕ i) · det (minor zero i 𝟙)))
    ≡⟨ ∑Mul1r
      (suc n)
      (λ i → (MF (toℕ i) · det {n} (minor zero i 𝟙)))
      zero ⟩
    MF zero · det {n} (minor zero zero 𝟙)
    ≡⟨ refl ⟩
    (1r · det {n} 𝟙)
    ≡⟨ ·IdL (det {n} 𝟙) ⟩
    det {n}  𝟙
    ≡⟨ detOne{n} ⟩
    1r
    ∎

  --The determinant remains unchanged under transposition.
  detTransp : {n : ℕ} → (M : FinMatrix R n n) → det M ≡ det (M ᵗ)
  detTransp {zero} M = refl
  detTransp {suc n} M =
    det M
    ≡⟨ refl ⟩
    ∑ (λ i → MF (toℕ i) · (M ᵗ) i zero · det ((minor i zero (M ᵗ))ᵗ))
    ≡⟨
      ∑Compat
      (λ i → MF (toℕ i) · (M ᵗ) i zero · det ((minor i zero (M ᵗ))ᵗ))
      (λ i → MF (toℕ i) · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
      (λ i →
        cong
        (λ a →  MF (toℕ i) · (M ᵗ) i zero · a)
        (sym (detTransp (minor i zero (M ᵗ)))))
     ⟩
    ∑ (λ i → MF (toℕ i) · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
    ≡⟨ ∑Compat
      (λ i → MF (toℕ i) · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
      (λ i → MF (toℕ i +ℕ zero) · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
      (λ i →
        cong
        (λ a →
         a · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
        (sym (MFplusZero i))) ⟩
    ∑ (λ i → MF (toℕ i +ℕ zero) · (M ᵗ) i zero · det (minor i zero (M ᵗ)))
    ≡⟨ (DetRowColumn ((M ᵗ))) ⟩
    det (M ᵗ)
    ∎
