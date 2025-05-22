{-# OPTIONS --safe #-}

module Cubical.Algebra.Determinat.Adjugate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order using (_<'Fin_; _≤'Fin_)
open import Cubical.Data.Int.Base using (pos; negsuc)
open import Cubical.Data.Vec.Base using (_∷_; [])
open import Cubical.Data.Nat.Order

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Semiring

open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.Determinat.Minor
open import Cubical.Algebra.Determinat.RingSum
open import Cubical.Algebra.Determinat.Base

module Adjugate (ℓ : Level) (P' : CommRing ℓ) where
  open Cubical.Algebra.Determinat.Minor.Minor ℓ
  open Cubical.Algebra.Determinat.RingSum.RingSum ℓ P'
  open RingStr (snd (CommRing→Ring P'))
  open Cubical.Algebra.Determinat.Base.Determinat ℓ P'
  open Coefficient (P')

  private variable
    n m : ℕ

  -- Scalar multiplication
  _∘_ : R → FinMatrix R n m → FinMatrix R n m
  (a ∘ M) i j = a · (M i j)

  opaque
    -- Properties of ==
    ==Refl : (k : Fin n) → k == k ≡ true
    ==Refl {n} zero = refl
    ==Refl {suc n} (suc k) = ==Refl {n} k

    ==Sym : (k l : Fin n) → k == l ≡ l == k
    ==Sym {suc n} zero zero = refl
    ==Sym {suc n} zero (suc l) = refl
    ==Sym {suc n} (suc k) zero = refl
    ==Sym {suc n} (suc k) (suc l) = ==Sym {n} k l

    -- Properties of the Kronecker Delta
    deltaProp : (k l : Fin n) → toℕ k <' toℕ l → δ k l ≡ 0r
    deltaProp {suc n} zero (suc l) (s≤s le) = refl
    deltaProp {suc n} (suc k) (suc l) (s≤s le) =  deltaProp {n} k l le

    deltaPropSym : (k l : Fin n) → toℕ l <' toℕ k → δ k l ≡ 0r
    deltaPropSym {suc n} (suc k) (zero) (s≤s le) = refl
    deltaPropSym {suc n} (suc k) (suc l) (s≤s le) =  deltaPropSym {n} k l le

    deltaPropEq : (k l : Fin n) → k ≡ l → δ k l ≡ 1r
    deltaPropEq k l e =
      δ k l
      ≡⟨ cong (λ a → δ a l) e ⟩
      δ l l
      ≡⟨ cong (λ a → if a then 1r else 0r) (==Refl l) ⟩
      1r
      ∎

    deltaComm : (k l : Fin n) → δ k l ≡ δ l k
    deltaComm k l = cong (λ a → if a then 1r else 0r) (==Sym k l)

  -- Definition of the cofactor matrix
  cof : FinMatrix R n n → FinMatrix R n n
  cof {suc n} M i j = (MF (toℕ i +ℕ toℕ j)) ·  det {n} (minor i j M)

  opaque
    -- Behavior of the cofactor matrix under transposition
    cofTransp : (M : FinMatrix R n n) → (i j : Fin n) → cof (M ᵗ) i j ≡ cof M j i
    cofTransp {suc n} M i j =
      MF (toℕ i +ℕ toℕ j) ·  det (minor i j (M ᵗ))
      ≡⟨ cong (λ a → MF (toℕ i +ℕ toℕ j) · a) (detTransp ((minor j i M ᵗ))) ⟩
      (MF (toℕ i +ℕ toℕ j) · det (minor j i M))
      ≡⟨
        cong
        (λ a → MF (a) · det (minor j i M)) (+ℕ-comm (toℕ i) (toℕ j)) ⟩
      (MF (toℕ j +ℕ toℕ i) · det (minor j i M))
      ∎

  -- Definition of the adjugate matrix
  adjugate : FinMatrix R n n → FinMatrix R n n
  adjugate M i j = cof M j i

  opaque
    -- Behavior of the adjugate matrix under transposition
    adjugateTransp : (M : FinMatrix R n n) → (i j : Fin n) → adjugate (M ᵗ) i j ≡ adjugate M j i
    adjugateTransp M i j = cofTransp M j i

    -- Properties of WeakenFin
    weakenPredFinLt : (k l : Fin (suc (suc n))) → toℕ k <' toℕ l → k ≤'Fin weakenFin (predFin l)
    weakenPredFinLt {zero} zero one (s≤s z≤) = z≤
    weakenPredFinLt {zero} one one (s≤s ())
    weakenPredFinLt {zero} one (suc (suc ())) (s≤s le)
    weakenPredFinLt {suc n} zero one (s≤s z≤) = z≤
    weakenPredFinLt {suc n} zero (suc (suc l)) (s≤s le) = z≤
    weakenPredFinLt {suc n} (suc k) (suc (suc l)) (s≤s (s≤s le)) = s≤s ( weakenPredFinLt {n} k (suc l) (s≤s le))

    sucPredFin : (k l : Fin (suc (suc n))) → toℕ k <' toℕ l → suc (predFin l) ≡ l
    sucPredFin {zero} zero one le = refl
    sucPredFin {zero} (suc k) (suc l) le = refl
    sucPredFin {suc n} zero (suc l) le = refl
    sucPredFin {suc n} (suc k) (suc l) (s≤s le) = refl


    adjugatePropAux1a : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) → toℕ k <' toℕ l →
     ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))))
      ≡
      ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ z) · M l (weakenFin z))
               · det (minor (predFin l) z (minor k i M)))))
    adjugatePropAux1a M k l le =
      ∑∑Compat
      (λ i j →
             ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M)))))
      (λ z z₁ →
          ind> (toℕ z) (toℕ z₁) ·
          (M l z · MF (toℕ k +ℕ toℕ z) ·
           (MF (toℕ (predFin l) +ℕ toℕ z₁) · M l (weakenFin z₁))
           · det (minor (predFin l) z₁ (minor k z M))))
        (ind>prop
        (λ z z₁ →
            M l z · MF (toℕ k +ℕ toℕ z) ·
            (MF (toℕ (predFin l) +ℕ toℕ z₁) · minor k z M (predFin l) z₁ ·
             det (minor (predFin l) z₁ (minor k z M))))
        (λ z z₁ →
            M l z · MF (toℕ k +ℕ toℕ z) ·
            (MF (toℕ (predFin l) +ℕ toℕ z₁) · M l (weakenFin z₁))
            · det (minor (predFin l) z₁ (minor k z M)))
        (λ i j lf →
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
             det (minor (predFin l) j (minor k i M))))
          ≡⟨
            cong
            (λ a → M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · a  ·
             det (minor (predFin l) j (minor k i M))))
            (minorSucId
              k
              i
              (predFin l)
              j
              M
              (weakenPredFinLt k l le)
              lf)
           ⟩
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M (suc (predFin l)) (weakenFin j)
             · det (minor (predFin l) j (minor k i M))))
          ≡⟨ ·Assoc _ _ _ ⟩
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M (suc (predFin l)) (weakenFin j))
            · det (minor (predFin l) j (minor k i M)))
          ≡⟨ cong
            (λ a → (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M a (weakenFin j))
            · det (minor (predFin l) j (minor k i M))))
            (sucPredFin
              k
              l
              le
            )
           ⟩
           (M l i · MF (toℕ k +ℕ toℕ i) ·
             (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
             · det (minor (predFin l) j (minor k i M)))
          ∎
          )
        )

    adjugatePropAux1b : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) → toℕ k <' toℕ l →
      ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ  i) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M))))))
     ≡
     ∑
       (λ i →
          ∑
          (λ z →
             (1r + - ind> (toℕ i) (toℕ z)) ·
             (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z))) · M l (suc z) ·
               det (minor (predFin l) i (minor k (suc z) M))))))

    adjugatePropAux1b M k l le =
      ∑∑Compat
        (λ i j →
              (1r + - ind> (toℕ  i) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M)))))
        (λ z z₁ →
            (1r + - ind> (toℕ z) (toℕ z₁)) ·
            (M l (weakenFin z) · MF (toℕ k +ℕ toℕ (weakenFin z)) ·
             (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z₁))) · M l (suc z₁) ·
              det (minor (predFin l) z (minor k (suc z₁) M)))))
        λ i j →
          ind>anti
          (λ i j → (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M)))))
          (λ z z₁ →
              M l (weakenFin z) · MF (toℕ k +ℕ toℕ (weakenFin z)) ·
              (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z₁))) · M l (suc z₁) ·
               det (minor (predFin l) z (minor k (suc z₁) M))))
          (λ i j lf →
            (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) ·
               minor k (weakenFin i) M (predFin l) j
               · det (minor (predFin l) j (minor k (weakenFin i) M))))
            ≡⟨
              cong
              (λ a → M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) ·  a
               · det (minor (predFin l) j (minor k (weakenFin i) M))))
              (minorSucSuc
                k (weakenFin i) (predFin l) j M (weakenPredFinLt k l le) (weakenweakenFinLe i j lf))
             ⟩
             M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
             (MF (toℕ (predFin l) +ℕ toℕ j) · M (suc (predFin l)) (suc j) ·
             det (minor (predFin l) j (minor k (weakenFin i) M)))
            ≡⟨
              cong
              (λ a →
                 M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
             (MF (toℕ (predFin l) +ℕ toℕ j) · M (a) (suc j) ·
             det (minor (predFin l) j (minor k (weakenFin i) M))))
              (sucPredFin k l le)
             ⟩
            M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · M l (suc j) ·
               det (minor (predFin l) j (minor k (weakenFin i) M)))
            ≡⟨
              cong
              (λ a →  M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · M l (suc j) · a))
              (detComp
                (minor (predFin l) j (minor k (weakenFin i) M))
                (minor (predFin l) i (minor k (suc j) M))
                (λ i₁ j₁ →
                  (sym (minorSemiCommR k (predFin l) j i i₁ j₁ M lf))))
              ⟩
            M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · M l (suc j) ·
               det (minor (predFin l) i (minor k (suc j) M)))
            ≡⟨ cong
               (λ a →
                 M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
                   (a · M l (suc j) ·
                   det (minor (predFin l) i (minor k (suc j) M))))
               (sumMF (toℕ (predFin l)) (toℕ j))
             ⟩
            (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l)) · MF (toℕ j) · M l (suc j) ·
               det (minor (predFin l) i (minor k (suc j) M))))
            ≡⟨
              cong
              (λ a → (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l)) · a · M l (suc j) ·
               det (minor (predFin l) i (minor k (suc j) M)))))
              (sucMFRev (toℕ j))
             ⟩
            (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
              (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc j))) · M l (suc j) ·
               det (minor (predFin l) i (minor k (suc j) M))))
            ∎)
          i
          j

    adjugatePropAux2a : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) →
      toℕ k <' toℕ l →
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
               · det (minor (predFin l) j (minor k i M)))))
     ≡
     ∑
       (λ i →
          ∑
          (λ z →
             1r ·
             (ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (predFin l) z (minor k i M)))))))
    adjugatePropAux2a M k l le =
      ∑∑Compat
       (λ i j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
               · det (minor (predFin l) j (minor k i M))))
       (λ z z₁ →
           1r ·
           (ind> (toℕ z) (toℕ z₁) ·
            (M l z · (MF (toℕ k) · MF (toℕ z)) ·
             (MF (toℕ (predFin l)) · MF (toℕ z₁) · M l (weakenFin z₁) ·
              det (minor (predFin l) z₁ (minor k z M))))))
       (λ i j →
         (ind> (toℕ i) (toℕ j) ·
           (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
            · det (minor (predFin l) j (minor k i M))))
         ≡⟨
           cong
           (λ a → (ind> (toℕ i) (toℕ j) ·
           (M l i · a ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
            · det (minor (predFin l) j (minor k i M)))))
           (sumMF (toℕ k) (toℕ i)) ⟩
         (ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
            · det (minor (predFin l) j (minor k i M))))
         ≡⟨
           cong
           (λ a → (ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (a · M l (weakenFin j))
            · det (minor (predFin l) j (minor k i M)))))
           (sumMF (toℕ (predFin l)) (toℕ j))
          ⟩
         (ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j))
            · det (minor (predFin l) j (minor k i M))))
         ≡⟨ cong
           (λ a → (ind> (toℕ i) (toℕ j) · a))
           (sym (·Assoc _ _ _))
           ⟩
         ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
             det (minor (predFin l) j (minor k i M))))
         ≡⟨ sym (·IdL _) ⟩
         (1r · (ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
             det (minor (predFin l) j (minor k i M))))))
         ∎ )

    adjugatePropAux2b : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) →
      toℕ k <' toℕ l →
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) · MF (toℕ k +ℕ toℕ (weakenFin j)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (predFin l) j (minor k i M))))))
     ≡
     ∑
       (λ i →
          ∑
          (λ z →
             - 1r ·
             (ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (predFin l) z (minor k i M)))))))
    adjugatePropAux2b M k l le =
      ∑∑Compat
      (λ i j →
              ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) · MF (toℕ k +ℕ toℕ (weakenFin j)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (predFin l) j (minor k i M)))))
      (λ z z₁ →
          - 1r ·
          (ind> (toℕ z) (toℕ z₁) ·
           (M l z · (MF (toℕ k) · MF (toℕ z)) ·
            (MF (toℕ (predFin l)) · MF (toℕ z₁) · M l (weakenFin z₁) ·
             det (minor (predFin l) z₁ (minor k z M))))))
      (λ i j →
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · MF (toℕ k +ℕ toℕ (weakenFin j)) ·
           (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (predFin l) j (minor k i M)))))
        ≡⟨
          cong
          (λ a →
            (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · a ·
           (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (predFin l) j (minor k i M))))))
          (sumMF (toℕ k) (toℕ (weakenFin j)))
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ (weakenFin j))) ·
           (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (predFin l) j (minor k i M)))))
        ≡⟨
          cong
          (λ a →
            (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF a) ·
           (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (predFin l) j (minor k i M))))))
          (weakenRespToℕ j) ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ j)) ·
           (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (predFin l) j (minor k i M)))))
        ≡⟨
         cong
         (λ a → ind> (toℕ i) (toℕ j) · a)
         (sym (·Assoc _ _ _))
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) ·
           (MF (toℕ k) · MF (toℕ j) ·
            (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
             det (minor (predFin l) j (minor k i M))))))
        ≡⟨
          cong
          (λ a →
            ind> (toℕ i) (toℕ j) ·
               (M l (weakenFin j) · a))
          (sym (·Assoc _ _ _))
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) ·
           (MF (toℕ k) ·
            (MF (toℕ j) ·
             (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
              det (minor (predFin l) j (minor k i M)))))))
        ≡⟨
          cong
          (λ a →
            (ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) ·
                (MF (toℕ k) · a))))
          (·Assoc _ _ _)
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) ·
           (MF (toℕ k) ·
            (MF (toℕ j) · (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i)
             · det (minor (predFin l) j (minor k i M))))))
        ≡⟨
          cong
          (λ a → ind> (toℕ i) (toℕ j) ·
                     (M l (weakenFin j) · a))
          (·Assoc _ _ _)
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) ·
           (MF (toℕ k) ·
            (MF (toℕ j) · (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i))
            · det (minor (predFin l) j (minor k i M)))))
        ≡⟨ cong
           (λ a → ind> (toℕ i) (toℕ j) · a)
           (·Assoc _ _ _)
          ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) ·
           (MF (toℕ k) ·
            (MF (toℕ j) ·
             (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i)))
           · det (minor (predFin l) j (minor k i M))))
        ≡⟨
          cong
          (λ a → ind> (toℕ i) (toℕ j) · (a  · det (minor (predFin l) j (minor k i M))))
          (solve! P')
         ⟩
        ind> (toℕ i) (toℕ j) ·
          (- 1r · M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j))
           · det (minor (predFin l) j (minor k i M)))
        ≡⟨ ·Assoc _ _ _ ⟩
        (ind> (toℕ i) (toℕ j) ·
          (- 1r · M l i · (MF (toℕ k) · MF (toℕ i)) ·
           (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j)))
          · det (minor (predFin l) j (minor k i M)))
        ≡⟨
          cong
          (λ a → a · det (minor (predFin l) j (minor k i M)))
          (·Assoc _ _ _)
         ⟩
        (ind> (toℕ i) (toℕ j) · (- 1r · M l i · (MF (toℕ k) · MF (toℕ i))) ·
          (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j))
          · det (minor (predFin l) j (minor k i M)))
        ≡⟨ cong
          (λ a → a · (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j))
          · det (minor (predFin l) j (minor k i M)))
          (solve! P')
         ⟩
        (- 1r) · ind> (toℕ i) (toℕ j) · (M l i · (MF (toℕ k) · MF (toℕ i))) ·
          (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j))
          · det (minor (predFin l) j (minor k i M))
        ≡⟨ sym (·Assoc _ _ _) ⟩
        - 1r · ind> (toℕ i) (toℕ j) · (M l i · (MF (toℕ k) · MF (toℕ i))) ·
          (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
           det (minor (predFin l) j (minor k i M)))
        ≡⟨ sym (·Assoc _ _ _) ⟩
        (- 1r · ind> (toℕ i) (toℕ j) ·
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
           (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
            det (minor (predFin l) j (minor k i M)))))
        ≡⟨  sym (·Assoc _ _ _) ⟩
        - 1r ·
          (ind> (toℕ i) (toℕ j) ·
           (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
             det (minor (predFin l) j (minor k i M)))))
        ∎)

    adjugatePropRG : (M : FinMatrix R (suc n) (suc n)) → (k l : Fin (suc n)) → toℕ k <' toℕ l →
     ∑ (λ i → (M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))) ≡ 0r
    adjugatePropRG {zero} M zero zero ()
    adjugatePropRG {zero} M zero (suc ()) (s≤s le)
    adjugatePropRG {suc n} M k l le =
      ∑ (λ i → M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))
      ≡⟨ ∑Compat
        (λ i → M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))
        (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
        (λ i → ·Assoc _ _ _) ⟩
      ∑ (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
      ≡⟨ ∑Compat
         (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
         (λ i → M l i · MF (toℕ k +ℕ toℕ i) · detR (predFin l) (minor k i M))
         (λ i →
           cong
           (λ a → M l i · MF (toℕ k +ℕ toℕ i) · a)
           (sym (DetRow (predFin l) (minor k i M))))
       ⟩
      ∑
        (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) · detR (predFin l) (minor k i M))
      ≡⟨ refl ⟩
      ∑
        (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) ·
           ∑
           (λ j →
              MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
              det (minor (predFin l) j (minor k i M))))
      ≡⟨ ∑Compat
         (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) ·
           ∑
           (λ j →
              MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
              det (minor (predFin l) j (minor k i M))))
         (λ i →
           ∑
           (λ j →  M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
              det (minor (predFin l) j (minor k i M)))))
         (λ i  →
           ∑DistR
             (M l i · MF (toℕ k +ℕ toℕ i))
             (λ j → MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
              det (minor (predFin l) j (minor k i M))))
       ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
               det (minor (predFin l) j (minor k i M)))))
      ≡⟨ ∑∑Compat
        (λ i j →
              M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
               det (minor (predFin l) j (minor k i M))))
        (λ z z₁ →
            ind> (toℕ z) (toℕ z₁) ·
            (M l z · MF (toℕ k +ℕ toℕ z) ·
             (MF (toℕ (predFin l) +ℕ toℕ z₁) · minor k z M (predFin l) z₁ ·
              det (minor (predFin l) z₁ (minor k z M))))
            +
            (1r + - ind> (toℕ z) (toℕ z₁)) ·
            (M l z · MF (toℕ k +ℕ toℕ z) ·
             (MF (toℕ (predFin l) +ℕ toℕ z₁) · minor k z M (predFin l) z₁ ·
              det (minor (predFin l) z₁ (minor k z M)))))
        (λ i j →
          distributeOne
          (ind> (toℕ i) (toℕ j))
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
             det (minor (predFin l) j (minor k i M))))
        )
       ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))
              +
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))))
      ≡⟨
        ∑∑Split
        (λ i j → ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M)))))
        (λ i j → (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M)))))
       ⟩
      (∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))))
        +
        ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M)))))))
      ≡⟨ +Compat refl (∑∑ShiftWeak λ i j →
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))) ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))))
        +
        ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M))))))
      ≡⟨ +Compat refl
        (∑∑Compat
          (λ i j →
              (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M)))))
          (λ z z₁ →
              (1r + - ind> (toℕ z) (toℕ z₁)) ·
              (M l (weakenFin z) · MF (toℕ k +ℕ toℕ (weakenFin z)) ·
               (MF (toℕ (predFin l) +ℕ toℕ z₁) ·
                minor k (weakenFin z) M (predFin l) z₁
                · det (minor (predFin l) z₁ (minor k (weakenFin z) M)))))
          (λ i j →
            cong
            (λ a →
              (1r + - ind> a (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M)))))
            (weakenRespToℕ i))
          )
       ⟩
      (∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · minor k i M (predFin l) j ·
                det (minor (predFin l) j (minor k i M))))))
        +
        ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) ·
                minor k (weakenFin i) M (predFin l) j
                · det (minor (predFin l) j (minor k (weakenFin i) M)))))))
      ≡⟨ +Compat (adjugatePropAux1a M k l le) (adjugatePropAux1b M k l le) ⟩
      (∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ z) · M l (weakenFin z))
               · det (minor (predFin l) z (minor k i M)))))
        +
        ∑
        (λ i →
           ∑
           (λ z →
              (1r + - ind> (toℕ i) (toℕ z)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z))) · M l (suc z) ·
                det (minor (predFin l) i (minor k (suc z) M)))))))
      ≡⟨ +Compat
        refl
        (∑Comm
          (λ i z →
              (1r + - ind> (toℕ i) (toℕ z)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z))) · M l (suc z) ·
                det (minor (predFin l) i (minor k (suc z) M)))))) ⟩
      (∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ z) · M l (weakenFin z))
               · det (minor (predFin l) z (minor k i M)))))
        +
        ∑
        (λ j →
           ∑
           (λ i →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc j))) · M l (suc j) ·
                det (minor (predFin l) i (minor k (suc j) M)))))))
      ≡⟨ +Compat refl
         (∑∑Compat
           (λ j i →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc j))) · M l (suc j) ·
                det (minor (predFin l) i (minor k (suc j) M)))))
           (λ z z₁ →
               ind> (suc (toℕ z)) (toℕ z₁) ·
               (M l (weakenFin z₁) · MF (toℕ k +ℕ toℕ (weakenFin z₁)) ·
                (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc z))) · M l (suc z) ·
                 det (minor (predFin l) z₁ (minor k (suc z) M)))))
           (λ j i →
             cong
             (λ a → a ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc j))) · M l (suc j) ·
                det (minor (predFin l) i (minor k (suc j) M)))))
             (sym (ind>Suc (toℕ j) (toℕ i)))
             )) ⟩
      (∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ z) · M l (weakenFin z))
               · det (minor (predFin l) z (minor k i M)))))
        +
        ∑
        (λ i →
           ∑
           (λ z →
              ind> (suc (toℕ i)) (toℕ z) ·
              (M l (weakenFin z) · MF (toℕ k +ℕ toℕ (weakenFin z)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ (suc i))) · M l (suc i) ·
                det (minor (predFin l) z (minor k (suc i) M)))))))
      ≡⟨ +Compat refl
        (sym (∑∑ShiftSuc
             (λ i z →
              (M l (weakenFin z) · MF (toℕ k +ℕ toℕ (weakenFin z)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (predFin l) z (minor k i M))))))) ⟩
      (∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (predFin l) +ℕ toℕ j) · M l (weakenFin j))
               · det (minor (predFin l) j (minor k i M)))))
        +
        ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) · MF (toℕ k +ℕ toℕ (weakenFin j)) ·
               (MF (toℕ (predFin l)) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (predFin l) j (minor k i M)))))))
      ≡⟨ +Compat
        (adjugatePropAux2a M k l le)
        (adjugatePropAux2b M k l le) ⟩
      (∑
        (λ i →
           ∑
           (λ z →
              1r ·
              (ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (predFin l) z (minor k i M)))))))
        +
        ∑
        (λ i →
           ∑
           (λ z →
              - 1r ·
              (ind> (toℕ i) (toℕ z) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                 det (minor (predFin l) z (minor k i M))))))))
       ≡⟨ sym
         (∑∑Split
         (λ i z →
              1r ·
              (ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (predFin l) z (minor k i M))))))
         λ i z →
              - 1r ·
              (ind> (toℕ i) (toℕ z) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ z) · M l (weakenFin z) ·
                 det (minor (predFin l) z (minor k i M))))))
       ⟩
       ∑
         (λ i →
            ∑
            (λ j →
               1r ·
               (ind> (toℕ i) (toℕ j) ·
                (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                 (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                  det (minor (predFin l) j (minor k i M)))))
               +
               - 1r ·
               (ind> (toℕ i) (toℕ j) ·
                (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                 (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                  det (minor (predFin l) j (minor k i M)))))))
       ≡⟨ ∑∑Compat
          (λ i j →
               1r ·
               (ind> (toℕ i) (toℕ j) ·
                (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                 (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                  det (minor (predFin l) j (minor k i M)))))
               +
               - 1r ·
               (ind> (toℕ i) (toℕ j) ·
                (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                 (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                  det (minor (predFin l) j (minor k i M))))))
          (λ i j → 0r)
          (λ i j →
            (1r ·
              (ind> (toℕ i) (toℕ j) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                 det (minor (predFin l) j (minor k i M)))))
              +
              - 1r ·
              (ind> (toℕ i) (toℕ j) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                 det (minor (predFin l) j (minor k i M))))))
            ≡⟨ sym (·DistL+ 1r (- 1r) (ind> (toℕ i) (toℕ j) ·
                                        (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                                         (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                                          det (minor (predFin l) j (minor k i M)))))) ⟩
            ((1r + - 1r) ·
              (ind> (toℕ i) (toℕ j) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                 det (minor (predFin l) j (minor k i M))))))
            ≡⟨ cong
               (λ a → a · (ind> (toℕ i) (toℕ j) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                 det (minor (predFin l) j (minor k i M))))))
               (+InvR 1r)
             ⟩
            (0r ·
              (ind> (toℕ i) (toℕ j) ·
               (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                 det (minor (predFin l) j (minor k i M))))))
            ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring P') (ind> (toℕ i) (toℕ j) ·
                                                                (M l i · (MF (toℕ k) · MF (toℕ i)) ·
                                                                 (MF (toℕ (predFin l)) · MF (toℕ j) · M l (weakenFin j) ·
                                                                  det (minor (predFin l) j (minor k i M))))) ⟩
            0r
            ∎)
        ⟩
       ∑ (λ (i : Fin (suc (suc n))) → ∑ (λ (j : Fin (suc n)) → 0r))
       ≡⟨ ∑Compat
         (λ (i : Fin (suc (suc n))) → ∑ (λ (j : Fin (suc n)) → 0r))
         (λ (i : Fin (suc (suc n))) → 0r)
         (λ (i : Fin (suc (suc n))) → ∑Zero {suc n} (λ (i : Fin  (suc n)) → 0r) (λ (i : Fin  (suc n)) → refl)) ⟩
       ∑ (λ  (i : Fin (suc (suc n))) → 0r)
       ≡⟨ ∑Zero (λ (i : Fin (suc (suc n))) → 0r) (λ  (i : Fin (suc (suc n))) → refl) ⟩
       0r
       ∎

    adjugateInvRGcomponent : (M : FinMatrix R n n) → (k l : Fin n) → toℕ l <' toℕ k → (M ⋆ adjugate M) k l ≡  (det M ∘ 𝟙) k l
    adjugateInvRGcomponent {suc n} M k l le =
      ∑ (λ i → M k i · (MF(toℕ l +ℕ toℕ i) · det(minor l i M)) )
      ≡⟨ adjugatePropRG M l k le  ⟩
      0r
      ≡⟨ sym (RingTheory.0RightAnnihilates (CommRing→Ring P') (det M)) ⟩
      det M · 0r
      ≡⟨ cong (λ a → det M · a) (sym (deltaPropSym k l le)) ⟩
      (det M ∘ 𝟙) k l
      ∎

  strongenFin : {j : Fin (suc n)} → (i : Fin (suc n)) → toℕ i <' toℕ j → Fin n
  strongenFin {zero} {zero} i ()
  strongenFin {zero} {suc ()} i le
  strongenFin {suc n} {suc j} zero le = zero
  strongenFin {suc n} {suc j} (suc i) (s≤s le) = suc (strongenFin {n} {j} i le)

  opaque
    strongenFinLeId : {j : Fin (suc n)} → (i : Fin (suc n)) → (le : toℕ i <' toℕ j) →
      toℕ (strongenFin i le) <' toℕ j
    strongenFinLeId {zero} {zero} zero ()
    strongenFinLeId {zero} {suc ()} i le
    strongenFinLeId {suc n} {suc j} zero (s≤s z≤) = s≤s z≤
    strongenFinLeId {suc n} {suc j} (suc i) (s≤s le) = s≤s (strongenFinLeId {n} {j} i le)

    weakenStrongenFin : {j : Fin (suc n)} → (i : Fin (suc n)) → (le : toℕ i <' toℕ j) →
      weakenFin (strongenFin i le) ≡ i
    weakenStrongenFin {zero} {zero} i ()
    weakenStrongenFin {zero} {suc ()} zero le
    weakenStrongenFin {suc n} {suc j} zero le = refl
    weakenStrongenFin {suc n} {suc j} (suc i) (s≤s le) =
      cong
      (λ a → suc a)
      (weakenStrongenFin {n} {j} i le)

    toℕstrongenFin : {j : Fin (suc n)} → (i : Fin (suc n)) → (le : toℕ i <' toℕ j) →
     toℕ (strongenFin i le) ≡ toℕ i
    toℕstrongenFin {zero} {zero} i ()
    toℕstrongenFin {zero} {suc ()} i (le)
    toℕstrongenFin {suc n} {suc j} zero le = refl
    toℕstrongenFin {suc n} {suc j} (suc i) (s≤s le) =
      cong (λ a → suc a) (toℕstrongenFin {n} {j} i le)


    adjugatePropAux3a : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) → (le : toℕ l <' toℕ k) →
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))))
      ≡
      ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ l) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (strongenFin l le) z (minor k i M))))))
    adjugatePropAux3a M k l le =
      ∑∑Compat
      (λ i j →
           ind> (toℕ i) (toℕ j) ·
            (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
            minor k i M (strongenFin l le) j
            · det (minor (strongenFin l le) j (minor k i M)))))
      (λ z z₁ →
          ind> (toℕ z) (toℕ z₁) ·
          (M l z · (MF (toℕ k) · MF (toℕ z)) ·
           (MF (toℕ l) · MF (toℕ z₁) · M l (weakenFin z₁) ·
            det (minor (strongenFin l le) z₁ (minor k z M)))))
      (ind>prop
        (λ i j →
            M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
            minor k i M (strongenFin l le) j
            · det (minor (strongenFin l le) j (minor k i M))))
        (λ z z₁ →
            M l z · (MF (toℕ k) · MF (toℕ z)) ·
            (MF (toℕ l) · MF (toℕ z₁) · M l (weakenFin z₁) ·
             det (minor (strongenFin l le) z₁ (minor k z M))))
        (λ i j lf →
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             minor k i M (strongenFin l le) j
             · det (minor (strongenFin l le) j (minor k i M))))
          ≡⟨
            cong
            (λ a →
              M l i · MF (toℕ k +ℕ toℕ i) ·
                (MF (toℕ (strongenFin l le) +ℕ toℕ j) · a
                · det (minor (strongenFin l le) j (minor k i M))))
            (minorIdId
              k
              i
              (strongenFin l le)
              j
              M
              (strongenFinLeId l le)
              lf)
           ⟩
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             M (weakenFin (strongenFin l le)) (weakenFin j)
             · det (minor (strongenFin l le) j (minor k i M))))
          ≡⟨
            cong
            (λ a →
              M l i · MF (toℕ k +ℕ toℕ i) ·
                (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                M a (weakenFin j)
                · det (minor (strongenFin l le) j (minor k i M))))
            (weakenStrongenFin l le)
           ⟩
          (M l i · MF (toℕ k +ℕ toℕ i) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) · M l (weakenFin j) ·
             det (minor (strongenFin l le) j (minor k i M))))
          ≡⟨
           cong
           (λ a → M l i · a ·
                  (MF (toℕ (strongenFin l le) +ℕ toℕ j) · M l (weakenFin j) ·
                  det (minor (strongenFin l le) j (minor k i M))))
           (sumMF (toℕ k) (toℕ i))
           ⟩
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) · M l (weakenFin j) ·
             det (minor (strongenFin l le) j (minor k i M))))
          ≡⟨
            cong
            (λ a →
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
              (a · M l (weakenFin j) ·
              det (minor (strongenFin l le) j (minor k i M)))))
            (sumMF (toℕ (strongenFin l le)) (toℕ j))
           ⟩
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ (strongenFin l le)) · MF (toℕ j) · M l (weakenFin j) ·
             det (minor (strongenFin l le) j (minor k i M))))
          ≡⟨
            cong
            (λ a → M l i · (MF (toℕ k) · MF (toℕ i)) ·
                   (MF a · MF (toℕ j) · M l (weakenFin j) ·
                   det (minor (strongenFin l le) j (minor k i M))))
            (toℕstrongenFin l le)
           ⟩
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
            (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j) ·
             det (minor (strongenFin l le) j (minor k i M))))
          ∎)
        )

    adjugatePropAux3b : (M : FinMatrix R (suc (suc n)) (suc (suc n))) → (k l : Fin (suc (suc n))) → (le : toℕ l <' toℕ k) →
      ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k (weakenFin i) M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))))
     ≡
     ∑
       (λ i →
          ∑
          (λ z →
             ind> (suc (toℕ z)) (toℕ i) ·
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
              (MF (toℕ l) · (- 1r · MF (suc (toℕ z))) · M l (suc z) ·
               det (minor (strongenFin l le) i (minor k (suc z) M))))))
    adjugatePropAux3b M k l le =
      ∑∑Compat
      (λ i j →
              (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k (weakenFin i) M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k (weakenFin i) M)))))
      (λ z z₁ →
          ind> (suc (toℕ z₁)) (toℕ z) ·
          (M l (weakenFin z) · (MF (toℕ k) · MF (toℕ (weakenFin z))) ·
           (MF (toℕ l) · (- 1r · MF (suc (toℕ z₁))) · M l (suc z₁) ·
            det (minor (strongenFin l le) z (minor k (suc z₁) M)))))
      (λ i j →
         (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
           (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             minor k (weakenFin i) M (strongenFin l le) j
             · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))
         ≡⟨ cong
           (λ a → (1r + - ind> a (toℕ j)) ·
           (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             minor k (weakenFin i) M (strongenFin l le) j
             · det (minor (strongenFin l le) j (minor k (weakenFin i) M)))))
           (weakenRespToℕ i) ⟩
         (1r + - ind> (toℕ i) (toℕ j)) ·
           (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             minor k (weakenFin i) M (strongenFin l le) j
             · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))
         ≡⟨
           ind>anti
           (λ i j → M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
            (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
             minor k (weakenFin i) M (strongenFin l le) j
             · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))
           (λ z z₁ →
               M l (weakenFin z) · (MF (toℕ k) · MF (toℕ (weakenFin z))) ·
               (MF (toℕ l) · (- 1r · MF (suc (toℕ z₁))) · M l (suc z₁) ·
                det (minor (strongenFin l le) z (minor k (suc z₁) M))))
           (λ i j lf  →
             (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k (weakenFin i) M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))
             ≡⟨
               cong
               (λ a →
                 M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
                   (MF (toℕ (strongenFin l le) +ℕ toℕ j) · a
                   · det (minor (strongenFin l le) j (minor k (weakenFin i) M))))
               (minorIdSuc
                 k
                 (weakenFin i)
                 (strongenFin l le)
                 j
                 M
                 (strongenFinLeId l le)
                 (weakenweakenFinLe i j lf))
              ⟩
             M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) j (minor k (weakenFin i) M)))
             ≡⟨
               cong
               (λ a →
                  M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
                   (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                   M (weakenFin (strongenFin l le)) (suc j) · a))
               (detComp
                 (minor (strongenFin l le) j (minor k (weakenFin i) M))
                 (minor (strongenFin l le) i (minor k (suc j) M))
                 (λ i₁ j₁ → sym
                     (minorSemiCommR k (strongenFin l le) j i i₁ j₁ M lf) )
               )
              ⟩
             (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
             ≡⟨
               cong
               (λ a →
                 M l (weakenFin i) · a ·
                   (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                   M (weakenFin (strongenFin l le)) (suc j)
                   · det (minor (strongenFin l le) i (minor k (suc j) M))))
               (sumMF (toℕ k) (toℕ (weakenFin i)))
              ⟩
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
             ≡⟨ cong
                (λ a → M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
                 (a · M (weakenFin (strongenFin l le)) (suc j)
                 · det (minor (strongenFin l le) i (minor k (suc j) M))))
                (sumMF (toℕ (strongenFin l le)) (toℕ j))
              ⟩
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ (strongenFin l le)) · MF (toℕ j) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
             ≡⟨
               cong
               (λ a →
                 M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF a · MF (toℕ j) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
               (toℕstrongenFin l le)
              ⟩
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · MF (toℕ j) · M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
             ≡⟨
               cong
               (λ a →
                 M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
                   (MF (toℕ l) · a · M (weakenFin (strongenFin l le)) (suc j)
                   · det (minor (strongenFin l le) i (minor k (suc j) M))))
               (sucMFRev (toℕ j))
              ⟩
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) ·
                M (weakenFin (strongenFin l le)) (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
             ≡⟨ cong
               (λ a →
                 M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) ·
                M a (suc j)
                · det (minor (strongenFin l le) i (minor k (suc j) M))))
               (weakenStrongenFin l le)
              ⟩
             (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) · M l (suc j) ·
                det (minor (strongenFin l le) i (minor k (suc j) M))))
             ∎)
           i
           j
          ⟩
         (1r + - ind> (toℕ i) (toℕ j)) ·
           (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
            (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) · M l (suc j) ·
             det (minor (strongenFin l le) i (minor k (suc j) M))))
         ≡⟨
           cong
           (λ a →
             a ·
           (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
            (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) · M l (suc j) ·
             det (minor (strongenFin l le) i (minor k (suc j) M)))))
           (sym (ind>Suc (toℕ j) (toℕ i)))
          ⟩
         (ind> (suc (toℕ j)) (toℕ i) ·
           (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
            (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) · M l (suc j) ·
             det (minor (strongenFin l le) i (minor k (suc j) M)))))
         ∎)

    adjugatePropAux4a : (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
      (k l : Fin (suc (suc n))) → (le : toℕ l <' toℕ k) →
       ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j) ·
                det (minor (strongenFin l le) j (minor k i M))))))
       ≡
       ∑
         (λ i →
            ∑
            (λ z →
               ind> (toℕ i) (toℕ z) ·
               (1r ·
                (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                 (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
                · det (minor (strongenFin l le) z (minor k i M)))))
    adjugatePropAux4a M k l le =
      ∑∑Compat
      (λ i j →
        ind> (toℕ i) (toℕ j) ·
        (M l i · (MF (toℕ k) · MF (toℕ i)) ·
        (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j) ·
        det (minor (strongenFin l le) j (minor k i M)))))
      (λ z z₁ →
          ind> (toℕ z) (toℕ z₁) ·
          (1r ·
           (M l z · (MF (toℕ k) · MF (toℕ z₁)) ·
            (MF (toℕ l) · MF (toℕ z) · M l (weakenFin z₁)))
           · det (minor (strongenFin l le) z₁ (minor k z M))))
      (λ i j →
        (ind> (toℕ i) (toℕ j) ·
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
           (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j) ·
            det (minor (strongenFin l le) j (minor k i M)))))
        ≡⟨
          cong
          (λ a →
            ind> (toℕ i) (toℕ j) · a)
          (·Assoc _ _ _)
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          (M l i · (MF (toℕ k) · MF (toℕ i)) ·
           (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j))
           · det (minor (strongenFin l le) j (minor k i M))))
        ≡⟨
          cong
          (λ a →
             ind> (toℕ i) (toℕ j) ·
              (a · det (minor (strongenFin l le) j (minor k i M))))
          (solve! P')
         ⟩
        (ind> (toℕ i) (toℕ j) ·
          ( 1r ·
           ( M l i · (MF (toℕ k) · MF (toℕ j)) ·
            (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j))) ·
             det (minor (strongenFin l le) j (minor k i M))))
        ∎)

    adjugatePropAux4b : (M : FinMatrix R (suc (suc n)) (suc (suc n))) →
      (k l : Fin (suc (suc n))) → (le : toℕ l <' toℕ k) →
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ (weakenFin j))) ·
               (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (strongenFin l le) j (minor k i M))))))
      ≡
      ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (- 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
               · det (minor (strongenFin l le) z (minor k i M)))))
    adjugatePropAux4b M k l le =
      ∑∑Compat
      (λ i j →
        ind> (toℕ i) (toℕ j) ·
        (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ (weakenFin j))) ·
        (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
        det (minor (strongenFin l le) j (minor k i M)))))
      (λ z z₁ →
          ind> (toℕ z) (toℕ z₁) ·
          (- 1r ·
           (M l z · (MF (toℕ k) · MF (toℕ z₁)) ·
            (MF (toℕ l) · MF (toℕ z) · M l (weakenFin z₁)))
           · det (minor (strongenFin l le) z₁ (minor k z M))))
      (λ i j →
        (ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ (weakenFin j))) ·
           (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (strongenFin l le) j (minor k i M)))))
        ≡⟨
          cong
          (λ a →
            ind> (toℕ i) (toℕ j) ·
            (M l (weakenFin j) · (MF (toℕ k) · MF a) ·
            (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (strongenFin l le) j (minor k i M)))))
          (weakenRespToℕ j)
         ⟩
        ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ j)) ·
           (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
            det (minor (strongenFin l le) j (minor k i M))))
        ≡⟨ cong
          (λ a → ind> (toℕ i) (toℕ j) · a)
          (·Assoc _ _ _)
         ⟩
        ind> (toℕ i) (toℕ j) ·
          (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ j)) ·
           (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i)
           · det (minor (strongenFin l le) j (minor k i M)))
        ≡⟨
          cong
          (λ a → ind> (toℕ i) (toℕ j) · (a
           · det (minor (strongenFin l le) j (minor k i M))))
          (solve! P')
         ⟩
        ind> (toℕ i) (toℕ j) ·
        ((- 1r) ·( M l (weakenFin j) · (MF (toℕ k) · MF (toℕ j)) ·
        (MF (toℕ l) · MF (toℕ i) · M l i))
        · det (minor (strongenFin l le) j (minor k i M)))
        ≡⟨ cong
          (λ a  → ind> (toℕ i) (toℕ j) ·
          ((- 1r) · a
          · det (minor (strongenFin l le) j (minor k i M))))
          (solve! P')
        ⟩
        ind> (toℕ i) (toℕ j) ·
          ((- 1r) ·
           ( M l i · (MF (toℕ k) · MF (toℕ j)) ·
            (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j))) ·
             det (minor (strongenFin l le) j (minor k i M)))
        ∎)

    adjugatePropRL : (M : FinMatrix R (suc n) (suc n)) → (k l : Fin (suc n)) → toℕ l <' toℕ k →
     ∑ (λ i → (M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))) ≡ 0r
    adjugatePropRL {zero} M zero zero ()
    adjugatePropRL {zero} M (suc ()) zero (s≤s le)
    adjugatePropRL {suc n} M k l le =
       ∑ (λ i → M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))
      ≡⟨ ∑Compat
         (λ i → M l i · (MF (toℕ k +ℕ toℕ i) · det (minor k i M)))
         (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
         (λ i → ·Assoc _ _ _)
        ⟩
      ∑ (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
      ≡⟨ ∑Compat
         (λ i → M l i · MF (toℕ k +ℕ toℕ i) · det (minor k i M))
         (λ i → M l i · MF (toℕ k +ℕ toℕ i) · detR (strongenFin l le) (minor k i M))
         (λ i →
           cong
           (λ a → M l i · MF (toℕ k +ℕ toℕ i) · a)
           (sym (DetRow  (strongenFin l le) (minor k i M)))) ⟩
      ∑
        (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) ·
           detR (strongenFin l le) (minor k i M))
      ≡⟨ refl ⟩
      ∑
        (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) ·
           ∑
           (λ j →
              MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M))))
      ≡⟨ ∑Compat
        (λ i →
           M l i · MF (toℕ k +ℕ toℕ i) ·
           ∑
           (λ j →
              MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M))))
        (λ i →
           ∑
           (λ j →  M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M)))))
        (λ i →
          ∑DistR
            (M l i · MF (toℕ k +ℕ toℕ i))
            ( (λ j →
              MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M)))))
       ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
               minor k i M (strongenFin l le) j
               · det (minor (strongenFin l le) j (minor k i M)))))
      ≡⟨ ∑∑Compat
        (λ i j →
              M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
               minor k i M (strongenFin l le) j
               · det (minor (strongenFin l le) j (minor k i M))))
        (λ i j →
            ind> (toℕ i) (toℕ j) ·
            (M l i · MF (toℕ k +ℕ toℕ i) ·
             (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M))))
            +
            (1r + - ind> (toℕ i) (toℕ j)) ·
            (M l i · MF (toℕ k +ℕ toℕ i) ·
             (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
              minor k i M (strongenFin l le) j
              · det (minor (strongenFin l le) j (minor k i M)))))
        (λ i j →
          distributeOne
          (ind> (toℕ i) (toℕ j))
          ( M l i · MF (toℕ k +ℕ toℕ i) ·
              (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
               minor k i M (strongenFin l le) j
               · det (minor (strongenFin l le) j (minor k i M))))
        )
       ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))
              +
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))))
      ≡⟨ ∑∑Split
         (λ i j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M)))))
         (λ i j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))) ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))))
       +
       ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ i) (toℕ j)) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))))
      ≡⟨ +Compat refl (∑∑ShiftWeak (λ i  j →
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M)))))) ⟩
      (∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · MF (toℕ k +ℕ toℕ i) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k i M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k i M))))))
        +
        ∑
        (λ i →
           ∑
           (λ j →
              (1r + - ind> (toℕ (weakenFin i)) (toℕ j)) ·
              (M l (weakenFin i) · MF (toℕ k +ℕ toℕ (weakenFin i)) ·
               (MF (toℕ (strongenFin l le) +ℕ toℕ j) ·
                minor k (weakenFin i) M (strongenFin l le) j
                · det (minor (strongenFin l le) j (minor k (weakenFin i) M)))))))
      ≡⟨ +Compat (adjugatePropAux3a M k l le) (adjugatePropAux3b M k l le) ⟩
      ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ l) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (strongenFin l le) z (minor k i M))))))
        +
        ∑
          (λ i →
             ∑
             (λ z →
                ind> (suc (toℕ z)) (toℕ i) ·
                (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
                 (MF (toℕ l) · (- 1r · MF (suc (toℕ z))) · M l (suc z) ·
                  det (minor (strongenFin l le) i (minor k (suc z) M))))))
      ≡⟨ +Compat
         refl
         (∑Comm (λ i z →
                ind> (suc (toℕ z)) (toℕ i) ·
                (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
                 (MF (toℕ l) · (- 1r · MF (suc (toℕ z))) · M l (suc z) ·
                  det (minor (strongenFin l le) i (minor k (suc z) M)))))) ⟩
      (∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ l) · MF (toℕ z) · M l (weakenFin z) ·
                det (minor (strongenFin l le) z (minor k i M))))))
        +
        ∑
        (λ j →
           ∑
           (λ i →
              ind> (suc (toℕ j)) (toℕ i) ·
              (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · (- 1r · MF (suc (toℕ j))) · M l (suc j) ·
                det (minor (strongenFin l le) i (minor k (suc j) M)))))))
      ≡⟨
        +Compat
        refl
        (sym
          (∑∑ShiftSuc
          λ j i →
              (M l (weakenFin i) · (MF (toℕ k) · MF (toℕ (weakenFin i))) ·
               (MF (toℕ l) · (- 1r · MF (toℕ j)) · M l j ·
                det (minor (strongenFin l le) i (minor k j M))))))
       ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l i · (MF (toℕ k) · MF (toℕ i)) ·
               (MF (toℕ l) · MF (toℕ j) · M l (weakenFin j) ·
                det (minor (strongenFin l le) j (minor k i M))))))
       +
       ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (M l (weakenFin j) · (MF (toℕ k) · MF (toℕ (weakenFin j))) ·
               (MF (toℕ l) · (- 1r · MF (toℕ i)) · M l i ·
                det (minor (strongenFin l le) j (minor k i M))))))
      ≡⟨ +Compat (adjugatePropAux4a M k l le) (adjugatePropAux4b M k l le) ⟩
      ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (1r ·
               (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
               · det (minor (strongenFin l le) z (minor k i M)))))
        +
        ∑
        (λ i →
           ∑
           (λ z →
              ind> (toℕ i) (toℕ z) ·
              (- 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
               · det (minor (strongenFin l le) z (minor k i M)))))
       ≡⟨
         sym
         (∑∑Split
           (λ i z →
              ind> (toℕ i) (toℕ z) ·
              (1r ·
               (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
               · det (minor (strongenFin l le) z (minor k i M))))
           λ i z →
              ind> (toℕ i) (toℕ z) ·
              (- 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ z)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin z)))
               · det (minor (strongenFin l le) z (minor k i M))))
        ⟩
      ∑
        (λ i →
           ∑
           (λ j →
              ind> (toℕ i) (toℕ j) ·
              (1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               · det (minor (strongenFin l le) j (minor k i M)))
              +
              ind> (toℕ i) (toℕ j) ·
              (- 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               · det (minor (strongenFin l le) j (minor k i M)))))
       ≡⟨
         ∑∑Compat
         (λ i j →
              ind> (toℕ i) (toℕ j) ·
              (1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               · det (minor (strongenFin l le) j (minor k i M)))
              +
              ind> (toℕ i) (toℕ j) ·
              (- 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               · det (minor (strongenFin l le) j (minor k i M))))
         (λ _ _ → 0r)
         (λ i j →
           (ind> (toℕ i) (toℕ j) ·
             (1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
              · det (minor (strongenFin l le) j (minor k i M)))
             +
             ind> (toℕ i) (toℕ j) ·
             (- 1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
              · det (minor (strongenFin l le) j (minor k i M))))
           ≡⟨ sym
             (·DistR+
               (ind> (toℕ i) (toℕ j))
               (1r ·
                 (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                 (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
                 · det (minor (strongenFin l le) j (minor k i M)))
               (- 1r · (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                 (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
                 · det (minor (strongenFin l le) j (minor k i M)))) ⟩
           (ind> (toℕ i) (toℕ j) ·
             (1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
              · det (minor (strongenFin l le) j (minor k i M))
              +
              - 1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
              · det (minor (strongenFin l le) j (minor k i M)))
             )
           ≡⟨
             cong
             (λ a → ind> (toℕ i) (toℕ j) · a)
             (sym
               (·DistL+
               (1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j))))
               ( - 1r ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j))))
               (det (minor (strongenFin l le) j (minor k i M)))))
            ⟩
           (ind> (toℕ i) (toℕ j) ·
             ((1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               +
               - 1r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j))))
              · det (minor (strongenFin l le) j (minor k i M))))
           ≡⟨
             cong
             (λ a →
               ind> (toℕ i) (toℕ j) · (a ·
                det (minor (strongenFin l le) j (minor k i M))))
             (sym
               (·DistL+
               1r
               (- 1r)
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                 (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))))
            ⟩
           (ind> (toℕ i) (toℕ j) ·
             ((1r + - 1r) ·
              (M l i · (MF (toℕ k) · MF (toℕ j)) ·
               (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
              · det (minor (strongenFin l le) j (minor k i M))))
            ≡⟨ cong
              (λ a → (ind> (toℕ i) (toℕ j) ·
                      (a · (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                      (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
                      · det (minor (strongenFin l le) j (minor k i M)))))
              (+InvR 1r)
             ⟩
            (ind> (toℕ i) (toℕ j) ·
              (0r ·
               (M l i · (MF (toℕ k) · MF (toℕ j)) ·
                (MF (toℕ l) · MF (toℕ i) · M l (weakenFin j)))
               · det (minor (strongenFin l le) j (minor k i M))))
            ≡⟨
              cong
              (λ a → (ind> (toℕ i) (toℕ j) ·
              (a · det (minor (strongenFin l le) j (minor k i M)))))
              (solve! P')
             ⟩
            (ind> (toℕ i) (toℕ j) ·
              (0r · det (minor (strongenFin l le) j (minor k i M))))
            ≡⟨ cong
              (λ a → ind> (toℕ i) (toℕ j) · a)
              (RingTheory.0LeftAnnihilates
                (CommRing→Ring P')
                (det (minor (strongenFin l le) j (minor k i M)))) ⟩
            (ind> (toℕ i) (toℕ j) · 0r)
            ≡⟨ solve! P' ⟩
            0r
           ∎)⟩
       ∑ (λ (i : Fin (suc (suc n))) → ∑ (λ (j : Fin (suc n)) → 0r))
       ≡⟨ ∑Zero
         (λ (i : Fin (suc (suc n))) → ∑ (λ (j : Fin (suc n)) → 0r))
         (λ i → ∑Zero (λ (j : Fin (suc n)) → 0r) (λ (j : Fin (suc n)) → refl)) ⟩
      0r
      ∎

    adjugateInvRLcomponent : {n : ℕ} → (M : FinMatrix R n n) → (k l : Fin n) → toℕ k <' toℕ l → (M ⋆ adjugate M) k l ≡  (det M ∘ 𝟙) k l
    adjugateInvRLcomponent {suc n} M k l le =
      ∑ (λ i → M k i · (MF(toℕ l +ℕ toℕ i) · det(minor l i M)) )
      ≡⟨ adjugatePropRL M l k le  ⟩
      0r
      ≡⟨ sym (RingTheory.0RightAnnihilates (CommRing→Ring P') (det M)) ⟩
      det M · 0r
      ≡⟨ cong (λ a → det M · a) (sym (deltaProp k l le)) ⟩
      (det M ∘ 𝟙) k l
      ∎

  FinCompare : {n : ℕ} → (k l : Fin n) →  (k ≡ l) ⊎ ((toℕ k <' toℕ l) ⊎ (toℕ l <' toℕ k))
  FinCompare {zero} () ()
  FinCompare {suc n} zero zero = inl refl
  FinCompare {suc n} zero (suc l) = inr (inl (s≤s z≤))
  FinCompare {suc n} (suc k) zero = inr (inr (s≤s z≤))
  FinCompare {suc n} (suc k) (suc l) with FinCompare {n} k l
  ... | inl x = inl (cong (λ a → (suc a)) x)
  ... | inr (inl x) = inr (inl (s≤s x))
  ... | inr (inr x) = inr (inr (s≤s x))

  opaque
    -- The adjugate matrix divided by the determinant is the right inverse.
    -- Component-wise version
    adjugateInvRComp : {n : ℕ} → (M : FinMatrix R n n) → (k l : Fin n)  → (M ⋆ adjugate M) k l ≡  (det M ∘ 𝟙) k l
    adjugateInvRComp {zero} M () ()
    adjugateInvRComp {suc n} M k l  with FinCompare k l
    ... | inl x =
      (∑ (λ i → M k i · (MF(toℕ l +ℕ toℕ i) · det(minor l i M)) )
       ≡⟨
         ∑Compat
         (λ i → M k i · (MF(toℕ l +ℕ toℕ i) · det(minor l i M)))
         (λ i → M k i · MF(toℕ l +ℕ toℕ i) · det(minor l i M))
         (λ i → ·Assoc _ _ _)
         ⟩
       ∑ (λ i → M k i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
       ≡⟨
         ∑Compat
         (λ i → M k i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
         (λ i → M l i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
         (λ i → cong
                (λ a → M a i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
                x )
        ⟩
       ∑ (λ i → M l i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
       ≡⟨  ∑Compat
             (λ i → M l i · MF (toℕ l +ℕ toℕ i) · det (minor l i M))
             (λ i → MF (toℕ l +ℕ toℕ i) · M l i · det (minor l i M))
             (λ i → cong
                (λ a → a · det (minor l i M))
                (CommRingStr.·Comm (snd P') (M l i) (MF (toℕ l +ℕ toℕ i))) ) ⟩
       detR l M
       ≡⟨ DetRow l M ⟩
       det M
       ≡⟨ sym (·IdR (det M)) ⟩
       (det M · 1r)
       ≡⟨ cong (λ a →  det M · a) (sym (deltaPropEq k l x))⟩
       (det M ∘ 𝟙) k l
       ∎)
    ... | inr (inl x) = adjugateInvRLcomponent M k l x
    ... | inr (inr x) =  adjugateInvRGcomponent M k l x

    -- The adjugate matrix divided by the determinant is the left inverse.
    -- Component-wise version
    adjugateInvLComp : {n : ℕ} → (M : FinMatrix R n n) → (k l : Fin n)  → (adjugate M ⋆ M) k l ≡  (det M ∘ 𝟙) k l
    adjugateInvLComp M k l =
      (adjugate M ⋆ M) k l
      ≡⟨ refl ⟩
      ∑ (λ i → adjugate M k i · (M ᵗ) l i)
      ≡⟨
        ∑Compat
        (λ i → adjugate M k i · (M ᵗ) l i)
        (λ i → adjugate (M ᵗ) i k · (M ᵗ) l i)
        (λ i → cong (λ a → a · (M ᵗ) l i) (sym (adjugateTransp M i k)))
       ⟩
      ∑ (λ i → adjugate (M ᵗ) i k · (M ᵗ) l i)
      ≡⟨
        ∑Compat
        (λ i → adjugate (M ᵗ) i k · (M ᵗ) l i)
        (λ z → (snd P' CommRingStr.· (M ᵗ) l z) (adjugate (M ᵗ) z k))
        (λ i → CommRingStr.·Comm (snd P') (adjugate (M ᵗ) i k) ((M ᵗ) l i))
       ⟩
      ∑ (λ i → (M ᵗ) l i · adjugate (M ᵗ) i k )
      ≡⟨ adjugateInvRComp (M ᵗ) l k ⟩
      (det (M ᵗ) ∘ 𝟙) l k
      ≡⟨ cong (λ a → (a ∘ 𝟙) l k) (sym (detTransp M)) ⟩
      det M · δ l k
      ≡⟨ cong (λ a → det M · a) (deltaComm l k) ⟩
      (det M · 𝟙 k l)
      ∎

    -- The adjugate matrix divided by the determinant is the right inverse.
    adjugateInvR : {n : ℕ} → (M : FinMatrix R n n)  → M ⋆ adjugate M ≡  det M ∘ 𝟙
    adjugateInvR M = funExt₂ (λ k l →  adjugateInvRComp M k l)

    -- The adjugate matrix divided by the determinant is the left inverse.
    adjugateInvL : {n : ℕ} → (M : FinMatrix R n n)  → adjugate M ⋆ M ≡  det M ∘ 𝟙
    adjugateInvL M = funExt₂ (λ k l →  adjugateInvLComp M k l)
