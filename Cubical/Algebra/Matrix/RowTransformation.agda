{-

Technical results about row transformation applied to matrices

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix.RowTransformation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.FinData renaming (znots to znotsFin ; snotz to snotzFin)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.RingSolver.Reflection

private
  variable
    ℓ : Level
    A : Type ℓ
    m n k l : ℕ

takeRow : (i : Fin m) → FinMatrix A (suc m) n → FinMatrix A 2 n
takeRow i M zero = M zero
takeRow i M one  = M (suc i)

≤-helper : (p : suc k < m)(q : l < m)(q' : l ≤ suc k)(r : ¬ enum (suc k) p ≡ enum l q) → l ≤ k
≤-helper p q q' r = pred-≤-pred (≤→< q' (λ s → r (enumExt p q (sym s))))

module _
  (T : FinMatrix A 2 n → FinMatrix A 2 n) where

  transOf2Rows-helper : (i j : Fin m) → biEq i j → FinMatrix A (suc m) n → FinVec A n
  transOf2Rows-helper i j (eq  _) M = T (takeRow i M) one
  transOf2Rows-helper i j (¬eq _) M = M (suc j)

  transOf2Rows : FinMatrix A (suc m) n → (i : Fin m) → FinMatrix A (suc m) n
  transOf2Rows {m = 0} M _ = M
  transOf2Rows {m = suc m} M i zero = T (takeRow i M) zero
  transOf2Rows {m = suc m} M i (suc j) = transOf2Rows-helper i j (biEq? _ _) M

  transOfRows-helper : (m k : ℕ)(p : k < m) → FinMatrix A (suc m) n → FinMatrix A (suc m) n
  transOfRows-helper 0 _ p = Empty.rec (¬-<-zero p)
  transOfRows-helper (suc m) 0 _ M = transOf2Rows M zero
  transOfRows-helper (suc m) (suc k) p M = transOf2Rows (transOfRows-helper (suc m) k (suc-< p) M) (enum _ p)

  transOfRows : FinMatrix A (suc m) n → FinMatrix A (suc m) n
  transOfRows {m = 0} M = M
  transOfRows {m = suc m} = transOfRows-helper (suc m) m ≤-refl

  module _
    (invRow : (M : FinMatrix A 2 n) → M zero ≡ T M zero) where

    invRow₀-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → M zero ≡ transOfRows-helper m k p M zero
    invRow₀-helper 0 _ p = Empty.rec (¬-<-zero p)
    invRow₀-helper (suc m) 0 _ _ = invRow _
    invRow₀-helper (suc m) (suc k) p M = invRow₀-helper _ _ (suc-< p) M ∙ invRow _

    invRow₀ : (M : FinMatrix A (suc m) n) → M zero ≡ transOfRows M zero
    invRow₀ {m = 0} _ = refl
    invRow₀ {m = suc m} = invRow₀-helper _ m ≤-refl

  transOfRows-invariance :
      (m k : ℕ)(p : k < m)
    → (M : FinMatrix A (suc m) n)
    → (l : ℕ)(q : l < m)(q' : k < l)
    → M (suc (enum l q)) ≡ transOfRows-helper m k p M (suc (enum l q))
  transOfRows-invariance 0 _ p = Empty.rec (¬-<-zero p)
  transOfRows-invariance (suc m) 0 p M l q q' = helper (biEq? _ _)
    where
      helper : (h : biEq (enum _ p) (enum l q))
        → M (suc (enum l q)) ≡ transOf2Rows-helper zero (enum l q) h M
      helper (eq  r) = Empty.rec (<→≢ q' (enumInj {p = p} r))
      helper (¬eq r) = refl
  transOfRows-invariance (suc m) (suc k) p M l q q' = helper (biEq? _ _)
    where
      helper : (h : biEq (enum _ p) (enum l q))
        → M (suc (enum l q)) ≡ transOf2Rows-helper _ _ h (transOfRows-helper _ _ (suc-< p) M)
      helper (eq  r) = Empty.rec (<→≢ q' (enumInj r))
      helper (¬eq r) = transOfRows-invariance _ _ (suc-< p) M l q (<-trans ≤-refl q')

  -- Several induction principle to prove properties after transformation

  module _
    (P : FinVec A n → Type ℓ)
    (indP : (M : FinMatrix A 2 n) → P (M zero) → P (T M zero)) where

    transOfRowsIndP-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → P (M zero)
      → P (transOfRows-helper m k p M zero)
    transOfRowsIndP-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndP-helper (suc m) 0 p M h = indP _ h
    transOfRowsIndP-helper (suc m) (suc k) p M h = indP _ (transOfRowsIndP-helper (suc m) k _ M h)

    transOfRowsIndP : (M : FinMatrix A (suc m) n) → P (M zero) → P (transOfRows M zero)
    transOfRowsIndP {m = 0} _ h = h
    transOfRowsIndP {m = suc m} = transOfRowsIndP-helper _ m ≤-refl

  module _
    (P : FinVec A n → Type ℓ)
    (indP : (M : FinMatrix A 2 n) → P (T M one)) where

    transOfRowsIndP'-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → P (transOfRows-helper m k p M (suc (enum l q)))
    transOfRowsIndP'-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndP'-helper (suc m) 0 p M l q q' =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      subst P (λ i → transOfRows-helper _ _ p M (sk≡sl i)) (indP _)
    transOfRowsIndP'-helper (suc m) (suc k) p M l q q' = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → P (transOf2Rows-helper _ _ h (transOfRows-helper (suc m) k (suc-< p) M))
        helper (eq  r) = indP _
        helper (¬eq r) = transOfRowsIndP'-helper _ _ (suc-< p) M l q (≤-helper p q q' r)

    transOfRowsIndP' : (M : FinMatrix A (suc m) n) → (i : Fin m) → P (transOfRows M (suc i))
    transOfRowsIndP' {m = suc m} M = enumElim _ _ ≤-refl refl (transOfRowsIndP'-helper _ m ≤-refl M)

  module _
    (Q : FinVec A n → Type ℓ)
    (P : FinVec A n → Type ℓ)
    (indQ : (M : FinMatrix A 2 n) → Q (M zero) → Q (T M zero))
    (indP : (M : FinMatrix A 2 n) → Q (M zero) → P (T M one )) where

    transOfRowsIndPQ-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → Q (M zero)
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → P (transOfRows-helper m k p M (suc (enum l q)))
    transOfRowsIndPQ-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndPQ-helper (suc m) 0 p M s l q q' =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      subst P (λ i → transOfRows-helper _ _ p M (sk≡sl i)) (indP _ s)
    transOfRowsIndPQ-helper (suc m) (suc k) p M s l q q' = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → P (transOf2Rows-helper _ _ h (transOfRows-helper (suc m) k (suc-< p) M))
        helper (eq  r) = indP _ (transOfRowsIndP-helper Q indQ (suc m) k _ _ s)
        helper (¬eq r) = transOfRowsIndPQ-helper _ _ (suc-< p) M s l q (≤-helper p q q' r)

    transOfRowsIndPQ : (M : FinMatrix A (suc m) n) → Q (M zero) → (i : Fin m) → P (transOfRows M (suc i))
    transOfRowsIndPQ {m = suc m} M p = enumElim _ _ ≤-refl refl (transOfRowsIndPQ-helper _ m ≤-refl M p)

  module _
    (Q : FinVec A n → Type ℓ)
    (P : FinVec A n → Type ℓ)
    (indQ : (M : FinMatrix A 2 n) → Q (M zero) → Q (T M zero))
    (indP : (M : FinMatrix A 2 n) → P (M one ) → Q (T M zero)) where

    transOfRowsIndPQ'-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → P (M (suc (enum l q)))
      → Q (transOfRows-helper m k p M zero)
    transOfRowsIndPQ'-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndPQ'-helper (suc m) 0 p M l q q' s =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      indP _ (subst P (λ i → M (sk≡sl (~ i))) s)
    transOfRowsIndPQ'-helper (suc m) (suc k) p M l q q' s = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → Q (transOfRows-helper (suc m) (suc k) p M zero)
        helper (eq  r) =
          let invRow =
                  transOfRows-invariance (suc m) k _ _ l _
                    (subst (λ a → k < a) (enumInj r) ≤-refl)
                ∙ (λ i → transOfRows-helper _ _ (suc-< p) M (suc (r (~ i))))
          in  indP _ (subst P invRow s)
        helper (¬eq r) =
          indQ _ (transOfRowsIndPQ'-helper _ _ (suc-< p) M l q (≤-helper p q q' r) s)

    transOfRowsIndPQ' : (M : FinMatrix A (suc m) n) → (i : Fin m) → P (M (suc i)) → Q (transOfRows M zero)
    transOfRowsIndPQ' {m = suc m} M = enumElim _ _ ≤-refl refl (transOfRowsIndPQ'-helper _ m ≤-refl M)

  module _
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indRel : (M : FinMatrix A 2 n) → Rel (M one) (T M one)) where

    transOfRowsIndRel-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → Rel (M (suc (enum l q))) (transOfRows-helper m k p M (suc (enum l q)))
    transOfRowsIndRel-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndRel-helper (suc m) 0 p M l q q' =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      transport (λ i → Rel (M (sk≡sl i)) (transOfRows-helper _ _ p M (sk≡sl i)))
                (indRel _)
    transOfRowsIndRel-helper (suc m) (suc k) p M l q q' = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → Rel (M (suc (enum l q)))
                (transOf2Rows-helper _ _ h (transOfRows-helper (suc m) k (suc-< p) M))
        helper (eq  r) =
          let invRow =
                  transOfRows-invariance (suc m) k _ _ l _
                    (subst (λ a → k < a) (enumInj r) ≤-refl)
                ∙ (λ i → transOfRows-helper _ _ (suc-< p) M (suc (r (~ i))))
          in  subst (λ V →
                      Rel V (transOf2Rows-helper _ _ (eq r)
                              (transOfRows-helper (suc m) k (suc-< p) M)))
                    (sym invRow) (indRel _)
        helper (¬eq r) = transOfRowsIndRel-helper _ _ (suc-< p) M l q (≤-helper p q q' r)

    transOfRowsIndRel : (M : FinMatrix A (suc m) n) → (i : Fin m) → Rel (M (suc i)) (transOfRows M (suc i))
    transOfRowsIndRel {m = suc m} M = enumElim _ _ ≤-refl refl (transOfRowsIndRel-helper _ m ≤-refl M)

  module _
    (Rel3 : FinVec A n → FinVec A n → FinVec A n → Type ℓ)
    (invRow : (M : FinMatrix A 2 n) → M zero ≡ T M zero)
    (indRel3 : (M : FinMatrix A 2 n) → Rel3 (M zero) (M one) (T M one)) where

    transOfRowsIndRel3-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → Rel3 (M zero) (M (suc (enum l q))) (transOfRows-helper m k p M (suc (enum l q)))
    transOfRowsIndRel3-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndRel3-helper (suc m) 0 p M l q q' =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      transport (λ i → Rel3 (M zero) (M (sk≡sl i)) (transOfRows-helper _ _ p M (sk≡sl i)))
                (indRel3 _)
    transOfRowsIndRel3-helper (suc m) (suc k) p M l q q' = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → Rel3 (M zero) (M (suc (enum l q)))
                 (transOf2Rows-helper _ _ h (transOfRows-helper (suc m) k (suc-< p) M))
        helper (eq  r) =
          let invRow0 = invRow₀-helper invRow (suc m) k _ _
              invRow =
                  transOfRows-invariance (suc m) k _ _ l _
                    (subst (λ a → k < a) (enumInj r) ≤-refl)
                ∙ (λ i → transOfRows-helper _ _ (suc-< p) M (suc (r (~ i))))
          in  transport (λ t → Rel3 (invRow0 (~ t)) (invRow (~ t)) (transOf2Rows-helper _ _ (eq r)
                          (transOfRows-helper (suc m) k (suc-< p) M)))
                        (indRel3 _)
        helper (¬eq r) = transOfRowsIndRel3-helper _ _ (suc-< p) M l q (≤-helper p q q' r)

    transOfRowsIndRel3 : (M : FinMatrix A (suc m) n) → (i : Fin m) → Rel3 (M zero) (M (suc i)) (transOfRows M (suc i))
    transOfRowsIndRel3 {m = suc m} M = enumElim _ _ ≤-refl refl (transOfRowsIndRel3-helper _ m ≤-refl M)

  module _
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indRel : (M : FinMatrix A 2 n) → Rel (M zero) (M one) → M zero ≡ T M zero) where

    transOfRowsIndRelInv-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      → M zero ≡ transOfRows-helper m k p M zero
    transOfRowsIndRelInv-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndRelInv-helper (suc m) 0 p M h = indRel _ (h _)
    transOfRowsIndRelInv-helper (suc m) (suc k) p M h =
      let inv₁ = transOfRowsIndRelInv-helper (suc m) k _ M h
          inv₂ = transOfRows-invariance (suc m) k _ M (suc k) p (≤-refl) in
        transOfRowsIndRelInv-helper (suc m) k _ M h
      ∙ indRel _ (transport (λ t → Rel (inv₁ t) (inv₂ t)) (h _))

    transOfRowsIndRelInv :
        (M : FinMatrix A (suc m) n)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      →  M zero ≡ transOfRows M zero
    transOfRowsIndRelInv {m = 0} M _ = refl
    transOfRowsIndRelInv {m = suc m} = transOfRowsIndRelInv-helper _ m ≤-refl

  module _
    (P : FinVec A n → Type ℓ)
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indPRel : (M : FinMatrix A 2 n) → P (M zero) → Rel (M zero) (M one) → M zero ≡ T M zero) where

    transOfRowsIndPRelInv-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      → M zero ≡ transOfRows-helper m k p M zero
    transOfRowsIndPRelInv-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndPRelInv-helper (suc m) 0 p M q h = indPRel _ q (h _)
    transOfRowsIndPRelInv-helper (suc m) (suc k) p M q h =
      let inv₁ = transOfRowsIndPRelInv-helper (suc m) k _ M q h
          inv₂ = transOfRows-invariance (suc m) k _ M (suc k) p (≤-refl) in
        transOfRowsIndPRelInv-helper (suc m) k _ M q h
      ∙ indPRel _
          (transport (λ t → P (inv₁ t)) q)
          (transport (λ t → Rel (inv₁ t) (inv₂ t)) (h _))

    transOfRowsIndPRelInv :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      → M zero ≡ transOfRows M zero
    transOfRowsIndPRelInv {m = 0} M _ _ = refl
    transOfRowsIndPRelInv {m = suc m} = transOfRowsIndPRelInv-helper _ m ≤-refl

  module _
    (P : FinVec A n → Type ℓ)
    (indP₀ : (M : FinMatrix A 2 n) → P (M zero) → P (M one) → P (T M zero))
    (indP₁ : (M : FinMatrix A 2 n) → P (M zero) → P (M one) → P (T M one )) where

    transOfRowsIndP₀-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      → P (transOfRows-helper m k p M zero)
    transOfRowsIndP₀-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndP₀-helper (suc m) 0 p M q q' = indP₀ _ q (q' _)
    transOfRowsIndP₀-helper (suc m) (suc k) p M q q' =
      let inv = transOfRows-invariance (suc m) k _ M (suc k) p (≤-refl)  in
      indP₀ _
        (transOfRowsIndP₀-helper (suc m) k _ M q q')
        (transport (λ t → P (inv t)) (q' _))

    transOfRowsIndP₁-helper :
        (m k : ℕ)(p : k < m)
      → (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      → (l : ℕ)(q : l < m)(q' : l ≤ k)
      → P (transOfRows-helper m k p M (suc (enum l q)))
    transOfRowsIndP₁-helper 0 _ p = Empty.rec (¬-<-zero p)
    transOfRowsIndP₁-helper (suc m) 0 p M h h' l q q' =
      let sk≡sl = cong suc (enumExt p q (sym (≤0→≡0 q'))) in
      subst P (λ i → transOfRows-helper _ _ p M (sk≡sl i)) (indP₁ _ h (h' _))
    transOfRowsIndP₁-helper (suc m) (suc k) p M s s' l q q' = helper (biEq? _ _)
      where
        helper : (h : biEq (enum _ p) (enum l q))
          → P (transOf2Rows-helper _ _ h (transOfRows-helper (suc m) k (suc-< p) M))
        helper (eq  r) =
          let inv = transOfRows-invariance (suc m) k _ M (suc k) p (≤-refl)  in
          indP₁ _
            (transOfRowsIndP₀-helper (suc m) k _ M s s')
            (transport (λ t → P (inv t)) (s' _))
        helper (¬eq r) = transOfRowsIndP₁-helper _ _ (suc-< p) M s s' l q (≤-helper p q q' r)

    transOfRowsIndP₀ :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      → P (transOfRows M zero)
    transOfRowsIndP₀ {m = 0} M p _ = p
    transOfRowsIndP₀ {m = suc m} = transOfRowsIndP₀-helper _ m ≤-refl

    transOfRowsIndP₁ :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      →  (i : Fin m) → P (transOfRows M (suc i))
    transOfRowsIndP₁ {m = 0} M _ q = q
    transOfRowsIndP₁ {m = suc m} M p q =
      enumElim _ _ ≤-refl refl (transOfRowsIndP₁-helper _ m ≤-refl M p q)


-- Row transformation of linear coefficient matrices

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.Matrix.CommRingCoefficient

module LinearTransformation (𝓡 : CommRing ℓ) where

  private
    R = 𝓡 .fst
    𝑹 = CommRing→Ring 𝓡
    AbR = Ring→AbGroup 𝑹

  open CommRingStr       (𝓡 .snd) renaming ( is-set to isSetR )
  open CommRingTheory     𝓡
  open RingTheory         𝑹
  open KroneckerDelta     𝑹
  open Sum                𝑹

  open Coefficient        𝓡

  ∑helper : (V : FinVec R m)(x : R)(j : Fin m) → x · V j ≡ ∑ (λ i → (x · δ j i) · V i)
  ∑helper V x j =
      (λ t → x · ∑Mul1r _ V j (~ t))
    ∙ ∑Mulrdist x (λ i → δ j i · V i)
    ∙ (λ t → ∑ (λ i → ·Assoc x (δ j i) (V i) t))

  diagδ : (i j : Fin m)(p : i ≡ j) → δ i j ≡ 1r
  diagδ zero zero _ = refl
  diagδ zero (suc _) p = Empty.rec (znotsFin p)
  diagδ (suc _) zero p = Empty.rec (snotzFin p)
  diagδ (suc m) (suc n) p = diagδ _ _ (injSucFin p)

  skewδ : (i j : Fin m)(p : ¬ i ≡ j) → δ i j ≡ 0r
  skewδ zero zero p = Empty.rec (p refl)
  skewδ zero (suc _) _ = refl
  skewδ (suc _) zero _ = refl
  skewδ (suc m) (suc n) p = skewδ _ _ (λ r → p (cong suc r))

  module _
    (M : Mat 2 2)(i₀ : Fin m) where

    transRowMat-helper : (i : Fin m) → (p : biEq i₀ i) → FinVec R (suc m)
    transRowMat-helper i (eq  _) zero = M one zero
    transRowMat-helper i (¬eq _) zero = 0r
    transRowMat-helper i (eq  _) (suc j) = M one one · δ i₀ j
    transRowMat-helper i (¬eq _) (suc j) = δ i j

    transRowMat : Mat (suc m) (suc m)
    transRowMat zero zero = M zero zero
    transRowMat zero (suc j) = M zero one · δ i₀ j
    transRowMat (suc i) = transRowMat-helper i (biEq? _ _)

    transRowMatᵗ-helper : (i : Fin (suc m))(j : Fin m) → (p : biEq i₀ j) → R
    transRowMatᵗ-helper zero j (eq  _) = M zero one
    transRowMatᵗ-helper zero j (¬eq _) = 0r
    transRowMatᵗ-helper (suc i) j (eq  _) = M one one · δ i₀ i
    transRowMatᵗ-helper (suc i) j (¬eq _) = δ i j

    transRowMatᵗ : Mat (suc m) (suc m)
    transRowMatᵗ zero zero = M zero zero
    transRowMatᵗ (suc i) zero = M one zero · δ i₀ i
    transRowMatᵗ i (suc j) = transRowMatᵗ-helper i j (biEq? _ _)

    private
      transRowMat≡Matᵗ-suc-zero :
          (i : Fin m)(p : biEq i₀ i)
        → transRowMat-helper i p zero ≡ transRowMatᵗ (suc i) zero
      transRowMat≡Matᵗ-suc-zero i (eq  p) = sym (·Rid _) ∙ (λ t → M one zero · diagδ _ _ p (~ t))
      transRowMat≡Matᵗ-suc-zero i (¬eq p) = sym (0RightAnnihilates _) ∙ (λ t → M one zero · skewδ _ _ p (~ t))

      transRowMat≡Matᵗ-zero-suc :
          (j : Fin m)(p : biEq i₀ j)
        → transRowMat zero (suc j) ≡ transRowMatᵗ-helper zero j p
      transRowMat≡Matᵗ-zero-suc j (eq  p) = (λ t → M zero one · diagδ _ _ p t) ∙ ·Rid _
      transRowMat≡Matᵗ-zero-suc j (¬eq p) = (λ t → M zero one · skewδ _ _ p t) ∙ 0RightAnnihilates _

      transRowMat≡Matᵗ-suc-suc :
          (i j : Fin m)(p : biEq i₀ i)(q : biEq i₀ j)
        → transRowMat-helper i p (suc j) ≡ transRowMatᵗ-helper (suc i) j q
      transRowMat≡Matᵗ-suc-suc i j (eq  p) (eq  q) = (λ t → M one one · δ i₀ ((sym q ∙ p) t))
      transRowMat≡Matᵗ-suc-suc i j (¬eq p) (eq  q) =
        skewδ _ _ helper ∙ sym (0RightAnnihilates _) ∙ (λ t → M one one · skewδ _ _ p (~ t))
        where helper : ¬ i ≡ j
              helper r = p (q ∙ sym r)
      transRowMat≡Matᵗ-suc-suc i j (eq  p) (¬eq q) =
        (λ t → M one one · skewδ _ _ q t) ∙ 0RightAnnihilates _ ∙ sym (skewδ _ _ helper)
        where helper : ¬ i ≡ j
              helper r = q (p ∙ r)
      transRowMat≡Matᵗ-suc-suc i j (¬eq p) (¬eq q) = refl

    transRowMat≡Matᵗ : transRowMat ≡ transRowMatᵗ
    transRowMat≡Matᵗ t zero zero = M zero zero
    transRowMat≡Matᵗ t (suc i) zero = transRowMat≡Matᵗ-suc-zero i (biEq? _ _) t
    transRowMat≡Matᵗ t zero (suc j) = transRowMat≡Matᵗ-zero-suc j (biEq? _ _) t
    transRowMat≡Matᵗ t (suc i) (suc j) = transRowMat≡Matᵗ-suc-suc i j (biEq? _ _) (biEq? _ _) t


    transRow-helper : Mat (suc m) (suc n) → (i : Fin m)(p : biEq i₀ i) → FinVec R (suc n)
    transRow-helper N i (eq  _) = (M ⋆ takeRow i₀ N) one
    transRow-helper N i (¬eq _) = N (suc i)

    transRow : Mat (suc m) (suc n) → Mat (suc m) (suc n)
    transRow N zero = (M ⋆ takeRow i₀ N) zero
    transRow N (suc i) = transRow-helper N i (biEq? _ _)

    module _
      (N : Mat (suc m) (suc n)) where

      private
        transRow⋆-suc-helper :
            (i : Fin m)(p : biEq i₀ i)(j : Fin (suc n))
          →   transRow-helper N i p j
            ≡ ∑(λ l → transRowMat-helper i p l · N l j)
        transRow⋆-suc-helper i (eq  p) j =
            mul2 M (takeRow i₀ N) _ _
          ∙ (λ t → M one zero · N zero j + ∑helper (λ l → N (suc l) j) (M one one) i₀ t)
        transRow⋆-suc-helper i (¬eq p) j =
          helper _ _ ∙ (λ t → 0r · N zero j + ∑Mul1r _ (λ l → N (suc l) j) i (~ t))
          where helper : (x y : R) → y ≡ 0r · x + y
                helper = solve 𝓡

      transRow⋆-zero-helper : transRow N zero ≡ (transRowMat ⋆ N) zero
      transRow⋆-zero-helper t j =
          (mul2 M (takeRow i₀ N) _ _
        ∙ (λ t → M zero zero · N zero j + ∑helper (λ i → N (suc i) j) (M zero one) i₀ t)) t

      transRow⋆ : transRow N ≡ transRowMat ⋆ N
      transRow⋆ t zero = transRow⋆-zero-helper t
      transRow⋆ t (suc i) j = transRow⋆-suc-helper i (biEq? _ _) j t

  module _
    (i₀ : Fin m) where

    transRowMat𝟙-helper : (i : Fin m) → (p : biEq i₀ i) → transRowMat-helper 𝟙 i₀ i p ≡ 𝟙 (suc i)
    transRowMat𝟙-helper i (eq  _) t zero = 0r
    transRowMat𝟙-helper i (¬eq _) t zero = 0r
    transRowMat𝟙-helper i (eq  p) t (suc j) = (·Lid _ ∙ (λ t → δ (p t) j)) t
    transRowMat𝟙-helper i (¬eq _) t (suc j) = δ i j

    transRowMat𝟙 : transRowMat 𝟙 i₀ ≡ 𝟙
    transRowMat𝟙 t zero zero = 1r
    transRowMat𝟙 t zero (suc j) = 0LeftAnnihilates (δ i₀ j) t
    transRowMat𝟙 t (suc i) = transRowMat𝟙-helper i (biEq? _ _) t

  module _
    (M N : Mat 2 2)(i₀ : Fin m) where

    private
      ∑helper1 : (x a b : R) → x + ∑(λ l → (a · δ i₀ l) · (b · δ i₀ l)) ≡ x + a · b
      ∑helper1 x a b =
          (λ t → x + ∑(λ l → helper a b (δ i₀ l) (δ i₀ l) t))
        ∙ (λ t → x + ∑Mul1r _ (λ l → (δ i₀ l · (a · b))) i₀ t)
        ∙ (λ t → x + diagδ i₀ i₀ refl t · (a · b))
        ∙ (λ t → x + ·Lid (a · b) t)
        where helper : (a b x y : R) → (a · x) · (b · y) ≡ x · (y · (a · b))
              helper = solve 𝓡

      ∑helper2 : (i : Fin m)(p : ¬ i₀ ≡ i)(a b : R) → 0r · a + ∑ (λ l → δ i l · (b · δ i₀ l)) ≡ 0r
      ∑helper2 i p a b =
          (λ t → 0r · a + ∑Mul1r _ (λ l → b · δ i₀ l) i t)
        ∙ (λ t → 0r · a + b · skewδ _ _ p t)
        ∙ helper _ _
        where helper : (a b : R) → 0r · a + b · 0r ≡ 0r
              helper = solve 𝓡

      ∑helper2' : (j : Fin m)(p : ¬ i₀ ≡ j)(a b : R) → a · 0r + ∑ (λ l → (b · δ i₀ l) · δ l j) ≡ 0r
      ∑helper2' j p a b =
          (λ t → a · 0r + ∑Mulr1 _ (λ l → b · δ i₀ l) j t)
        ∙ (λ t → a · 0r + b · skewδ _ _ p t)
        ∙ helper _ _
        where helper : (a b : R) → a · 0r + b · 0r ≡ 0r
              helper = solve 𝓡

      ∑helper3 : (i j : Fin m) → 0r · 0r + ∑ (λ l → δ i l · δ l j) ≡ δ i j
      ∑helper3 i j =
          (λ t → 0r · 0r + ∑Mulr1 _ (δ i) j t)
        ∙ helper _
        where helper : (a : R) → 0r · 0r + a ≡ a
              helper = solve 𝓡

      ⋆-helper-zero-zero :
          (transRowMat M i₀ ⋆ transRowMatᵗ N i₀) zero zero
        ≡ transRowMat (M ⋆ N) i₀ zero zero
      ⋆-helper-zero-zero = ∑helper1 _ _ _ ∙ sym (mul2 M N _ _)

      ⋆-helper-zero-suc : (j : Fin m)(p : biEq i₀ j)
        → ∑ (λ l → transRowMat M i₀ zero l · transRowMatᵗ-helper N i₀ l j p)
        ≡ transRowMat (M ⋆ N) i₀ zero (suc j)
      ⋆-helper-zero-suc _ (eq  p) =
          ∑helper1 _ _ _
        ∙ sym (mul2 M N _ _) ∙ sym (·Rid _)
        ∙ (λ t → (M ⋆ N) zero one · diagδ _ _ p (~ t))
      ⋆-helper-zero-suc _ (¬eq p) =
          ∑helper2' _ p _ _
        ∙ sym (0RightAnnihilates _)
        ∙ (λ t → (M ⋆ N) zero one · skewδ _ _ p (~ t))

      ⋆-helper-suc-zero : (i : Fin m)(p : biEq i₀ i)
        → ∑ (λ l → transRowMat-helper M i₀ i p l · transRowMatᵗ N i₀ l zero)
        ≡ transRowMat-helper (M ⋆ N) i₀ i p zero
      ⋆-helper-suc-zero _ (eq  p) = ∑helper1 _ _ _ ∙ sym (mul2 M N _ _)
      ⋆-helper-suc-zero _ (¬eq p) = ∑helper2 _ p _ _

      ⋆-helper-suc-suc : (i j : Fin m)(p : biEq i₀ i)(q : biEq i₀ j)
        → ∑ (λ l → transRowMat-helper M i₀ i p l · transRowMatᵗ-helper N i₀ l j q)
        ≡ transRowMat-helper (M ⋆ N) i₀ i p (suc j)
      ⋆-helper-suc-suc _ _ (eq  p) (eq  q) =
          ∑helper1 _ _ _
        ∙ sym (mul2 M N _ _) ∙ sym (·Rid _)
        ∙ (λ t → (M ⋆ N) one one · diagδ _ _ q (~ t))
      ⋆-helper-suc-suc _ _ (eq  p) (¬eq q) =
          ∑helper2' _ q _ _
        ∙ sym (0RightAnnihilates _)
        ∙ (λ t → (M ⋆ N) one one · skewδ _ _ q (~ t))
      ⋆-helper-suc-suc _ _ (¬eq p) (eq  q) = ∑helper2 _ p _ _ ∙ sym (skewδ _ _ (λ r → p (q ∙ sym r)))
      ⋆-helper-suc-suc i j (¬eq p) (¬eq q) = ∑helper3 i j

    ⋆TransRowMatᵗ : (transRowMat M i₀ ⋆ transRowMatᵗ N i₀) ≡ transRowMat (M ⋆ N) i₀
    ⋆TransRowMatᵗ t zero zero = ⋆-helper-zero-zero t
    ⋆TransRowMatᵗ t (suc i) zero = ⋆-helper-suc-zero i (biEq? _ _) t
    ⋆TransRowMatᵗ t zero (suc j) = ⋆-helper-zero-suc j (biEq? _ _) t
    ⋆TransRowMatᵗ t (suc i) (suc j) = ⋆-helper-suc-suc i j (biEq? _ _) (biEq? _ _) t

    ⋆TransRowMat : transRowMat M i₀ ⋆ transRowMat N i₀ ≡ transRowMat (M ⋆ N) i₀
    ⋆TransRowMat =
      subst (λ K → transRowMat M i₀ ⋆ K ≡ transRowMat (M ⋆ N) i₀)
        (sym (transRowMat≡Matᵗ N i₀)) ⋆TransRowMatᵗ

  -- Invertible linear transformation

  module _
    (M : Mat 2 2)(i₀ : Fin m)
    (isInvM : isInv M) where

    isInvTransRowMat : isInv (transRowMat M i₀)
    isInvTransRowMat .fst = transRowMat (isInvM .fst) i₀
    isInvTransRowMat .snd .fst =
      ⋆TransRowMat _ _ i₀ ∙ (λ t → transRowMat (isInvM .snd .fst t) i₀) ∙ transRowMat𝟙 _
    isInvTransRowMat .snd .snd =
      ⋆TransRowMat _ _ i₀ ∙ (λ t → transRowMat (isInvM .snd .snd t) i₀) ∙ transRowMat𝟙 _

  record isLinear2 (T : (n : ℕ) → Mat 2 (suc n) → Mat 2 (suc n)) : Type ℓ where
    field
      transMat : {n : ℕ} → (M : Mat 2 (suc n)) → Mat 2 2
      transEq  : {n : ℕ} → (M : Mat 2 (suc n)) → T _ M ≡ transMat M ⋆ M

  record isLinear (T : (n : ℕ) → Mat (suc m) (suc n) → Mat (suc m) (suc n)) : Type ℓ where
    field
      transMat : {n : ℕ} → (M : Mat (suc m) (suc n)) → Mat (suc m) (suc m)
      transEq  : {n : ℕ} → (M : Mat (suc m) (suc n)) → T _ M ≡ transMat M ⋆ M

  open isLinear2
  open isLinear

  isLinearId : isLinear {m = m} (λ _ M → M)
  isLinearId .transMat _ = 𝟙
  isLinearId .transEq  _ = sym (⋆lUnit _)

  isInvId : (M : Mat (suc m) (suc n)) → isInv (isLinearId .transMat M)
  isInvId _ = isInv𝟙

  module _
    {T₁ : (n : ℕ) → Mat (suc m) (suc n) → Mat (suc m) (suc n)}
    {T₂ : (n : ℕ) → Mat (suc m) (suc n) → Mat (suc m) (suc n)}
    (isLinearT₁ : isLinear T₁)
    (isLinearT₂ : isLinear T₂) where

    isLinearComp : isLinear (λ n M → T₂ _ (T₁ _ M))
    isLinearComp .transMat M =
      let T₁M = isLinearT₁ .transMat M in
      isLinearT₂ .transMat (T₁ _ M) ⋆ T₁M
    isLinearComp .transEq  M =
        isLinearT₂ .transEq _
      ∙ (λ t → isLinearT₂ .transMat (T₁ _ M) ⋆ (isLinearT₁ .transEq M t))
      ∙ ⋆Assoc (isLinearT₂ .transMat _) (isLinearT₁ .transMat M) M

    module _
      (isInvT₁ : (M : Mat (suc m) (suc n)) → isInv (isLinearT₁ .transMat M))
      (isInvT₂ : (M : Mat (suc m) (suc n)) → isInv (isLinearT₂ .transMat M)) where

      isInvComp : (M : Mat (suc m) (suc n)) → isInv (isLinearComp .transMat M)
      isInvComp M =
        let T₁M = isLinearT₁ .transMat M in
        isInv⋆ {M = isLinearT₂ .transMat (T₁ _ M)} {M' = T₁M} (isInvT₂ (T₁ _ M)) (isInvT₁ M)

    module _
      (P : FinVec R (suc n) → Type ℓ)
      (indP : (M : Mat (suc m) (suc n)) → P (M zero) → P (T₁ _ M zero))
      (isInvT₁ : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearT₁ .transMat M))
      (isInvT₂ : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearT₂ .transMat M)) where

      isInvCompInd : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearComp .transMat M)
      isInvCompInd M p =
        let T₁M = isLinearT₁ .transMat M in
        isInv⋆ {M = isLinearT₂ .transMat (T₁ _ M)} {M' = T₁M} (isInvT₂ (T₁ _ M) (indP _ p)) (isInvT₁ M p)


  module _
    (T : (n : ℕ) → Mat 2 (suc n) → Mat 2 (suc n))
    (isLinear2T : isLinear2 T) where

    isLinearTransOf2Rows-helper-helper :
        (M : Mat (suc m) (suc n))(i j : Fin m)(p : biEq i j)
      → transOf2Rows-helper (T n) i j p M ≡ transRow-helper (isLinear2T .transMat (takeRow i M)) i M j p
    isLinearTransOf2Rows-helper-helper M i j (eq  _) t = isLinear2T .transEq (takeRow i M) t one
    isLinearTransOf2Rows-helper-helper M i j (¬eq _) = refl

    isLinearTransOf2Rows-helper :
        (M : Mat (suc m) (suc n))(i : Fin m)
      → transOf2Rows (T _) M i ≡ transRow (isLinear2T .transMat (takeRow i M)) i M
    isLinearTransOf2Rows-helper {m = suc m} M i t zero = isLinear2T .transEq (takeRow i M) t zero
    isLinearTransOf2Rows-helper {m = suc m} M i t (suc j) = isLinearTransOf2Rows-helper-helper M i j (biEq? _ _) t

    isLinearTransOf2Rows : (i : Fin m) → isLinear (λ n M → transOf2Rows (T n) M i)
    isLinearTransOf2Rows i .transMat M = transRowMat (isLinear2T .transMat (takeRow i M)) i
    isLinearTransOf2Rows i .transEq  M = isLinearTransOf2Rows-helper M i ∙ transRow⋆ _ i M


    isLinearTransOfRows-helper :
        (m k : ℕ)(p : k < m)
      → isLinear {m = m} (λ n M → transOfRows-helper (T n) m k p M)
    isLinearTransOfRows-helper 0 _ p = Empty.rec (¬-<-zero p)
    isLinearTransOfRows-helper (suc m) 0 _ = isLinearTransOf2Rows _
    isLinearTransOfRows-helper (suc m) (suc k) p =
      isLinearComp (isLinearTransOfRows-helper (suc m) k (suc-< p)) (isLinearTransOf2Rows _)

    isLinearTransOfRows : isLinear {m = m} (λ n M → transOfRows (T n) M)
    isLinearTransOfRows {m = 0} = isLinearId
    isLinearTransOfRows {m = suc m} = isLinearTransOfRows-helper _ m ≤-refl

    module _
      (isInvT : (n : ℕ)(M : Mat 2 (suc n)) → isInv (isLinear2T .transMat M)) where

      isInvTransOf2Rows :
        (i : Fin m)(M : Mat (suc m) (suc n)) → isInv (isLinearTransOf2Rows i .transMat M)
      isInvTransOf2Rows i M = isInvTransRowMat _ _ (isInvT _ _)


      isInvTransOfRows-helper :
          (m k : ℕ)(p : k < m)
        → (M : Mat (suc m) (suc n))
        → isInv (isLinearTransOfRows-helper m k p .transMat M)
      isInvTransOfRows-helper 0 _ p = Empty.rec (¬-<-zero p)
      isInvTransOfRows-helper (suc m) 0 _ = isInvTransOf2Rows _
      isInvTransOfRows-helper (suc m) (suc k) p =
        isInvComp
          (isLinearTransOfRows-helper (suc m) k (suc-< p)) (isLinearTransOf2Rows _)
          (isInvTransOfRows-helper (suc m) k (suc-< p)) (isInvTransOf2Rows _)

      isInvTransOfRows : (M : Mat (suc m) (suc n)) → isInv (isLinearTransOfRows .transMat M)
      isInvTransOfRows {m = 0} = isInvId
      isInvTransOfRows {m = suc m} = isInvTransOfRows-helper _ m ≤-refl

    module _
      (P : FinVec R (suc n) → Type ℓ)
      (indP : (M : Mat 2 (suc n)) → P (M zero) → P (T _ M zero))
      (isInvT : (M : Mat 2 (suc n)) → P (M zero) → isInv (isLinear2T .transMat M)) where

      isInvTransOf2RowsInd :
        (i : Fin m)(M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearTransOf2Rows i .transMat M)
      isInvTransOf2RowsInd i M p = isInvTransRowMat _ _ (isInvT _ p)


      isInvTransOfRowsInd-helper :
          (m k : ℕ)(p : k < m)
        → (M : Mat (suc m) (suc n))
        → P (M zero)
        → isInv (isLinearTransOfRows-helper m k p .transMat M)
      isInvTransOfRowsInd-helper 0 _ p = Empty.rec (¬-<-zero p)
      isInvTransOfRowsInd-helper (suc m) 0 _ = isInvTransOf2RowsInd _
      isInvTransOfRowsInd-helper (suc m) (suc k) p =
        isInvCompInd
          (isLinearTransOfRows-helper (suc m) k (suc-< p)) (isLinearTransOf2Rows _)
          P (transOfRowsIndP-helper (T _) P indP _ k (suc-< p))
          (isInvTransOfRowsInd-helper (suc m) k (suc-< p)) (isInvTransOf2RowsInd _)

      isInvTransOfRowsInd :
        (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearTransOfRows .transMat M)
      isInvTransOfRowsInd {m = 0} M _ = isInvId M
      isInvTransOfRowsInd {m = suc m} = isInvTransOfRowsInd-helper _ m ≤-refl
