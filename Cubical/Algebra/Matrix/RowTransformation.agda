{-

Technical results about row transformation applied to matrices

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix.RowTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.FinData renaming (znots to znotsFin ; snotz to snotzFin)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Matrix
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Matrix.CommRingCoefficient

private
  variable
    ℓ : Level
    A : Type ℓ
    m n k l : ℕ

takeRows : FinMatrix A (suc (suc m)) n → FinMatrix A 2 n
takeRows M zero = M zero
takeRows M one  = M one

takeRowsᶜ : FinMatrix A (suc (suc m)) n → FinMatrix A (suc m) n
takeRowsᶜ M zero    = M zero
takeRowsᶜ M (suc i) = M (suc (suc i))

combRows : FinMatrix A (suc (suc m)) n → FinMatrix A 2 n → FinMatrix A (suc m) n
combRows M M₀ zero    = M₀ zero
combRows M M₀ (suc i) = M  (suc (suc i))

shufRows : FinMatrix A 2 n → FinMatrix A (suc m) n → FinMatrix A (suc (suc m)) n
shufRows M₀ M₁ zero = M₁ zero
shufRows M₀ M₁ one  = M₀ one
shufRows M₀ M₁ (suc (suc i)) = M₁ (suc i)

module _
  (T₀ : FinMatrix A 2 n → FinMatrix A 2 n)
  (M  : FinMatrix A (suc (suc m)) n) where

  private
    M₀ = T₀ (takeRows M)

  takeTrans : FinMatrix A (suc (suc m)) n
  takeTrans zero = M₀ zero
  takeTrans one  = M₀ one
  takeTrans (suc (suc i)) = M (suc (suc i))

module _
  (T₁ : FinMatrix A (suc m) n → FinMatrix A (suc m) n)
  (M  : FinMatrix A (suc (suc m)) n) where

  private
    M₁ = T₁ (takeRowsᶜ M)

  combTrans : FinMatrix A (suc (suc m)) n
  combTrans zero = M₁ zero
  combTrans one  = M  one
  combTrans (suc (suc i)) = M₁ (suc i)

module _
  (T₀ : FinMatrix A 2 n → FinMatrix A 2 n)
  (T₁ : FinMatrix A (suc m) n → FinMatrix A (suc m) n)
  (M  : FinMatrix A (suc (suc m)) n) where

  private
    M₀ = T₀ (takeRows M)
    M₁ = T₁ (combRows M M₀)

    helper : takeRowsᶜ (takeTrans T₀ M) ≡ combRows M M₀
    helper t zero    = M₀ zero
    helper t (suc i) = M (suc (suc i))

  takeCombShufRows : FinMatrix A (suc (suc m)) n
  takeCombShufRows = shufRows M₀ M₁

  takeCombShufEquiv : combTrans T₁ (takeTrans T₀ M) ≡ takeCombShufRows
  takeCombShufEquiv t zero = T₁ (helper t) zero
  takeCombShufEquiv t one  = M₀ one
  takeCombShufEquiv t (suc (suc i)) = T₁ (helper t) (suc i)

-- The iterated row transformation

module _
  (T : FinMatrix A 2 n → FinMatrix A 2 n) where

  transRows : FinMatrix A (suc m) n → FinMatrix A (suc m) n
  transRows {m = 0} M = M
  transRows {m = suc m} = takeCombShufRows T transRows

  -- Several induction principle to prove properties after transformation

  module _
    (invRow : (M : FinMatrix A 2 n) → M zero ≡ T M zero) where

    invRow₀ : (M : FinMatrix A (suc m) n) → M zero ≡ transRows M zero
    invRow₀ {m = 0}     _ = refl
    invRow₀ {m = suc m} M = invRow _ ∙ invRow₀ (combRows M _)

  module _
    (P : FinVec A n → Type ℓ)
    (indP : (M : FinMatrix A 2 n) → P (M zero) → P (T M zero)) where

    transRowsIndP : (M : FinMatrix A (suc m) n) → P (M zero) → P (transRows M zero)
    transRowsIndP {m = 0} _ h = h
    transRowsIndP {m = suc m} M h = transRowsIndP (combRows M _) (indP _ h)

  module _
    (P : FinVec A n → Type ℓ)
    (indP : (M : FinMatrix A 2 n) → P (T M one)) where

    transRowsIndP' : (M : FinMatrix A (suc m) n) → (i : Fin m) → P (transRows M (suc i))
    transRowsIndP' {m = suc m} M zero    = indP _
    transRowsIndP' {m = suc m} M (suc i) = transRowsIndP' _ i

  module _
    (Q : FinVec A n → Type ℓ)
    (P : FinVec A n → Type ℓ)
    (indQ : (M : FinMatrix A 2 n) → Q (M zero) → Q (T M zero))
    (indP : (M : FinMatrix A 2 n) → Q (M zero) → P (T M one )) where

    transRowsIndPQ : (M : FinMatrix A (suc m) n) → Q (M zero) → (i : Fin m) → P (transRows M (suc i))
    transRowsIndPQ {m = suc m} M p zero    = indP _ p
    transRowsIndPQ {m = suc m} M p (suc i) = transRowsIndPQ _ (indQ _ p) i

  module _
    (Q : FinVec A n → Type ℓ)
    (P : FinVec A n → Type ℓ)
    (indQ : (M : FinMatrix A 2 n) → Q (M zero) → Q (T M zero))
    (indP : (M : FinMatrix A 2 n) → P (M one ) → Q (T M zero)) where

    transRowsIndPQ' : (M : FinMatrix A (suc m) n) → (i : Fin m) → P (M (suc i)) → Q (transRows M zero)
    transRowsIndPQ' {m = suc m} M zero    p = transRowsIndP Q indQ (combRows M _) (indP _ p)
    transRowsIndPQ' {m = suc m} M (suc i) p = transRowsIndPQ' (combRows M _) _ p

  module _
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indRel : (M : FinMatrix A 2 n) → Rel (M one) (T M one)) where

    transRowsIndRel : (M : FinMatrix A (suc m) n) → (i : Fin m) → Rel (M (suc i)) (transRows M (suc i))
    transRowsIndRel {m = suc m} M zero    = indRel _
    transRowsIndRel {m = suc m} M (suc i) = transRowsIndRel _ i

  module _
    (Rel3 : FinVec A n → FinVec A n → FinVec A n → Type ℓ)
    (invRow  : (M : FinMatrix A 2 n) → M zero ≡ T M zero)
    (indRel3 : (M : FinMatrix A 2 n) → Rel3 (M zero) (M one) (T M one)) where

    transRowsIndRel3 : (M : FinMatrix A (suc m) n) → (i : Fin m) → Rel3 (M zero) (M (suc i)) (transRows M (suc i))
    transRowsIndRel3 {m = suc m} M zero    = indRel3 _
    transRowsIndRel3 {m = suc m} M (suc i) =
      subst (λ V → Rel3 V (M (suc (suc i)))
        (transRows M (suc (suc i)))) (sym (invRow _)) (transRowsIndRel3 _ i)

  module _
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indRel : (M : FinMatrix A 2 n) → Rel (M zero) (M one) → M zero ≡ T M zero) where

    transRowsIndRelInv :
        (M : FinMatrix A (suc m) n)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      →  M zero ≡ transRows M zero
    transRowsIndRelInv {m = 0}     _ _   = refl
    transRowsIndRelInv {m = suc m} M rel =
      let invRow = indRel _ (rel zero)
          rel₁ = (λ i → subst (λ V → Rel V (M (suc (suc i)))) invRow (rel (suc i)))
      in  invRow ∙ transRowsIndRelInv _ rel₁

  module _
    (P : FinVec A n → Type ℓ)
    (Rel : FinVec A n → FinVec A n → Type ℓ)
    (indPRel : (M : FinMatrix A 2 n) → P (M zero) → Rel (M zero) (M one) → M zero ≡ T M zero) where

    transRowsIndPRelInv :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → Rel (M zero) (M (suc i)))
      → M zero ≡ transRows M zero
    transRowsIndPRelInv {m = 0}     _ _ _   = refl
    transRowsIndPRelInv {m = suc m} M p rel =
      let invRow = indPRel _ p (rel zero)
          p₁   = subst P invRow p
          rel₁ = (λ i → subst (λ V → Rel V (M (suc (suc i)))) invRow (rel (suc i)))
      in  invRow ∙ transRowsIndPRelInv _ p₁ rel₁

  module _
    (P : FinVec A n → Type ℓ)
    (indP₀ : (M : FinMatrix A 2 n) → P (M zero) → P (M one) → P (T M zero))
    (indP₁ : (M : FinMatrix A 2 n) → P (M zero) → P (M one) → P (T M one )) where

    transRowsIndP₀ :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      → P (transRows M zero)
    transRowsIndP₀ {m = 0}     _ p _ = p
    transRowsIndP₀ {m = suc m} _ p q = transRowsIndP₀ _ (indP₀ _ p (q zero)) (q ∘ suc)

    transRowsIndP₁ :
        (M : FinMatrix A (suc m) n)
      → P (M zero)
      → ((i : Fin m) → P (M (suc i)))
      →  (i : Fin m) → P (transRows M (suc i))
    transRowsIndP₁ {m = 0}     _ _ q = q
    transRowsIndP₁ {m = suc m} _ p q zero    = indP₁ _ p (q zero)
    transRowsIndP₁ {m = suc m} M p q (suc i) = transRowsIndP₁ _ (indP₀ _ p (q zero)) (q ∘ suc) i


-- Row transformation of linear coefficient matrices

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

  -- Definition of linear transformation

  record isLinear2×2 (T : Mat 2 n → Mat 2 n) : Type ℓ where
    field
      transMat : (M : Mat 2 n) → Mat 2 2
      transEq  : (M : Mat 2 n) → T M ≡ transMat M ⋆ M

  record isLinear (T : Mat m n → Mat k n) : Type ℓ where
    field
      transMat : (M : Mat m n) → Mat k m
      transEq  : (M : Mat m n) → T M ≡ transMat M ⋆ M

  open isLinear2×2
  open isLinear

  isLinearId : isLinear {m = m} {n = n} (idfun _)
  isLinearId .transMat _ = 𝟙
  isLinearId .transEq  _ = sym (⋆lUnit _)

  isInvId : (M : Mat (suc m) (suc n)) → isInv (isLinearId .transMat M)
  isInvId _ = isInv𝟙

  module _
    {T₁ : Mat (suc m) (suc n) → Mat (suc k) (suc n)}
    {T₂ : Mat (suc k) (suc n) → Mat (suc l) (suc n)}
    (isLinearT₁ : isLinear T₁)
    (isLinearT₂ : isLinear T₂) where

    isLinearComp : isLinear (T₂ ∘ T₁)
    isLinearComp .transMat M =
      let T₁M = isLinearT₁ .transMat M in
      isLinearT₂ .transMat (T₁ M) ⋆ T₁M
    isLinearComp .transEq  M =
        isLinearT₂ .transEq _
      ∙ (λ t → isLinearT₂ .transMat (T₁ M) ⋆ (isLinearT₁ .transEq M t))
      ∙ ⋆Assoc (isLinearT₂ .transMat _) (isLinearT₁ .transMat M) M

  module _
    {T₁ : Mat (suc m) (suc n) → Mat (suc m) (suc n)}
    {T₂ : Mat (suc m) (suc n) → Mat (suc m) (suc n)}
    (isLinearT₁ : isLinear T₁)
    (isLinearT₂ : isLinear T₂) where

    module _
      (isInvT₁ : (M : Mat (suc m) (suc n)) → isInv (isLinearT₁ .transMat M))
      (isInvT₂ : (M : Mat (suc m) (suc n)) → isInv (isLinearT₂ .transMat M)) where

      isInvComp : (M : Mat (suc m) (suc n)) → isInv (isLinearComp isLinearT₁ isLinearT₂ .transMat M)
      isInvComp M =
        let T₁M = isLinearT₁ .transMat M in
        isInv⋆ {M = isLinearT₂ .transMat (T₁ M)} {M' = T₁M} (isInvT₂ (T₁ M)) (isInvT₁ M)

    module _
      (P : FinVec R (suc n) → Type ℓ)
      (indP : (M : Mat (suc m) (suc n)) → P (M zero) → P (T₁ M zero))
      (isInvT₁ : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearT₁ .transMat M))
      (isInvT₂ : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearT₂ .transMat M)) where

      isInvCompInd : (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearComp isLinearT₁ isLinearT₂ .transMat M)
      isInvCompInd M p =
        let T₁M = isLinearT₁ .transMat M in
        isInv⋆ {M = isLinearT₂ .transMat (T₁ M)} {M' = T₁M} (isInvT₂ (T₁ M) (indP _ p)) (isInvT₁ M p)

  -- Linearity of row transformation

  takeTransMat : Mat 2 2 → Mat (suc (suc m)) (suc (suc m))
  takeTransMat P zero zero = P zero zero
  takeTransMat P one  zero = P one  zero
  takeTransMat P zero one  = P zero one
  takeTransMat P one  one  = P one  one
  takeTransMat _ zero (suc (suc j)) = 0r
  takeTransMat _ one  (suc (suc j)) = 0r
  takeTransMat _ (suc (suc i)) zero = 0r
  takeTransMat _ (suc (suc i)) one  = 0r
  takeTransMat _ (suc (suc i)) (suc (suc j)) = 𝟙 i j

  takeTransMat𝟙 : takeTransMat {m = m} 𝟙 ≡ 𝟙
  takeTransMat𝟙 t zero zero = 1r
  takeTransMat𝟙 t one  zero = 0r
  takeTransMat𝟙 t zero one  = 0r
  takeTransMat𝟙 t one  one  = 1r
  takeTransMat𝟙 t zero (suc (suc j)) = 0r
  takeTransMat𝟙 t one  (suc (suc j)) = 0r
  takeTransMat𝟙 t (suc (suc i)) zero = 0r
  takeTransMat𝟙 t (suc (suc i)) one  = 0r
  takeTransMat𝟙 t (suc (suc i)) (suc (suc j)) = δ i j

  module _
    (M N : Mat 2 2) where

    ⋆TakeTransMat : takeTransMat M ⋆ takeTransMat N ≡ takeTransMat {m = m} (M ⋆ N)
    ⋆TakeTransMat {m = m} t zero zero =
      M zero zero · N zero zero + (M zero one · N one zero + ∑Mul0r {n = m} (λ i → 0r) t)
    ⋆TakeTransMat {m = m} t one  zero =
      M one  zero · N zero zero + (M one one  · N one zero + ∑Mul0r {n = m} (λ i → 0r) t)
    ⋆TakeTransMat {m = m} t zero one  =
      M zero zero · N zero one  + (M zero one · N one one  + ∑Mul0r {n = m} (λ i → 0r) t)
    ⋆TakeTransMat {m = m} t one  one  =
      M one  zero · N zero one  + (M one one  · N one one  + ∑Mul0r {n = m} (λ i → 0r) t)
    ⋆TakeTransMat t zero (suc (suc j)) =
      (helper (M zero zero) (M zero one ) _ ∙ ∑Mul0r (λ i → 𝟙 i j)) t
      where helper : (a b c : R) → a · 0r + (b · 0r + c) ≡ c
            helper _ _ _ = solve! 𝓡
    ⋆TakeTransMat t one  (suc (suc j)) =
      (helper (M one  zero) (M one  one ) _ ∙ ∑Mul0r (λ i → 𝟙 i j)) t
      where helper : (a b c : R) → a · 0r + (b · 0r + c) ≡ c
            helper _ _ _ = solve! 𝓡
    ⋆TakeTransMat t (suc (suc i)) zero =
      (helper (N zero zero) (N one  zero) _ ∙ ∑Mulr0 (λ j → 𝟙 i j)) t
      where helper : (a b c : R) → 0r · a + (0r · b + c) ≡ c
            helper _ _ _ = solve! 𝓡
    ⋆TakeTransMat t (suc (suc i)) one  =
      (helper (N zero one ) (N one  one ) _ ∙ ∑Mulr0 (λ j → 𝟙 i j)) t
      where helper : (a b c : R) → 0r · a + (0r · b + c) ≡ c
            helper _ _ _ = solve! 𝓡
    ⋆TakeTransMat t (suc (suc i)) (suc (suc j)) =
        (helper _
      ∙ (λ t → ⋆lUnit 𝟙 t i j)) t
      where helper : (c : R) → 0r · 0r + (0r · 0r + c) ≡ c
            helper _ = solve! 𝓡

  module _
    (T₀ : Mat 2 (suc n) → Mat 2 (suc n))
    (isLinear2×2T₀ : isLinear2×2 T₀) where

    module _
      (M : Mat (suc (suc m)) (suc n)) where

      private
        P = isLinear2×2T₀ .transMat (takeRows M)

      takeTransEquiv : takeTrans T₀ M ≡ takeTransMat P ⋆ M
      takeTransEquiv t zero j =
        ((λ t → isLinear2×2T₀ .transEq (takeRows M) t zero j)
        ∙ mul2 P (takeRows M) _ _
        ∙ helper _ _
        ∙ (λ t → P zero zero · M zero j + (P zero one · M one j
               + ∑Mul0r (λ i → M (suc (suc i)) j) (~ t)))) t
        where helper : (a b : R) → a + b ≡ a + (b + 0r)
              helper _ _ = solve! 𝓡
      takeTransEquiv t one  j =
        ((λ t → isLinear2×2T₀ .transEq (takeRows M) t one  j)
        ∙ mul2 P (takeRows M) _ _
        ∙ helper _ _
        ∙ (λ t → P one  zero · M zero j + (P one  one · M one j
               + ∑Mul0r (λ i → M (suc (suc i)) j) (~ t)))) t
        where helper : (a b : R) → a + b ≡ a + (b + 0r)
              helper _ _ = solve! 𝓡
      takeTransEquiv t (suc (suc i)) j =
        ((λ t → ⋆lUnit (λ i j → M (suc (suc i)) j) (~ t) i j)
        ∙ helper (M zero j) (M one  j) _) t
        where helper : (a b c : R) → c ≡ 0r · a + (0r · b + c)
              helper _ _ _ = solve! 𝓡

    isLinearTakeRowsTrans : isLinear (takeTrans {m = m} T₀)
    isLinearTakeRowsTrans .transMat M = takeTransMat _
    isLinearTakeRowsTrans .transEq    = takeTransEquiv

  isInvTakeTransMat : (M : Mat 2 2)(isInvM : isInv M) → isInv (takeTransMat {m = m} M)
  isInvTakeTransMat M isInvM .fst = takeTransMat (isInvM .fst)
  isInvTakeTransMat M isInvM .snd .fst =
    ⋆TakeTransMat _ _ ∙ (λ t → takeTransMat (isInvM .snd .fst t)) ∙ takeTransMat𝟙
  isInvTakeTransMat M isInvM .snd .snd =
    ⋆TakeTransMat _ _ ∙ (λ t → takeTransMat (isInvM .snd .snd t)) ∙ takeTransMat𝟙

  combTransMat : Mat (suc m) (suc m) → Mat (suc (suc m)) (suc (suc m))
  combTransMat P zero zero = P zero zero
  combTransMat _ zero one  = 0r
  combTransMat _ one  zero = 0r
  combTransMat _ one  one  = 1r
  combTransMat P zero (suc (suc j)) = P zero (suc j)
  combTransMat _ one  (suc (suc j)) = 0r
  combTransMat P (suc (suc i)) zero = P (suc i) zero
  combTransMat _ (suc (suc i)) one  = 0r
  combTransMat P (suc (suc i)) (suc (suc j)) = P (suc i) (suc j)

  combTransMat𝟙 : combTransMat {m = m} 𝟙 ≡ 𝟙
  combTransMat𝟙 t zero zero = 1r
  combTransMat𝟙 t zero one  = 0r
  combTransMat𝟙 t one  zero = 0r
  combTransMat𝟙 t one  one  = 1r
  combTransMat𝟙 t zero (suc (suc j)) = 0r
  combTransMat𝟙 t one  (suc (suc j)) = 0r
  combTransMat𝟙 t (suc (suc i)) zero = 0r
  combTransMat𝟙 t (suc (suc i)) one  = 0r
  combTransMat𝟙 t (suc (suc i)) (suc (suc j)) = δ i j

  module _
    (M N : Mat (suc m) (suc m)) where

    ⋆CombTransMat : combTransMat M ⋆ combTransMat N ≡ combTransMat (M ⋆ N)
    ⋆CombTransMat t zero zero  =
      helper (M zero zero · N zero zero) (∑ (λ l → M zero (suc l) · N (suc l) zero)) t
      where helper : (a c : R) → a + (0r · 0r + c) ≡ a + c
            helper _ _  = solve! 𝓡
    ⋆CombTransMat t zero one  =
      (helper (M zero zero) _ ∙ ∑Mulr0 (λ j → M zero (suc j))) t
      where helper : (a c : R) → a · 0r + (0r · 1r + c) ≡ c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t one  zero =
      (helper (N zero zero) _ ∙ ∑Mul0r (λ i → N (suc i) zero)) t
      where helper : (a c : R) → 0r · a + (1r · 0r + c) ≡ c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t one  one  =
      ((λ t → 0r · 0r + (1r · 1r + ∑Mul0r {n = m} (λ i → 0r) t))
      ∙ helper) t
      where helper : 0r · 0r + (1r · 1r + 0r) ≡ 1r
            helper = solve! 𝓡
    ⋆CombTransMat t zero (suc (suc j)) =
      helper (M zero zero · N zero (suc j)) (∑ (λ l → M zero (suc l) · N (suc l) (suc j))) t
      where helper : (a c : R) → a + (0r · 0r + c) ≡ a + c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t one  (suc (suc j)) =
      (helper (N zero (suc j)) _ ∙ ∑Mul0r (λ i → N (suc i) (suc j))) t
      where helper : (a c : R) → 0r · a + (1r · 0r + c) ≡ c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t (suc (suc i)) zero =
      helper (M (suc i) zero · N zero zero) (∑ (λ l → M (suc i) (suc l) · N (suc l) zero)) t
      where helper : (a c : R) → a + (0r · 0r + c) ≡ a + c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t (suc (suc i)) one  =
      (helper (M (suc i) zero) _ ∙ ∑Mulr0 (λ j → M (suc i) (suc j))) t
      where helper : (a c : R) → a · 0r + (0r · 1r + c) ≡ c
            helper _ _ = solve! 𝓡
    ⋆CombTransMat t (suc (suc i)) (suc (suc j)) =
      helper (M (suc i) zero · N zero (suc j)) (∑ (λ l → M (suc i) (suc l) · N (suc l) (suc j))) t
      where helper : (a c : R) → a + (0r · 0r + c) ≡ a + c
            helper _ _ = solve! 𝓡

  module _
    (T₁ : Mat (suc m) (suc n) → Mat (suc m) (suc n))
    (isLinearT₁ : isLinear T₁) where

    module _
      (M : Mat (suc (suc m)) (suc n)) where

      private
        P = isLinearT₁ .transMat (takeRowsᶜ M)

      combTransEquiv : combTrans T₁ M ≡ combTransMat P ⋆ M
      combTransEquiv t zero j =
        ((λ t → isLinearT₁ .transEq (takeRowsᶜ M) t zero j)
        ∙ helper _ (M one j) _) t
        where helper : (a b c : R) → a + c ≡ a + (0r · b + c)
              helper _ _ _ = solve! 𝓡
      combTransEquiv t one  j =
          (helper _ _
        ∙ (λ t → 0r · M zero j + (1r · M one j
               + ∑Mul0r (λ i → M (suc (suc i)) j) (~ t)))) t
        where helper : (a b : R) → b ≡ 0r · a + (1r · b + 0r)
              helper _ _ = solve! 𝓡
      combTransEquiv t (suc (suc i)) j =
        ((λ t → isLinearT₁ .transEq (takeRowsᶜ M) t (suc i) j)
        ∙ helper _ (M one j) _) t
        where helper : (a b c : R) → a + c ≡ a + (0r · b + c)
              helper _ _ _ = solve! 𝓡

    isLinearCombRowsTrans : isLinear (combTrans T₁)
    isLinearCombRowsTrans .transMat M = combTransMat _
    isLinearCombRowsTrans .transEq    = combTransEquiv

  isInvCombTransMat : (M : Mat (suc m) (suc m))(isInvM : isInv M) → isInv (combTransMat M)
  isInvCombTransMat M isInvM .fst = combTransMat (isInvM .fst)
  isInvCombTransMat M isInvM .snd .fst =
    ⋆CombTransMat _ _ ∙ (λ t → combTransMat (isInvM .snd .fst t)) ∙ combTransMat𝟙
  isInvCombTransMat M isInvM .snd .snd =
    ⋆CombTransMat _ _ ∙ (λ t → combTransMat (isInvM .snd .snd t)) ∙ combTransMat𝟙

  module _
    {T₁ : Mat 2 (suc n) → Mat 2 (suc n)}
    {T₂ : Mat (suc m) (suc n) → Mat (suc m) (suc n)}
    (isLinearT₁ : isLinear2×2 T₁)
    (isLinearT₂ : isLinear    T₂) where

    private
      compL = isLinearComp (isLinearTakeRowsTrans _ isLinearT₁) (isLinearCombRowsTrans _ isLinearT₂)

    isLinearTakeCombShufRows : isLinear (takeCombShufRows {m = m} T₁ T₂)
    isLinearTakeCombShufRows .transMat   = compL .transMat
    isLinearTakeCombShufRows .transEq  M = sym (takeCombShufEquiv _ _ _) ∙ compL .transEq _

  module _
    (T : Mat 2 (suc n) → Mat 2 (suc n))
    (isLinear2×2T : isLinear2×2 T) where

    isLinearTransRows : (m : ℕ) → isLinear (transRows T {m = m})
    isLinearTransRows 0       = isLinearId
    isLinearTransRows (suc m) = isLinearTakeCombShufRows isLinear2×2T (isLinearTransRows m)

    module _
      (isInvT : (M : Mat 2 (suc n)) → isInv (isLinear2×2T .transMat M)) where

      isInvTransRows : (M : Mat (suc m) (suc n)) → isInv (isLinearTransRows _ .transMat M)
      isInvTransRows {m = 0}     _ = isInv𝟙
      isInvTransRows {m = suc m} M =
        isInv⋆ {M = combTransMat _} {M' = takeTransMat _}
               (isInvCombTransMat _ (isInvTransRows _))
               (isInvTakeTransMat _ (isInvT _))

    module _
      (P : FinVec R (suc n) → Type ℓ)
      (indP   : (M : Mat 2 (suc n)) → P (M zero) → P (T M zero))
      (isInvT : (M : Mat 2 (suc n)) → P (M zero) → isInv (isLinear2×2T .transMat M)) where

      isInvTransRowsInd :
        (M : Mat (suc m) (suc n)) → P (M zero) → isInv (isLinearTransRows _ .transMat M)
      isInvTransRowsInd {m = 0} M _ = isInvId M
      isInvTransRowsInd {m = suc m} M p =
        isInv⋆ {M = combTransMat _} {M' = takeTransMat _}
               (isInvCombTransMat _ (isInvTransRowsInd _ (indP _ p)))
               (isInvTakeTransMat _ (isInvT _ p))

  -- Some useful properties of 2-rows transformation

  symδ : (i j : Fin m) → δ i j ≡ δ j i
  symδ zero    zero    = refl
  symδ zero    (suc _) = refl
  symδ (suc _) zero    = refl
  symδ (suc i) (suc j) = symδ i j

  diagδ : (i j : Fin m)(p : i ≡ j) → δ i j ≡ 1r
  diagδ zero    zero    _ = refl
  diagδ (suc _) zero    p = Empty.rec (snotzFin p)
  diagδ zero    (suc _) p = Empty.rec (znotsFin p)
  diagδ (suc i) (suc j) p = diagδ _ _ (injSucFin p)

  skewδ : (i j : Fin m)(p : ¬ i ≡ j) → δ i j ≡ 0r
  skewδ zero    zero    p = Empty.rec (p refl)
  skewδ (suc _) zero    _ = refl
  skewδ zero    (suc _) _ = refl
  skewδ (suc i) (suc j) p = skewδ _ _ (λ r → p (cong suc r))

  diagSet : (i₀ : Fin m)(a : R) → Mat m m
  diagSet {m = suc m} zero a zero    zero    = a
  diagSet {m = suc m} zero _ (suc i) zero    = 0r
  diagSet {m = suc m} zero _ zero    (suc j) = 0r
  diagSet {m = suc m} zero _ (suc i) (suc j) = δ i j
  diagSet {m = suc m} (suc i₀) _ zero    zero    = 1r
  diagSet {m = suc m} (suc i₀) _ (suc i) zero    = 0r
  diagSet {m = suc m} (suc i₀) _ zero    (suc j) = 0r
  diagSet {m = suc m} (suc i₀) a (suc i) (suc j) = diagSet i₀ a i j

  diagSet≡diagSetᵗ : (i₀ : Fin m)(a : R) → diagSet i₀ a ≡ (diagSet i₀ a)ᵗ
  diagSet≡diagSetᵗ {m = suc m} zero a t zero    zero    = a
  diagSet≡diagSetᵗ {m = suc m} zero _ t (suc i) zero    = 0r
  diagSet≡diagSetᵗ {m = suc m} zero _ t zero    (suc j) = 0r
  diagSet≡diagSetᵗ {m = suc m} zero _ t (suc i) (suc j) = symδ i j t
  diagSet≡diagSetᵗ {m = suc m} (suc i₀) _ t zero    zero    = 1r
  diagSet≡diagSetᵗ {m = suc m} (suc i₀) _ t (suc i) zero    = 0r
  diagSet≡diagSetᵗ {m = suc m} (suc i₀) _ t zero    (suc j) = 0r
  diagSet≡diagSetᵗ {m = suc m} (suc i₀) a t (suc i) (suc j) = diagSet≡diagSetᵗ i₀ a t i j

  diagSet1≡𝟙 : (i₀ : Fin m) → diagSet i₀ 1r ≡ 𝟙
  diagSet1≡𝟙 {m = suc m} zero t zero    zero    = 1r
  diagSet1≡𝟙 {m = suc m} zero t (suc i) zero    = 0r
  diagSet1≡𝟙 {m = suc m} zero t zero    (suc j) = 0r
  diagSet1≡𝟙 {m = suc m} zero t (suc i) (suc j) = δ i j
  diagSet1≡𝟙 {m = suc m} (suc i₀) t zero    zero    = 1r
  diagSet1≡𝟙 {m = suc m} (suc i₀) t (suc i) zero    = 0r
  diagSet1≡𝟙 {m = suc m} (suc i₀) t zero    (suc j) = 0r
  diagSet1≡𝟙 {m = suc m} (suc i₀) t (suc i) (suc j) = diagSet1≡𝟙 i₀ t i j

  module _
    (a b c : R) where

    ·DiagSetˡ : (i₀ : Fin m)(i : Fin m) → a · δ i₀ i + diagSet i₀ b i i₀ · c ≡ (a + (b · c + 0r)) · δ i₀ i
    ·DiagSetˡ {m = suc m} zero     zero    = solve! 𝓡
    ·DiagSetˡ {m = suc m} (suc i₀) zero    = solve! 𝓡
    ·DiagSetˡ {m = suc m} zero     (suc j) = solve! 𝓡
    ·DiagSetˡ {m = suc m} (suc i₀) (suc j) = ·DiagSetˡ i₀ j

    ·DiagSetʳ : (i₀ : Fin m)(i : Fin m) → a · δ i₀ i + b · diagSet i₀ c i₀ i ≡ (a + (b · c + 0r)) · δ i₀ i
    ·DiagSetʳ {m = suc m} zero     zero    = solve! 𝓡
    ·DiagSetʳ {m = suc m} (suc i₀) zero    = solve! 𝓡
    ·DiagSetʳ {m = suc m} zero     (suc j) = solve! 𝓡
    ·DiagSetʳ {m = suc m} (suc i₀) (suc j) = ·DiagSetʳ i₀ j

  module _
    (a b : R) where

    ⋆DiagSet : (i₀ : Fin m) → diagSet i₀ a ⋆ diagSet i₀ b ≡ diagSet i₀ (a · b)
    ⋆DiagSet {m = suc m} zero t zero    zero    =
      ((λ t → a · b + ∑Mul0r {n = m} (λ i → 0r) t) ∙ helper _) t
      where helper : (a : R) → a + 0r ≡ a
            helper _ = solve! 𝓡
    ⋆DiagSet {m = suc m} zero t (suc i) zero    =
      ((λ t → 0r · b + ∑Mulr0 (λ j → diagSet zero a (suc i) (suc j)) t) ∙ helper _) t
      where helper : (b : R) → 0r · b + 0r ≡ 0r
            helper _ = solve! 𝓡
    ⋆DiagSet {m = suc m} zero t zero    (suc j) =
      ((λ t → a · 0r + ∑Mul0r (λ i → diagSet zero b (suc i) (suc j)) t) ∙ helper _) t
      where helper : (a : R) → a · 0r + 0r ≡ 0r
            helper _ = solve! 𝓡
    ⋆DiagSet {m = suc m} zero t (suc i) (suc j) =
      ((λ t → 0r · 0r + ∑Mulr1 _ (λ l → δ i l) j t) ∙ helper _) t
      where helper : (d : R) → 0r · 0r + d ≡ d
            helper _ = solve! 𝓡
    ⋆DiagSet {m = suc m} (suc i₀) t zero    zero    =
      ((λ t → 1r · 1r + ∑Mul0r {n = m} (λ i → 0r) t) ∙ helper) t
      where helper : 1r · 1r + 0r ≡ 1r
            helper = solve! 𝓡
    ⋆DiagSet {m = suc m} (suc i₀) t (suc i) zero    =
      ((λ t → 0r · 1r + ∑Mulr0 (λ j → diagSet (suc i₀) a (suc i) (suc j)) t) ∙ helper) t
      where helper : 0r · 1r + 0r ≡ 0r
            helper = solve! 𝓡
    ⋆DiagSet {m = suc m} (suc i₀) t zero    (suc j) =
      ((λ t → 1r · 0r + ∑Mul0r (λ i → diagSet (suc i₀) b (suc i) (suc j)) t) ∙ helper) t
      where helper : 1r · 0r + 0r ≡ 0r
            helper = solve! 𝓡
    ⋆DiagSet {m = suc m} (suc i₀) t (suc i) (suc j) =
      ((λ t → 0r · 0r + ⋆DiagSet i₀ t i j) ∙ helper _) t
      where helper : (a : R) → 0r · 0r + a ≡ a
            helper _ = solve! 𝓡

  module _
    (a b c : R) where

    +DiagSet :
        (i₀ i j : Fin m)
      → (a · δ i₀ i) · (b · δ i₀ j) + diagSet i₀ c i j ≡ diagSet i₀ (a · b + (c + 0r)) i j
    +DiagSet {m = suc m} zero zero    zero        = solve! 𝓡
    +DiagSet {m = suc m} zero (suc i) zero        = solve! 𝓡
    +DiagSet {m = suc m} zero zero    (suc j)     = solve! 𝓡
    +DiagSet {m = suc m} zero (suc i) (suc j)     = solve! 𝓡
    +DiagSet {m = suc m} (suc i₀) zero    zero    = solve! 𝓡
    +DiagSet {m = suc m} (suc i₀) (suc i) zero    = solve! 𝓡
    +DiagSet {m = suc m} (suc i₀) zero    (suc j) = solve! 𝓡
    +DiagSet {m = suc m} (suc i₀) (suc i) (suc j) = +DiagSet i₀ i j

  module _
    (M : Mat 2 2)(i₀ : Fin m) where

    trans2RowsMat : Mat (suc m) (suc m)
    trans2RowsMat zero    zero    = M zero zero
    trans2RowsMat (suc i) zero    = M one zero · δ i₀ i
    trans2RowsMat zero    (suc j) = M zero one · δ i₀ j
    trans2RowsMat (suc i) (suc j) = diagSet i₀ (M one one) i j

  module _
    (i₀ : Fin m) where

    trans2RowsMat𝟙 : trans2RowsMat 𝟙 i₀ ≡ 𝟙
    trans2RowsMat𝟙 t zero    zero    = 1r
    trans2RowsMat𝟙 t (suc i) zero    = 0LeftAnnihilates (δ i₀ i) t
    trans2RowsMat𝟙 t zero    (suc j) = 0LeftAnnihilates (δ i₀ j) t
    trans2RowsMat𝟙 t (suc i) (suc j) = diagSet1≡𝟙 i₀ t i j

  module _
    (M N : Mat 2 2)(i₀ : Fin m) where

    private
      ∑helper00 : (x a b : R) → x + ∑(λ l → (a · δ i₀ l) · (b · δ i₀ l)) ≡ x + a · b
      ∑helper00 x a b =
          (λ t → x + ∑(λ l → helper a b (δ i₀ l) (δ i₀ l) t))
        ∙ (λ t → x + ∑Mul1r _ (λ l → (δ i₀ l · (a · b))) i₀ t)
        ∙ (λ t → x + diagδ i₀ i₀ refl t · (a · b))
        ∙ (λ t → x + ·IdL (a · b) t)
        where helper : (a b x y : R) → (a · x) · (b · y) ≡ x · (y · (a · b))
              helper _ _ _ _ = solve! 𝓡

      ∑helper10 :
          (a b c : R)(K : Mat m m)(i : Fin m)
        → (a · δ i₀ i) · b + ∑ (λ l → K i l · (c · δ i₀ l)) ≡ (a · b) · δ i₀ i + K i i₀ · c
      ∑helper10 a b c K i =
          (λ t → helper1 a b (δ i₀ i) t + ∑ (λ l → helper2 (K i l) c (δ i₀ l) t))
        ∙ (λ t → (a · b) · δ i₀ i + ∑Mul1r _ (λ l → K i l · c) i₀ t)
        where helper1 : (a b c : R) → (a · c) · b ≡ (a · b) · c
              helper1 _ _ _ = solve! 𝓡
              helper2 : (a b c : R) → a · (b · c) ≡ c · (a · b)
              helper2 _ _ _ = solve! 𝓡

      ∑helper01 :
          (a b c : R)(K : Mat m m)(i : Fin m)
        → a · (b · δ i₀ i) + ∑ (λ l → (c · δ i₀ l) · K l i) ≡ (a · b) · δ i₀ i + c · K i₀ i
      ∑helper01 a b c K i =
          (λ t → helper1 a b (δ i₀ i) t + ∑ (λ l → helper2 c (K l i) (δ i₀ l) t))
        ∙ (λ t → (a · b) · δ i₀ i + ∑Mul1r _ (λ l → c · K l i) i₀ t)
        where helper1 : (a b c : R) → a · (b · c) ≡ (a · b) · c
              helper1 _ _ _ = solve! 𝓡
              helper2 : (a b c : R) → (a · c) · b ≡ c · (a · b)
              helper2 _ _ _ = solve! 𝓡

    ⋆Trans2RowsMat : trans2RowsMat M i₀ ⋆ trans2RowsMat N i₀ ≡ trans2RowsMat (M ⋆ N) i₀
    ⋆Trans2RowsMat t zero    zero    =
      (∑helper00 _ _ _ ∙ sym (mul2 M N zero zero)) t
    ⋆Trans2RowsMat t (suc i) zero    =
       (∑helper10 (M one  zero) (N zero zero)
                  (N one  zero) (diagSet i₀ (M one one)) i
      ∙ ·DiagSetˡ _ _ _ i₀ i) t
    ⋆Trans2RowsMat t zero    (suc j) =
       (∑helper01 (M zero zero) (N zero one)
                  (M zero one ) (diagSet i₀ (N one one)) j
      ∙ ·DiagSetʳ _ _ _ i₀ j) t
    ⋆Trans2RowsMat t (suc i) (suc j) =
      ((λ t → (M one zero · δ i₀ i) · (N zero one · δ i₀ j)
              + ⋆DiagSet (M one one) (N one one) i₀ t i j)
      ∙ +DiagSet _ _ _ i₀ i j) t

  isInvTrans2RowsMat : (M : Mat 2 2)(i₀ : Fin m)(isInvM : isInv M) → isInv (trans2RowsMat M i₀)
  isInvTrans2RowsMat M i₀ isInvM .fst = trans2RowsMat (isInvM .fst) i₀
  isInvTrans2RowsMat M i₀ isInvM .snd .fst =
    ⋆Trans2RowsMat _ _ _ ∙ (λ t → trans2RowsMat (isInvM .snd .fst t) i₀) ∙ trans2RowsMat𝟙 _
  isInvTrans2RowsMat M i₀ isInvM .snd .snd =
    ⋆Trans2RowsMat _ _ _ ∙ (λ t → trans2RowsMat (isInvM .snd .snd t) i₀) ∙ trans2RowsMat𝟙 _
