{-
  Define finitely generated ideals of commutative rings and
  show that they are an ideal.
  Parts of this should be reusable for explicit constructions
  of free modules over a finite set.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.FGIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat using (ℕ)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving hiding (∣)

private
  variable
    ℓ : Level

module _ (Ring@(R , str) : CommRing ℓ) (r : R) where
  infixr 5 _holds
  _holds : hProp ℓ → Type ℓ
  P holds = fst P
  open CommRingStr str
  open RingTheory (CommRing→Ring Ring)
  open Sum (CommRing→Ring Ring)

  linearCombination : {n : ℕ} → FinVec R n → FinVec R n → R
  linearCombination α V = ∑ (λ i → α i · V i)
  -- linearCombination [] [] = 0r
  -- linearCombination (c ∷ coefficients) (x ∷ l) = c · x + linearCombination coefficients l

  -- this is just (λ i → c i + c' i)
  -- coefficientSum : {n : ℕ} → Vec R n → Vec R n → Vec R n
  -- coefficientSum [] [] = []
  -- coefficientSum (x ∷ c) (y ∷ c′) = x + y ∷ coefficientSum c c′

  sumDist+ : ∀ {n : ℕ} (α β V : FinVec R n)
           → linearCombination (λ i → α i + β i) V ≡ linearCombination α V + linearCombination β V
  sumDist+ α β V = ∑Ext (λ i → ·Ldist+ (α i) (β i) (V i)) ∙ ∑Split (λ i → α i · V i) (λ i → β i · V i)
  -- sumDist+ ℕ.zero [] [] [] = solve Ring
  -- sumDist+ (ℕ.suc n) (x ∷ c) (y ∷ c′) (a ∷ l) =
  --   linearCombination (coefficientSum (x ∷ c) (y ∷ c′)) (a ∷ l)            ≡⟨ refl ⟩
  --   (x + y) · a + linearCombination (coefficientSum c c′) l                ≡⟨ step1 ⟩
  --   (x + y) · a + (linearCombination c l + linearCombination c′ l)         ≡⟨ step2 ⟩
  --   (x · a + linearCombination c l) + (y · a + linearCombination c′ l)     ≡⟨ refl ⟩
  --   linearCombination (x ∷ c) (a ∷ l) + linearCombination (y ∷ c′) (a ∷ l) ∎
  --   where
  --     step1 = cong (λ z → (x + y) · a + z) (sumDist+ n c c′ l)
  --     autoSolve : (x y a t1 t2 : R)
  --                 → (x + y) · a + (t1 + t2) ≡ (x · a + t1) + (y · a + t2)
  --     autoSolve = solve Ring
  --     step2 = autoSolve x y a _ _

  dist- : ∀ {n : ℕ} (α V : FinVec R n)
        → linearCombination (λ i → - α i) V ≡ - linearCombination α V
  dist- α V = ∑Ext (λ i → -DistL· (α i) (V i)) ∙ ∑Dist- (λ i → α i · V i)
  -- dist- ℕ.zero [] [] = solve Ring
  -- dist- (ℕ.suc n) (x ∷ c) (a ∷ l) =
  --     - x · a + linearCombination (map -_ c) l    ≡[ i ]⟨ - x · a + dist- n c l i ⟩
  --     - x · a - linearCombination c l             ≡⟨ step1 x a _ ⟩
  --     - (x · a + linearCombination c l)           ∎
  --     where step1 : (x a t1 : R) → - x · a - t1 ≡ - (x · a + t1)
  --           step1 = solve Ring

  dist0 : ∀ {n : ℕ} (V : FinVec R n)
        → linearCombination (replicateFinVec n 0r) V ≡ 0r
  dist0 {n = n} V = ∑Ext (λ i → 0LeftAnnihilates (V i)) ∙ ∑0r n
  -- dist0 ℕ.zero [] = refl
  -- dist0 (ℕ.suc n) (a ∷ l) =
  --   0r · a + linearCombination (replicate 0r) l ≡[ i ]⟨  0r · a + dist0 n l i ⟩
  --   0r · a + 0r                                 ≡⟨ step1 a ⟩
  --   0r ∎
  --   where step1 : (a : R) → 0r · a + 0r ≡ 0r
  --         step1 = solve Ring

  isLinearCombination : {n : ℕ} → FinVec R n → R → Type ℓ
  isLinearCombination V x = ∃[ α ∈ FinVec R _ ] x ≡ linearCombination α V

  {- If x and y are linear combinations of l, then (x + y) is
     a linear combination. -}
  isLinearCombination+ : {n : ℕ} {x y : R} (V : FinVec R n)
                         → isLinearCombination V x
                         → isLinearCombination V y
                         → isLinearCombination V (x + y)
  isLinearCombination+ V = map2 λ α β → (λ i → α .fst i + β .fst i)
                                       , cong₂ (_+_) (α .snd) (β .snd) ∙ sym (sumDist+ _ _ V)
    -- elim (λ _ → isOfHLevelΠ 1 (λ _ → propTruncIsProp))
    --      (λ {(cx , px) → elim (λ _ → propTruncIsProp)
    --       λ {(cy , py) →
    --         ∣  (λ i → cx i + cy i) ,
    --             (_ + _                                           ≡[ i ]⟨ px i + py i ⟩
    --              linearCombination cx V + linearCombination cy V ≡⟨ sym (sumDist+ cx cy V) ⟩
    --              linearCombination (λ i → cx i + cy i) V ∎) ∣}})

  -- {- If x is a linear combinations of l, then -x is
  --    a linear combination. -}
  isLinearCombination- : {n : ℕ} {x : R} (V : FinVec R n)
                       → isLinearCombination V x → isLinearCombination V (- x)
  isLinearCombination- V = map λ α → (λ i → - α .fst i) , cong (-_) (α .snd) ∙ sym (dist- _ V)
    -- elim (λ _ → propTruncIsProp)
    --      λ {(cx , px) → ∣ (λ i → - cx i) ,
    --                      ( - _                             ≡⟨ cong -_ px ⟩
    --                        - linearCombination cx V        ≡⟨ sym (dist-  cx V) ⟩
    --                        linearCombination (λ i → - cx i) V ∎) ∣}

  {- 0r is the trivial linear Combination -}
  isLinearCombination0 : {n : ℕ} (V : FinVec R n)
                       → isLinearCombination V 0r
  isLinearCombination0 V = ∣ _ , sym (dist0 V) ∣

  {- Linear combinations are stable under left multiplication -}
  isLinearCombinationL· : {n : ℕ} (V : FinVec R n) (r : R) {x : R}
                        → isLinearCombination V x → isLinearCombination V (r · x)
  isLinearCombinationL· V r = map λ α → (λ i → r · α .fst i) , cong (r ·_) (α .snd)
                                                            ∙∙ ∑Mulrdist r (λ i → α .fst i · V i)
                                                            ∙∙ ∑Ext λ i → ·Assoc r (α .fst i) (V i)
  --   elim (λ _ → propTruncIsProp)
  --        λ {(cx , px) →
  --           ∣ map (r ·_) cx ,
  --            (r · _                               ≡[ i ]⟨ r · px i ⟩
  --             r · linearCombination cx l          ≡⟨ step1 _ cx l r  ⟩
  --             linearCombination (map (r ·_) cx) l ∎) ∣}
  --   where
  --     step2 : (r c a t1 : R) → r · (c · a + t1) ≡ r · (c · a) + r · t1
  --     step2 = solve Ring
  --     step3 : (r c a t1 : R) → r · (c · a) + t1 ≡ r · c · a + t1
  --     step3 = solve Ring
  --     step1 : (k : ℕ) (cx l : Vec R k)
  --             → (r : R)
  --             → r · linearCombination cx l ≡ linearCombination (map (r ·_) cx) l
  --     step1 ℕ.zero [] [] r = 0RightAnnihilates _
  --     step1 (ℕ.suc k) (c ∷ cx) (a ∷ l) r =
  --       r · (c · a + linearCombination cx l)               ≡⟨ step2 r c a _ ⟩
  --       r · (c · a) + r · linearCombination cx l           ≡[ i ]⟨ r · (c · a) + step1 _ cx l r i ⟩
  --       r · (c · a) + linearCombination (map (_·_ r) cx) l ≡⟨ step3 r c a _ ⟩
  --       r · c · a + linearCombination (map (_·_ r) cx) l ∎

  generatedIdeal : {n : ℕ} → FinVec R n → IdealsIn Ring
  generatedIdeal V = makeIdeal Ring
                               (λ x → isLinearCombination V x , propTruncIsProp)
                               (isLinearCombination+ V)
                               (isLinearCombination0 V)
                               λ r → isLinearCombinationL· V r
