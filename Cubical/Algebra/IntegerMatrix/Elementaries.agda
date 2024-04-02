{-

Elementary transformation specific to coefficient ℤ

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Elementaries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.RowTransformation

private
  variable
    ℓ : Level
    m n : ℕ

-- It seems there are bugs when applying ring solver to integers.
-- The following is a work-around.
private
  module Helper {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b x y g : 𝓡 .fst) → (a · x - b · - y) · g ≡ a · (x · g) + b · (y · g)
    helper1 _ _ _ _ _ = solve! 𝓡

    helper2 : (a b : 𝓡 .fst) → a ≡ 1r · a + 0r · b
    helper2 _ _ = solve! 𝓡

open Helper ℤCommRing

module ElemTransformationℤ where

  open import Cubical.Foundations.Powerset

  open import Cubical.Data.Int using (·rCancel)
  open import Cubical.Data.Int.Divisibility

  private
    ℤ = ℤCommRing .fst

  open CommRingStr      (ℤCommRing .snd)
  open Sum              (CommRing→Ring ℤCommRing)

  open Coefficient ℤCommRing
  open LinearTransformation ℤCommRing
  open Bézout

  open SimRel
  open Sim

  open isLinear
  open isLinear2×2

  -- The Bézout step to simplify one row

  module _
    (x y : ℤ)(b : Bézout x y) where

    bézout2Mat : Mat 2 2
    bézout2Mat zero zero = b .coef₁
    bézout2Mat zero one  = b .coef₂
    bézout2Mat one  zero = - (div₂ b)
    bézout2Mat one  one  = div₁ b

    module _
      (p : ¬ x ≡ 0) where

      open Units ℤCommRing

      private
        detEq : det2×2 bézout2Mat · b .gcd ≡ b .gcd
        detEq =
            helper1 (b .coef₁) (b .coef₂) _ _ _
          ∙ (λ t → b .coef₁ · divideEq (b .isCD .fst) t + b .coef₂ · divideEq (b .isCD .snd) t)
          ∙ b .identity

        det≡1 : det2×2 bézout2Mat ≡ 1
        det≡1 = ·rCancel _ _ _ (detEq ∙ sym (·IdL _)) (¬m≡0→¬gcd≡0 b p)

      isInvBézout2Mat : isInv bézout2Mat
      isInvBézout2Mat = isInvMat2x2 bézout2Mat (subst (λ r → r ∈ Rˣ) (sym det≡1) RˣContainsOne)

  module _
    (M : Mat 2 (suc n)) where

    private
      b = bézout (M zero zero) (M one zero)

    bézout2Rows : Mat 2 (suc n)
    bézout2Rows zero i =   b .coef₁ · M zero i +  b .coef₂ · M one i
    bézout2Rows one  i = - (div₂ b) · M zero i +    div₁ b · M one i

    bézout2Rows-vanish : bézout2Rows one zero ≡ 0
    bézout2Rows-vanish = div·- b

    bézout2Rows-div₁ : (n : ℤ) → M zero zero ∣ n → bézout2Rows zero zero ∣ n
    bézout2Rows-div₁ n p = subst (λ a → a ∣ n) (sym (b .identity)) (∣-trans (b .isCD .fst) p)

    bézout2Rows-div₂ : (n : ℤ) → M one  zero ∣ n → bézout2Rows zero zero ∣ n
    bézout2Rows-div₂ n p = subst (λ a → a ∣ n) (sym (b .identity)) (∣-trans (b .isCD .snd) p)

    bézout2Rows-nonZero : ¬ M zero zero ≡ 0 → ¬ bézout2Rows zero zero ≡ 0
    bézout2Rows-nonZero p r =
      p (sym (∣-zeroˡ (subst (λ a → a ∣ M zero zero) r (bézout2Rows-div₁ (M zero zero) (∣-refl refl)))))

    bézout2Rows-inv : ¬ M zero zero ≡ 0 → M zero zero ∣ M one zero → M zero ≡ bézout2Rows zero
    bézout2Rows-inv p q t j =
      let (c₁≡1 , c₂≡0) = bézout∣ _ _ p q in
      (helper2 (M zero j) (M one j) ∙ (λ t → c₁≡1 (~ t) · M zero j + c₂≡0 (~ t) · M one j)) t

    bézout2Rows-commonDiv : (a : ℤ)
      → ((j : Fin (suc n)) → a ∣ M zero j)
      → ((j : Fin (suc n)) → a ∣ M one  j)
      →  (i : Fin 2)(j : Fin (suc n)) → a ∣ bézout2Rows i j
    bézout2Rows-commonDiv a p q zero j = ∣-+ (∣-right· {n =   b .coef₁} (p j)) (∣-right· {n = b .coef₂} (q j))
    bézout2Rows-commonDiv a p q one  j = ∣-+ (∣-right· {n = - (div₂ b)} (p j)) (∣-right· {n =   div₁ b} (q j))

  module _
    (M : Mat (suc m) (suc n)) where

    bézoutRows : Mat (suc m) (suc n)
    bézoutRows = transRows bézout2Rows M

    bézoutRows-vanish : (i : Fin m) → bézoutRows (suc i) zero ≡ 0
    bézoutRows-vanish = transRowsIndP' _ (λ v → v zero ≡ 0) bézout2Rows-vanish M

    bézoutRows-div₁-helper : (n : ℤ) → M zero zero ∣ n → bézoutRows zero zero ∣ n
    bézoutRows-div₁-helper n = transRowsIndP _ (λ v → v zero ∣ n) (λ M → bézout2Rows-div₁ M n) M

    bézoutRows-div₂-helper : (n : ℤ) → (i : Fin m) → M (suc i) zero ∣ n → bézoutRows zero zero ∣ n
    bézoutRows-div₂-helper n =
      transRowsIndPQ' _ (λ v → v zero ∣ n) (λ v → v zero ∣ n)
        (λ M → bézout2Rows-div₁ M n) (λ M → bézout2Rows-div₂ M n) M

    bézoutRows-div : (i : Fin (suc m)) → bézoutRows zero zero ∣ M i zero
    bézoutRows-div zero    = bézoutRows-div₁-helper _   (∣-refl refl)
    bézoutRows-div (suc i) = bézoutRows-div₂-helper _ i (∣-refl refl)

    bézoutRows-nonZero : ¬ M zero zero ≡ 0 → ¬ bézoutRows zero zero ≡ 0
    bézoutRows-nonZero p r = p (sym (∣-zeroˡ (subst (λ a → a ∣ M zero zero) r (bézoutRows-div zero))))

    bézoutRows-inv : ¬ M zero zero ≡ 0 → ((i : Fin m) → M zero zero ∣ M (suc i) zero) → M zero ≡ bézoutRows zero
    bézoutRows-inv = transRowsIndPRelInv _ (λ V → ¬ V zero ≡ 0) (λ U V → U zero ∣ V zero) bézout2Rows-inv M

    bézoutRows-commonDiv₀ : (a : ℤ)
      → ((j : Fin (suc n)) → a ∣ M zero j)
      → ((i : Fin m)(j : Fin (suc n)) → a ∣ M (suc i) j)
      →  (j : Fin (suc n)) → a ∣ bézoutRows zero j
    bézoutRows-commonDiv₀ a =
      transRowsIndP₀ _ (λ V → ((j : Fin (suc n)) → a ∣ V j))
        (λ N s s' → bézout2Rows-commonDiv N a s s' zero)
        (λ N s s' → bézout2Rows-commonDiv N a s s' one) _

    bézoutRows-commonDiv₁ : (a : ℤ)
      → ((j : Fin (suc n)) → a ∣ M zero j)
      → ((i : Fin m)(j : Fin (suc n)) → a ∣ M (suc i) j)
      →  (i : Fin m)(j : Fin (suc n)) → a ∣ bézoutRows (suc i) j
    bézoutRows-commonDiv₁ a =
      transRowsIndP₁ _ (λ V → ((j : Fin (suc n)) → a ∣ V j))
        (λ N s s' → bézout2Rows-commonDiv N a s s' zero)
        (λ N s s' → bézout2Rows-commonDiv N a s s' one) _

    bézoutRows-commonDiv :
        ((i : Fin (suc m))(j : Fin (suc n)) → M zero zero ∣ M i j)
      →  (i : Fin (suc m))(j : Fin (suc n)) → M zero zero ∣ bézoutRows i j
    bézoutRows-commonDiv p zero    = bézoutRows-commonDiv₀ _ (p zero) (p ∘ suc)
    bézoutRows-commonDiv p (suc i) = bézoutRows-commonDiv₁ _ (p zero) (p ∘ suc) i

    bézoutRows-commonDivInv :
        ¬ M zero zero ≡ 0
      → ((i : Fin (suc m))(j : Fin (suc n)) → M zero zero ∣ M i j)
      →  (i : Fin (suc m))(j : Fin (suc n)) → bézoutRows zero zero ∣ bézoutRows i j
    bézoutRows-commonDivInv h p i j =
      let inv = (λ t → bézoutRows-inv h (λ i → p (suc i) zero) t zero) in
      subst (_∣ bézoutRows i j) inv (bézoutRows-commonDiv p i j)

  isLinear2Bézout2Rows : isLinear2×2 (bézout2Rows {n = n})
  isLinear2Bézout2Rows .transMat M = bézout2Mat _ _ (bézout (M zero zero) (M one zero))
  isLinear2Bézout2Rows .transEq  M t zero j = mul2 (isLinear2Bézout2Rows .transMat M) M zero j (~ t)
  isLinear2Bézout2Rows .transEq  M t one  j = mul2 (isLinear2Bézout2Rows .transMat M) M one  j (~ t)

  isLinearBézoutRows : isLinear (bézoutRows {m = m} {n = n})
  isLinearBézoutRows = isLinearTransRows _ isLinear2Bézout2Rows _

  isInv2Bézout2Rows : (M : Mat 2 (suc n))(p : ¬ M zero zero ≡ 0) → isInv (isLinear2Bézout2Rows .transMat M)
  isInv2Bézout2Rows _ p = isInvBézout2Mat _ _ _ p

  isInvBézout2Rows : (M : Mat (suc m) (suc n))(p : ¬ M zero zero ≡ 0) → isInv (isLinearBézoutRows .transMat M)
  isInvBézout2Rows = isInvTransRowsInd _ _ (λ V → ¬ V zero ≡ 0) bézout2Rows-nonZero isInv2Bézout2Rows

  -- Using Bézout identity to eliminate the first column/row

  record RowsImproved (M : Mat (suc m) (suc n)) : Type where
    field
      sim : Sim M

      div     : (i : Fin (suc m)) → sim .result zero zero ∣ M i zero
      vanish  : (i : Fin m) → sim .result (suc i) zero ≡ 0
      nonZero : ¬ sim .result zero zero ≡ 0

  record ColsImproved (M : Mat (suc m) (suc n)) : Type where
    field
      sim : Sim M

      div     : (j : Fin (suc n)) → sim .result zero zero ∣ M zero j
      vanish  : (j : Fin n) → sim .result zero (suc j) ≡ 0
      nonZero : ¬ sim .result zero zero ≡ 0

  open RowsImproved
  open ColsImproved

  improveRows : (M : Mat (suc m) (suc n))(p : ¬ M zero zero ≡ 0) → RowsImproved M
  improveRows M _ .sim .result   = bézoutRows M
  improveRows M _ .sim .simrel .transMatL = isLinearBézoutRows .transMat M
  improveRows _ _ .sim .simrel .transMatR = 𝟙
  improveRows _ _ .sim .simrel .transEq   = isLinearBézoutRows .transEq _ ∙ sym (⋆rUnit _)
  improveRows _ p .sim .simrel .isInvTransL = isInvBézout2Rows _ p
  improveRows _ p .sim .simrel .isInvTransR = isInv𝟙
  improveRows _ _ .div     = bézoutRows-div     _
  improveRows _ _ .vanish  = bézoutRows-vanish  _
  improveRows M p .nonZero = bézoutRows-nonZero M p

  improveCols : (M : Mat (suc m) (suc n))(p : ¬ M zero zero ≡ 0) → ColsImproved M
  improveCols M _ .sim .result    = (bézoutRows (M ᵗ))ᵗ
  improveCols _ _ .sim .simrel .transMatL = 𝟙
  improveCols M _ .sim .simrel .transMatR = (isLinearBézoutRows .transMat (M ᵗ))ᵗ
  improveCols M _ .sim .simrel .transEq     =
    let P = isLinearBézoutRows .transMat (M ᵗ) in
      (λ t → (isLinearBézoutRows .transEq (M ᵗ) t)ᵗ)
    ∙ compᵗ P (M ᵗ)
    ∙ (λ t → idemᵗ M t ⋆ P ᵗ)
    ∙ (λ t → ⋆lUnit M (~ t) ⋆ P ᵗ)
  improveCols _ _ .sim .simrel .isInvTransL = isInv𝟙
  improveCols M p .sim .simrel .isInvTransR =
    isInvᵗ {M = isLinearBézoutRows .transMat (M ᵗ)} (isInvBézout2Rows (M ᵗ) p)
  improveCols _ _ .div     = bézoutRows-div     _
  improveCols _ _ .vanish  = bézoutRows-vanish  _
  improveCols M p .nonZero = bézoutRows-nonZero (M ᵗ) p
