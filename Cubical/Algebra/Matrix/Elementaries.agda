{-

Technical results about elementary transformations

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix.Elementaries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.Data.FinData renaming (znots to znotsFin ; snotz to snotzFin)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.RowTransformation

private
  variable
    ℓ : Level
    A : Type ℓ
    m n k l : ℕ

module ElemTransformation (𝓡 : CommRing ℓ) where

  private
    R = 𝓡 .fst

  open CommRingStr     (𝓡 .snd) renaming ( is-set to isSetR )
  open KroneckerDelta  (CommRing→Ring 𝓡)
  open Sum             (CommRing→Ring 𝓡)

  open Coefficient           𝓡
  open LinearTransformation  𝓡

  open SimRel
  open Sim

  open isLinear
  open isLinear2×2

  -- Swapping the first row with another

  swapMat : Mat 2 2
  swapMat zero zero = 0r
  swapMat zero one  = 1r
  swapMat one  zero = 1r
  swapMat one  one  = 0r

  uniSwapMat : swapMat ⋆ swapMat ≡ 𝟙
  uniSwapMat t zero zero =
    (mul2 swapMat swapMat zero zero ∙ helper) t
    where helper : 0r · 0r + 1r · 1r ≡ 1r
          helper = solve 𝓡
  uniSwapMat t zero one  =
    (mul2 swapMat swapMat zero one  ∙ helper) t
    where helper : 0r · 1r + 1r · 0r ≡ 0r
          helper = solve 𝓡
  uniSwapMat t one  zero =
    (mul2 swapMat swapMat one  zero ∙ helper) t
    where helper : 1r · 0r + 0r · 1r ≡ 0r
          helper = solve 𝓡
  uniSwapMat t one  one  =
    (mul2 swapMat swapMat one  one  ∙ helper) t
    where helper : 1r · 1r + 0r · 0r ≡ 1r
          helper = solve 𝓡

  isInvSwapMat2 : isInv swapMat
  isInvSwapMat2 .fst = swapMat
  isInvSwapMat2 .snd .fst = uniSwapMat
  isInvSwapMat2 .snd .snd = uniSwapMat

  swapRow2 : Mat 2 n → Mat 2 n
  swapRow2 M zero = M one
  swapRow2 M one  = M zero

  isLinear2×2SwapRow2 : isLinear2×2 {n = n} swapRow2
  isLinear2×2SwapRow2 .transMat _ = swapMat
  isLinear2×2SwapRow2 .transEq M t zero j =
    ((mul2 swapMat M zero j) ∙ helper _ _) (~ t)
    where helper : (a b : R) → 0r · a + 1r · b ≡ b
          helper = solve 𝓡
  isLinear2×2SwapRow2 .transEq M t one  j =
    ((mul2 swapMat M one  j) ∙ helper _ _) (~ t)
    where helper : (a b : R) → 1r · a + 0r · b ≡ a
          helper = solve 𝓡

  swapRow : (i₀ : Fin m)(M : Mat (suc m) n) → Mat (suc m) n
  swapRow i M zero = M (suc i)
  swapRow zero M one  = M zero
  swapRow zero M (suc (suc i)) = M (suc (suc i))
  swapRow (suc i₀) M one   = M one
  swapRow (suc i₀) M (suc (suc i)) = swapRow i₀ (takeRowsᶜ M) (suc i)

  swapRowMat : (i₀ : Fin m) → Mat (suc m) (suc m)
  swapRowMat = trans2RowsMat swapMat

  swapRowEq : (i₀ : Fin m)(M : Mat (suc m) n) → swapRow i₀ M ≡ swapRowMat i₀ ⋆ M
  swapRowEq {m = suc m} zero M t zero j =
      (helper1 _ _
    ∙ (λ t → 0r · M zero j + ∑Mulr1 _ (λ i → M (suc i) j) zero (~ t))
    ∙ (λ t → 0r · M zero j + ∑ (λ i → helper2 (δ i zero) (M (suc i) j) t))) t
    where helper1 : (a b : R) → b ≡ 0r · a + b
          helper1 = solve 𝓡
          helper2 : (a b : R) → b · a ≡ (1r · a) · b
          helper2 = solve 𝓡
  swapRowEq {m = suc m} zero M t one  j =
      (helper _
    ∙ (λ t → (1r · 1r) · M zero j + ∑Mul0r (λ i → M (suc i) j) (~ t))) t
    where helper : (a : R) → a ≡ (1r · 1r) · a + 0r
          helper = solve 𝓡
  swapRowEq {m = suc m} zero M t (suc (suc i)) j =
      (helper _ _
    ∙ (λ t → (1r · 0r) · M zero j + ∑Mul1r _ (λ l → M (suc l) j) (suc i) (~ t))) t
    where helper : (a b : R) → b ≡ (1r · 0r) · a + b
          helper = solve 𝓡
  swapRowEq {m = suc m} (suc i₀) M t zero j =
      (helper1 _ _
    ∙ (λ t → 0r · M zero j + ∑Mul1r _ (λ i → M (suc i) j) (suc i₀) (~ t))
    ∙ (λ t → 0r · M zero j + ∑ (λ l → helper2 (δ (suc i₀) l) (M (suc l) j) t))) t
    where helper1 : (a b : R) → b ≡ 0r · a + b
          helper1 = solve 𝓡
          helper2 : (a b : R) → a · b ≡ (1r · a) · b
          helper2 = solve 𝓡
  swapRowEq {m = suc m} (suc i₀) M t one  j =
        (helper _ _ --helper1 _ _
      ∙ (λ t → (1r · 0r) · M zero j + ∑Mul1r _ (λ i → M (suc i) j) zero (~ t))) t
    where helper : (a b : R) → b ≡ (1r · 0r) · a + b
          helper = solve 𝓡
  swapRowEq {m = suc m} (suc i₀) M t (suc (suc i)) j =
     ((λ t → swapRowEq i₀ (takeRowsᶜ M) t (suc i) j)
    ∙ helper _ (M one j) _) t
    where helper : (a b c : R) → a + c ≡ a + (0r · b + c)
          helper = solve 𝓡

  isLinearSwapRow : (i : Fin m) → isLinear (swapRow {n = n} i)
  isLinearSwapRow i .transMat _ = swapRowMat i
  isLinearSwapRow i .transEq    = swapRowEq  i

  isInvSwapMat : (i : Fin m)(M : Mat (suc m) (suc n)) → isInv (isLinearSwapRow i .transMat M)
  isInvSwapMat i _ = isInvTrans2RowsMat _ i isInvSwapMat2

  -- Similarity defined by swapping

  record SwapFirstRow (i : Fin m)(M : Mat (suc m) (suc n)) : Type ℓ where
    field
      sim : Sim M
      swapEq : (j : Fin (suc n)) → M (suc i) j ≡ sim .result zero j

  record SwapFirstCol (j : Fin n)(M : Mat (suc m) (suc n)) : Type ℓ where
    field
      sim : Sim M
      swapEq : (i : Fin (suc m)) → M i (suc j) ≡ sim .result i zero

  record SwapPivot (i : Fin (suc m))(j : Fin (suc n))(M : Mat (suc m) (suc n)) : Type ℓ where
    field
      sim : Sim M
      swapEq : M i j ≡ sim .result zero zero

  open SwapFirstRow
  open SwapFirstCol
  open SwapPivot

  swapFirstRow : (i : Fin m)(M : Mat (suc m) (suc n)) → SwapFirstRow i M
  swapFirstRow i M .sim .result    = swapRow i M
  swapFirstRow i M .sim .simrel .transMatL = isLinearSwapRow i .transMat M
  swapFirstRow i M .sim .simrel .transMatR = 𝟙
  swapFirstRow i M .sim .simrel .transEq     = isLinearSwapRow i .transEq _ ∙ sym (⋆rUnit _)
  swapFirstRow i M .sim .simrel .isInvTransL = isInvSwapMat i M
  swapFirstRow i M .sim .simrel .isInvTransR = isInv𝟙
  swapFirstRow i M .swapEq j = refl

  swapFirstCol : (j : Fin n)(M : Mat (suc m) (suc n)) → SwapFirstCol j M
  swapFirstCol j M .sim .result    = (swapRow j (M ᵗ))ᵗ
  swapFirstCol j M .sim .simrel .transMatL = 𝟙
  swapFirstCol j M .sim .simrel .transMatR = (isLinearSwapRow j .transMat (M ᵗ))ᵗ
  swapFirstCol j M .sim .simrel .transEq =
    let P = isLinearSwapRow j .transMat (M ᵗ) in
      (λ t → (isLinearSwapRow j .transEq (M ᵗ) t)ᵗ)
    ∙ compᵗ P (M ᵗ)
    ∙ (λ t → idemᵗ M t ⋆ P ᵗ)
    ∙ (λ t → ⋆lUnit M (~ t) ⋆ P ᵗ)
  swapFirstCol j M .sim .simrel .isInvTransL = isInv𝟙
  swapFirstCol j M .sim .simrel .isInvTransR =
    isInvᵗ {M = isLinearSwapRow j .transMat (M ᵗ)} (isInvSwapMat j (M ᵗ))
  swapFirstCol j M .swapEq i t = M i (suc j)

  swapPivot : (i : Fin (suc m))(j : Fin (suc n))(M : Mat (suc m) (suc n)) → SwapPivot i j M
  swapPivot zero zero M .sim    = idSim M
  swapPivot zero zero M .swapEq = refl
  swapPivot (suc i) zero M .sim    = swapFirstRow i M .sim
  swapPivot (suc i) zero M .swapEq = refl
  swapPivot zero (suc j) M .sim    = swapFirstCol j M .sim
  swapPivot zero (suc j) M .swapEq = refl
  swapPivot (suc i) (suc j) M .sim = compSim (swapFirstRow i M .sim) (swapFirstCol j _ .sim)
  swapPivot (suc i) (suc j) M .swapEq = refl


  -- Add the first row to another

  addMat : Mat 2 2
  addMat zero zero = 1r
  addMat zero one  = 0r
  addMat one  zero = 1r
  addMat one  one  = 1r

  subMat : Mat 2 2
  subMat zero zero = 1r
  subMat zero one  = 0r
  subMat one  zero = - 1r
  subMat one  one  = 1r

  add⋆subMat : addMat ⋆ subMat ≡ 𝟙
  add⋆subMat t zero zero =
    (mul2 addMat subMat zero zero ∙ helper) t
    where helper : 1r · 1r + 0r · - 1r ≡ 1r
          helper = solve 𝓡
  add⋆subMat t zero one  =
    (mul2 addMat subMat zero one  ∙ helper) t
    where helper : 1r · 0r + 0r · 1r ≡ 0r
          helper = solve 𝓡
  add⋆subMat t one  zero =
    (mul2 addMat subMat one  zero ∙ helper) t
    where helper : 1r · 1r + 1r · - 1r ≡ 0r
          helper = solve 𝓡
  add⋆subMat t one  one  =
    (mul2 addMat subMat one  one  ∙ helper) t
    where helper : 1r · 0r + 1r · 1r ≡ 1r
          helper = solve 𝓡

  sub⋆addMat : subMat ⋆ addMat ≡ 𝟙
  sub⋆addMat t zero zero =
    (mul2 subMat addMat  zero zero ∙ helper) t
    where helper : 1r · 1r + 0r · 1r ≡ 1r
          helper = solve 𝓡
  sub⋆addMat t zero one  =
    (mul2 subMat addMat  zero one  ∙ helper) t
    where helper : 1r · 0r + 0r · 1r ≡ 0r
          helper = solve 𝓡
  sub⋆addMat t one  zero =
    (mul2 subMat addMat  one  zero ∙ helper) t
    where helper : - 1r · 1r + 1r · 1r ≡ 0r
          helper = solve 𝓡
  sub⋆addMat t one  one  =
    (mul2 subMat addMat  one  one  ∙ helper) t
    where helper : - 1r · 0r + 1r · 1r ≡ 1r
          helper = solve 𝓡

  isInvAddMat2 : isInv addMat
  isInvAddMat2 .fst = subMat
  isInvAddMat2 .snd .fst = add⋆subMat
  isInvAddMat2 .snd .snd = sub⋆addMat

  addRow2 : Mat 2 n → Mat 2 n
  addRow2 M zero  = M zero
  addRow2 M one j = M zero j + M one j

  isLinear2AddRow2 : isLinear2×2 {n = n} addRow2
  isLinear2AddRow2 .transMat _ = addMat
  isLinear2AddRow2 .transEq M t zero j =
    ((mul2 addMat M zero j) ∙ helper _ _) (~ t)
    where helper : (a b : R) → 1r · a + 0r · b ≡ a
          helper = solve 𝓡
  isLinear2AddRow2 .transEq M t one  j =
    ((mul2 addMat M one  j) ∙ helper _ _) (~ t)
    where helper : (a b : R) → 1r · a + 1r · b ≡ a + b
          helper = solve 𝓡

  -- Add the first row to all other rows

  addRows : Mat (suc m) n → Mat (suc m) n
  addRows M zero = M zero
  addRows M (suc i) j = M zero j + M (suc i) j

  private
    firstRowStayInvariant : (M : Mat (suc m) n) → M zero ≡ transRows addRow2 M zero
    firstRowStayInvariant = invRow₀ _ (λ _ → refl)

  addRowsEq : (M : Mat (suc m) n) → transRows addRow2 M ≡ addRows M
  addRowsEq M t zero = firstRowStayInvariant M (~ t)
  addRowsEq M t one j = M zero j + M one j
  addRowsEq M t (suc (suc i)) j = takeCombShufRows addRow2 (λ N → addRowsEq N t) M (suc (suc i)) j

  isLinearAddRows : isLinear (addRows {m = m} {n = suc n})
  isLinearAddRows =
    let isLinear = isLinearTransRows _ isLinear2AddRow2 _
    in  record
          { transMat = isLinear .transMat
          ; transEq  = (λ M → sym (addRowsEq M) ∙ isLinear .transEq M) }

  isInvAddRows : (M : Mat (suc m) (suc n)) → isInv (isLinearAddRows .transMat M)
  isInvAddRows = isInvTransRows _ _ (λ _ → isInvAddMat2)

-- Similarity defined by adding rows

  record AddFirstRow (M : Mat (suc m) (suc n)) : Type ℓ where
    field
      sim : Sim M
      inv₀  : M zero ≡ sim .result zero
      addEq : (i : Fin m)(j : Fin (suc n)) → M zero j + M (suc i) j ≡ sim .result (suc i) j

  open AddFirstRow

  addFirstRow : (M : Mat (suc m) (suc n)) → AddFirstRow M
  addFirstRow M .sim .result    = addRows M
  addFirstRow M .sim .simrel .transMatL = isLinearAddRows .transMat M
  addFirstRow M .sim .simrel .transMatR = 𝟙
  addFirstRow M .sim .simrel .transEq     = isLinearAddRows .transEq _ ∙ sym (⋆rUnit _)
  addFirstRow M .sim .simrel .isInvTransL = isInvAddRows M
  addFirstRow M .sim .simrel .isInvTransR = isInv𝟙
  addFirstRow M .inv₀      = refl
  addFirstRow M .addEq i j = refl


-- Elementary transformation specific to coefficient ℤ

open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to Ringℤ)

-- It seems there are bugs when applying ring solver to integers.
-- The following is a work-around.
private
  module Helper {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b x y g : 𝓡 .fst) → (a · x - b · - y) · g ≡ a · (x · g) + b · (y · g)
    helper1 = solve 𝓡

    helper2 : (a b : 𝓡 .fst) → a ≡ 1r · a + 0r · b
    helper2 = solve 𝓡

open Helper Ringℤ

module ElemTransformationℤ where

  open import Cubical.Foundations.Powerset

  open import Cubical.Data.Int using (·rCancel)
  open import Cubical.Data.Int.Divisibility

  private
    ℤ = Ringℤ .fst

  open CommRingStr      (Ringℤ .snd)
  open Sum              (CommRing→Ring Ringℤ)

  open Coefficient Ringℤ
  open LinearTransformation Ringℤ
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

      open Units Ringℤ

      private
        detEq : det2×2 bézout2Mat · b .gcd ≡ b .gcd
        detEq =
            helper1 (b .coef₁) (b .coef₂) _ _ _
          ∙ (λ t → b .coef₁ · divideEq (b .isGCD .fst) t + b .coef₂ · divideEq (b .isGCD .snd) t)
          ∙ b .identity

        det≡1 : det2×2 bézout2Mat ≡ 1
        det≡1 = ·rCancel _ _ _ (detEq ∙ sym (·Lid _)) (¬m≡0→¬gcd≡0 b p)

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
    bézout2Rows-div₁ n p = subst (λ a → a ∣ n) (sym (b .identity)) (∣-trans (b .isGCD .fst) p)

    bézout2Rows-div₂ : (n : ℤ) → M one  zero ∣ n → bézout2Rows zero zero ∣ n
    bézout2Rows-div₂ n p = subst (λ a → a ∣ n) (sym (b .identity)) (∣-trans (b .isGCD .snd) p)

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
