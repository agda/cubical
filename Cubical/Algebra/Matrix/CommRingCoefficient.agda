{-

Matrix with coefficients in a commutative ring

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix.CommRingCoefficient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.FinData

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

open import Cubical.Algebra.Matrix

private
  variable
    ℓ : Level
    m n k l : ℕ

module Coefficient (𝓡 : CommRing ℓ) where

  private
    R = 𝓡 .fst
    𝑹 = CommRing→Ring 𝓡
    AbR = Ring→AbGroup 𝑹

  open CommRingStr       (𝓡 .snd) renaming ( is-set to isSetR )



  open Sum                𝑹
  open FinMatrixAbGroup

  -- Convenient renaming

  Mat : (m n : ℕ) → Type ℓ
  Mat m n = FinMatrix R m n

  isSetMat : isSet (Mat m n)
  isSetMat = isSetΠ2 (λ _ _ → isSetR)

  isContrEmpty : {n : ℕ} → isContr (Mat 0 n)
  isContrEmpty =
    isOfHLevelRespectEquiv _ (equiv→ (uninhabEquiv (λ ()) ¬Fin0) (idEquiv _)) isContr⊥→A

  isContrEmptyᵗ : {m : ℕ} → isContr (Mat m 0)
  isContrEmptyᵗ =
    isContrΠ (λ _ → isOfHLevelRespectEquiv _ (equiv→ (uninhabEquiv (λ ()) ¬Fin0) (idEquiv _)) isContr⊥→A)

  𝟙 : Mat n n
  𝟙 = oneFinMatrix 𝑹

  𝟘 : Mat m n
  𝟘 = zeroFinMatrix AbR

  _⋆_ : Mat m n → Mat n k → Mat m k
  M ⋆ N = mulFinMatrix 𝑹 M N

  infixl 8 _⋆_

  ⋆lUnit : (M : Mat m n) → 𝟙 ⋆ M ≡ M
  ⋆lUnit = mulFinMatrix1r 𝑹

  ⋆rUnit : (M : Mat m n) → M ⋆ 𝟙 ≡ M
  ⋆rUnit = mulFinMatrixr1 𝑹

  ⋆Assoc : (M : Mat m n)(N : Mat n k)(K : Mat k l) → M ⋆ (N ⋆ K) ≡ (M ⋆ N) ⋆ K
  ⋆Assoc = mulFinMatrixAssoc 𝑹

  -- Transposition

  _ᵗ : Mat m n → Mat n m
  (M ᵗ) i j = M j i

  idemᵗ : (M : Mat m n) → (M ᵗ)ᵗ ≡ M
  idemᵗ M t i j = M i j

  compᵗ : (M : Mat m n)(N : Mat n k) → (M ⋆ N)ᵗ ≡ N ᵗ ⋆ M ᵗ
  compᵗ M N t i j = ∑ (λ l → ·Comm (M j l) (N l i) t)

  𝟙ᵗ : 𝟙 ᵗ ≡ 𝟙 {n = n}
  𝟙ᵗ t zero zero = 1r
  𝟙ᵗ t (suc i) zero = 0r
  𝟙ᵗ t zero (suc j) = 0r
  𝟙ᵗ t (suc i) (suc j) = 𝟙ᵗ t i j

  -- Invertible matrices

  isInv' : Mat n n → Mat n n → Type ℓ
  isInv' {n = n} M N = (M ⋆ N ≡ 𝟙) × (N ⋆ M ≡ 𝟙)

  isPropIsInv' : (M N : Mat n n) → isProp (isInv' M N)
  isPropIsInv' M N = isProp× (isSetMat _ _) (isSetMat _ _)

  invUniq : (M N N' : Mat n n) → isInv' M N → isInv' M N' → N ≡ N'
  invUniq M N N' p q =
      sym (⋆lUnit N)
    ∙ (λ i → q .snd (~ i) ⋆ N)
    ∙ sym (⋆Assoc N' M N)
    ∙ (λ i → N' ⋆ p .fst i)
    ∙ ⋆rUnit N'

  isInv : Mat n n → Type ℓ
  isInv {n = n} M = Σ[ N ∈ Mat n n ] isInv' M N

  isPropIsInv : (M : Mat n n) → isProp (isInv M)
  isPropIsInv M p q = Σ≡Prop (λ _ → isPropIsInv' M _) (invUniq M _ _ (p .snd) (q .snd))

  isInv⋆ : (M M' : Mat n n) → isInv M → isInv M' → isInv (M ⋆ M')
  isInv⋆ M M' (N , p) (N' , q) .fst = N' ⋆ N
  isInv⋆ M M' (N , p) (N' , q) .snd .fst =
      sym (⋆Assoc M M' (N' ⋆ N))
    ∙ (λ i → M ⋆ ⋆Assoc M' N' N i)
    ∙ (λ i → M ⋆ (q .fst i ⋆ N))
    ∙ (λ i → M ⋆ ⋆lUnit N i)
    ∙ p .fst
  isInv⋆ M M' (N , p) (N' , q) .snd .snd =
      sym (⋆Assoc N' N (M ⋆ M'))
    ∙ (λ i → N' ⋆ ⋆Assoc N M M' i)
    ∙ (λ i → N' ⋆ (p .snd i ⋆ M'))
    ∙ (λ i → N' ⋆ ⋆lUnit M' i)
    ∙ q .snd

  InvMat : (n : ℕ) → Type ℓ
  InvMat n = Σ[ M ∈ Mat n n ] isInv M

  isInv𝟙 : isInv {n = n} 𝟙
  isInv𝟙 .fst = 𝟙
  isInv𝟙 .snd .fst = ⋆lUnit _
  isInv𝟙 .snd .snd = ⋆lUnit _

  isInvᵗ : {M : Mat n n} → isInv M → isInv (M ᵗ)
  isInvᵗ {M = M} isInvM .fst = (isInvM .fst)ᵗ
  isInvᵗ {M = M} isInvM .snd .fst = (sym (compᵗ _ M)) ∙ (λ t → (isInvM .snd .snd t)ᵗ) ∙ 𝟙ᵗ
  isInvᵗ {M = M} isInvM .snd .snd = (sym (compᵗ M _)) ∙ (λ t → (isInvM .snd .fst t)ᵗ) ∙ 𝟙ᵗ

  -- Inversion formula for 2 × 2 matrices

  dot2 : (V W : FinVec R 2) → (∑ λ i → V i · W i) ≡ V zero · W zero + V one · W one
  dot2 V W i = V zero · W zero + (+Rid (V one · W one) i)

  mul2 :
      (M : Mat m 2)(N : Mat 2 n)
    → (i : Fin m)(j : Fin n)
    → (M ⋆ N) i j ≡ M i zero · N zero j + M i one · N one j
  mul2 M N i j = dot2 (M i) (λ k → N k j)

  open Units 𝓡

  det2×2 : Mat 2 2 → R
  det2×2 M = M zero zero · M one one - M zero one · M one zero

  module _
    (M : Mat 2 2)(p : det2×2 M ∈ Rˣ) where

    private
      Δ   = det2×2 M
      Δ⁻¹ = (_⁻¹) Δ ⦃ p ⦄

      ·rInv : Δ · Δ⁻¹ ≡ 1r
      ·rInv = ·-rinv _ ⦃ p ⦄

      M⁻¹ : Mat 2 2
      M⁻¹ zero zero =   M one  one  · Δ⁻¹
      M⁻¹ zero one  = - M zero one  · Δ⁻¹
      M⁻¹ one  zero = - M one  zero · Δ⁻¹
      M⁻¹ one  one  =   M zero zero · Δ⁻¹

    isInvMat2x2 : isInv M
    isInvMat2x2 .fst = M⁻¹
    isInvMat2x2 .snd .fst i zero zero =
      (mul2 M M⁻¹ zero zero ∙ helper _ _ _ _ _ ∙ ·rInv) i
      where helper : (x y z w d : R) → x · (w · d) + y · (- z · d) ≡  (x · w - y · z) · d
            helper = solve 𝓡
    isInvMat2x2 .snd .fst i zero one  =
      (mul2 M M⁻¹ zero one  ∙ helper _ _ _) i
      where helper : (x y d : R) → x · (- y · d) + y · (x · d) ≡ 0r
            helper = solve 𝓡
    isInvMat2x2 .snd .fst i one  zero =
      (mul2 M M⁻¹ one  zero ∙ helper _ _ _) i
      where helper : (z w d : R) → z · (w · d) + w · (- z · d) ≡ 0r
            helper = solve 𝓡
    isInvMat2x2 .snd .fst i one  one  =
      (mul2 M M⁻¹ one  one  ∙ helper _ _ _ _ _ ∙ ·rInv) i
      where helper : (x y z w d : R) → z · (- y · d) + w · (x · d) ≡  (x · w - y · z) · d
            helper = solve 𝓡
    isInvMat2x2 .snd .snd i zero zero =
      (mul2 M⁻¹ M zero zero ∙ helper _ _ _ _ _ ∙ ·rInv) i
      where helper : (x y z w d : R) → (w · d) · x + (- y · d) · z ≡  (x · w - y · z) · d
            helper = solve 𝓡
    isInvMat2x2 .snd .snd i zero one  =
      (mul2 M⁻¹ M zero one  ∙ helper _ _ _) i
      where helper : (y w d : R) → (w · d) · y + (- y · d) · w ≡ 0r
            helper = solve 𝓡
    isInvMat2x2 .snd .snd i one  zero =
      (mul2 M⁻¹ M one  zero ∙ helper _ _ _) i
      where helper : (x z d : R) → (- z · d) · x + (x · d) · z ≡ 0r
            helper = solve 𝓡
    isInvMat2x2 .snd .snd i one  one  =
      (mul2 M⁻¹ M one  one  ∙ helper _ _ _ _ _ ∙ ·rInv) i
      where helper : (x y z w d : R) → (- z · d) · y + (x · d) · w ≡  (x · w - y · z) · d
            helper = solve 𝓡


  -- Similarity of matrices

  record SimRel (M N : Mat m n) : Type ℓ where
    field
      transMatL : Mat m m
      transMatR : Mat n n
      transEq : N ≡ transMatL ⋆ M ⋆ transMatR

      isInvTransL : isInv transMatL
      isInvTransR : isInv transMatR

  open SimRel

  record Sim (M : Mat m n) : Type ℓ where
    field
      result : Mat m n

      transMatL : Mat m m
      transMatR : Mat n n
      transEq : result ≡ transMatL ⋆ M ⋆ transMatR

      isInvTransL : isInv transMatL
      isInvTransR : isInv transMatR

  open Sim

  idSim : (M : Mat m n) → Sim M
  idSim M .result = M
  idSim _ .transMatL = 𝟙
  idSim _ .transMatR = 𝟙
  idSim M .transEq = sym ((λ t → ⋆lUnit M t ⋆ 𝟙) ∙ ⋆rUnit _)
  idSim _ .isInvTransL = isInv𝟙
  idSim _ .isInvTransR = isInv𝟙

  ≡Sim : (M N : Mat m n) → M ≡ N → Sim M
  ≡Sim M N p = record (idSim M) { result = N ; transEq = sym p ∙ idSim M .transEq }

  compSim : {M : Mat m n}(simM : Sim M)(simN : Sim (simM .result)) → Sim M
  compSim _ simN .result = simN .result
  compSim simM simN .transMatL = simN .transMatL ⋆ simM .transMatL
  compSim simM simN .transMatR = simM .transMatR ⋆ simN .transMatR
  compSim {M = M} simM simN .transEq =
      let L  = simM .transMatL
          R  = simM .transMatR
          L' = simN .transMatL
          R' = simN .transMatR in
      simN .transEq
    ∙ (λ t → L' ⋆ simM .transEq t ⋆ R')
    ∙ (λ t → L' ⋆ ⋆Assoc L M R (~ t) ⋆ R')
    ∙ (λ t → ⋆Assoc L' (L ⋆ (M ⋆ R)) R' (~ t))
    ∙ (λ t → L' ⋆ ⋆Assoc L (M ⋆ R) R' (~ t))
    ∙ (λ t → L' ⋆ (L ⋆ ⋆Assoc M R R' (~ t)))
    ∙ (λ t → L' ⋆ ⋆Assoc L M (R ⋆ R') t)
    ∙ (λ t → ⋆Assoc L' (L ⋆ M) (R ⋆ R') t)
    ∙ (λ t → ⋆Assoc L' L M t ⋆ (R ⋆ R'))
  compSim simM simN .isInvTransL = isInv⋆ _ _ (simN .isInvTransL) (simM .isInvTransL)
  compSim simM simN .isInvTransR = isInv⋆ _ _ (simM .isInvTransR) (simN .isInvTransR)

  -- Add a new element at upper-left corner

  _⊕_ : R → Mat m n → Mat (suc m) (suc n)
  (a ⊕ M) zero zero = a
  (a ⊕ M) zero (suc j) = 0r
  (a ⊕ M) (suc i) zero = 0r
  (a ⊕ M) (suc i) (suc j) = M i j

  infixr 5 _⊕_

  sucMat : (M : Mat (suc m) (suc n)) → Mat m n
  sucMat M i j = M (suc i) (suc j)

  𝟙suc : (i j : Fin m) → 𝟙 i j ≡ sucMat 𝟙 i j
  𝟙suc zero zero = refl
  𝟙suc zero (suc j) = refl
  𝟙suc (suc i) zero = refl
  𝟙suc (suc i) (suc j) = refl

  1⊕𝟙 : 1r ⊕ 𝟙 {n = n} ≡ 𝟙
  1⊕𝟙 t zero zero = 1r
  1⊕𝟙 t zero (suc j) = 0r
  1⊕𝟙 t (suc i) zero = 0r
  1⊕𝟙 t (suc i) (suc j) = 𝟙suc i j t

  ⊕-⋆ : (a b : R)(M : Mat m n)(N : Mat n k) → (a ⊕ M) ⋆ (b ⊕ N) ≡ (a · b) ⊕ (M ⋆ N)
  ⊕-⋆ {n = n} a b M N t zero zero = ((λ t → a · b + ∑Mul0r {n = n} (λ i → 0r) t) ∙ helper _ _) t
    where helper : (a b : R) → a · b + 0r ≡ a · b
          helper = solve 𝓡
  ⊕-⋆ a b M N t zero (suc j) = (helper a _ ∙ ∑Mul0r (λ i → N i j)) t
    where helper : (a c : R) → a · 0r + c ≡ c
          helper = solve 𝓡
  ⊕-⋆ a b M N t (suc i) zero = (helper b _ ∙ ∑Mulr0 (λ j → M i j)) t
    where helper : (b c : R) → 0r · b + c ≡ c
          helper = solve 𝓡
  ⊕-⋆ _ _ M N t (suc i) (suc j) = helper ((M ⋆ N) i j) t
    where helper : (c : R) → 0r · 0r + c ≡ c
          helper = solve 𝓡

  isInv⊕ : (M : Mat m m) → isInv M → (isInv (1r ⊕ M))
  isInv⊕ M isInvM .fst = 1r ⊕ isInvM .fst
  isInv⊕ M isInvM .snd .fst = ⊕-⋆ _ _ _ _ ∙ (λ t → ·Lid 1r t ⊕ isInvM .snd .fst t) ∙ 1⊕𝟙
  isInv⊕ M isInvM .snd .snd = ⊕-⋆ _ _ _ _ ∙ (λ t → ·Rid 1r t ⊕ isInvM .snd .snd t) ∙ 1⊕𝟙

  ⊕Sim : (a : R)(M : Mat m n) → (sim : Sim M) → Sim (a ⊕ M)
  ⊕Sim a M sim .result = a ⊕ sim .result
  ⊕Sim a M sim .transMatL = 1r ⊕ sim .transMatL
  ⊕Sim a M sim .transMatR = 1r ⊕ sim .transMatR
  ⊕Sim a M sim .transEq =
    let P = sim .transMatL
        Q = sim .transMatR in
      (λ t → helper a t ⊕ sim .transEq t)
    ∙ sym (⊕-⋆ _ _ _ Q)
    ∙ (λ t → ⊕-⋆ 1r a P M (~ t) ⋆ (1r ⊕ Q))
    where helper : (a : R) → a ≡ (1r · a) · 1r
          helper = solve 𝓡
  ⊕Sim a M sim .isInvTransL = isInv⊕ _ (sim .isInvTransL)
  ⊕Sim a M sim .isInvTransR = isInv⊕ _ (sim .isInvTransR)
