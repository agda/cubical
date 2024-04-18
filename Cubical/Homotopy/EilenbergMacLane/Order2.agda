{-# OPTIONS --safe --lossy-unification #-}

{- This file contains properties of K(G,n) for G of order 2
(in particular of ℤ/2) -}

module Cubical.Homotopy.EilenbergMacLane.Order2 where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)

open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous


open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; elim to ℕelim)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct

open AbGroupStr
open PlusBis

module EM2 {ℓ : Level} (G : AbGroup ℓ)
         (-Const : (x : fst G) → -_ (snd G) x ≡ x) where

  -ₖConst : (n : ℕ) → (x : EM G (suc n)) → -ₖ x ≡ x
  -ₖConst =
   elim+2 -ₖConst₁
     (TR.elim (λ _ → isOfHLevelPath 4
                       (hLevelEM _ 2) _ _)
     λ { north → refl
       ; south i → ∣ merid embase i ∣
       ; (merid a i) j →
         hcomp (λ r → λ {(i = i0) → ∣ north ∣
                         ; (i = i1) → ∣ merid embase (j ∧ r) ∣
                         ; (j = i0) → EM→ΩEM+1-sym (suc zero) a r i
                         ; (j = i1) → ∣ compPath-filler (merid a)
                                        (sym (merid embase)) (~ r) i ∣})
                (EM→ΩEM+1 (suc zero) (-ₖConst₁ a j) i)})
     λ n ind → TR.elim (λ _ → isOfHLevelPath (suc (suc (suc (suc (suc n)))))
                        (hLevelEM _ (suc (suc (suc n)))) _ _)
     λ { north → refl
       ; south i → ∣ merid north i ∣
       ; (merid a i) j →
          hcomp (λ r → λ {(i = i0) → ∣ north ∣
                         ; (i = i1) → ∣ merid north (j ∧ r) ∣
                         ; (j = i0) → EM→ΩEM+1-sym (suc (suc n)) ∣ a ∣ₕ r i
                         ; (j = i1) → ∣ compPath-filler (merid a)
                                         (sym (merid north)) (~ r) i ∣})
                (EM→ΩEM+1 (suc (suc n)) (ind ∣ a ∣ j) i)}
    where
    -ₖConst₁ : (x : EM G (suc zero)) → -[ 1 ]ₖ x ≡ x
    -ₖConst₁ = elimSet _ (λ _ → emsquash _ _)
          refl
          λ g → flipSquare (sym (emloop-sym (AbGroup→Group G) g)
               ∙ cong emloop (-Const g))

  -- encode-decode proof that sym = id in ΩK(ℤ/2,n)
  -- (reducing to (transport refl) refl for the case sym refl = refl)
  private
    symCode : (n : ℕ) (x : EM G (suc n))
      → 0ₖ (suc n) ≡ x
      → TypeOfHLevel ℓ (suc n)
    symCode zero =
      EM-raw'-elim _ 1
       (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelTypeOfHLevel 1)
        λ { embase-raw → λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _
         ; (emloop-raw g i) → main g i}
      where
      main' : (g : fst G)
        → PathP (λ i → Path (EM G 1) embase (emloop g i) → Type ℓ)
                 (λ p → p ≡ sym p) λ p → p ≡ sym p
      main' g = toPathP (funExt
        λ p → (λ i
            → transp (λ j → Path (EM G 1) embase (emloop g (~ j ∧ ~ i))) i
                      (compPath-filler p (sym (emloop g)) i)
             ≡ sym (transp (λ j → Path (EM G 1) embase (emloop g (~ j ∧ ~ i))) i
                      (compPath-filler p (sym (emloop g)) i)))
           ∙ cong (p ∙ sym (emloop g) ≡_) (symDistr p (sym (emloop g))
                  ∙ isCommΩEM {G = G} 0 (emloop g) (sym p)
                  ∙ cong (sym p ∙_) (cong sym (sym (EM→ΩEM+1-sym 0 g)
                  ∙ cong (EM→ΩEM+1 0) (-Const g))))
           ∙ (λ i → compPath-filler p (sym (emloop g)) (~ i)
                   ≡ compPath-filler (sym p) (sym (emloop g)) (~ i)))
      main : (g : fst G)
        → PathP (λ i → Path (EM G 1) embase (emloop g i) → TypeOfHLevel ℓ 1)
                 (λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _)
                 λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _
      main g = toPathP (funExt (λ p → Σ≡Prop (λ _ → isPropIsProp)
                (funExt⁻ (fromPathP (main' g)) p)))
    symCode (suc n) =
      TR.elim (λ _ → isOfHLevelΠ (4 +ℕ n)
              λ _ → isOfHLevelSuc (3 +ℕ n) (isOfHLevelTypeOfHLevel (2 +ℕ n)))
              λ a p → Code a p , hLevCode a p
      where
      Code : (a : EM-raw G (suc (suc n))) → 0ₖ (suc (suc n)) ≡ ∣ a ∣ₕ → Type ℓ
      Code north p = p ≡ sym p
      Code south p = p ∙ cong ∣_∣ₕ (sym (merid ptEM-raw))
                   ≡ cong ∣_∣ₕ (merid ptEM-raw) ∙ sym p
      Code (merid a i) = h a i
        where
        K2 = EM G (suc (suc n))



        h : (a : _) → PathP (λ i → Path K2 ∣ north ∣ ∣ merid a i ∣ → Type ℓ)
                             (λ p → (p ≡ sym p))
                             λ p → (p ∙ cong ∣_∣ₕ (sym (merid ptEM-raw))
                                  ≡ cong ∣_∣ₕ (merid ptEM-raw) ∙ sym p)
        h a =
          toPathP (flipTransport
                   {A = λ i → Path K2 ∣ north ∣ ∣ merid a i ∣ → Type ℓ}
                      (funExt (λ p →
                        (((p₃ p
                         ∙ λ i → p₁ p i ≡ p₂ p (~ i))
                        ∙ λ i → delTransp p (~ i) ∙ sym m∙
                               ≡ m∙ ∙ sym (delTransp p (~ i)))
                       ∙ sym (transportRefl _)))))
          where
          m∙ : Path K2 ∣ north ∣ ∣ south ∣
          m∙ i = ∣ merid ptEM-raw i ∣

          ma : Path K2 ∣ north ∣ ∣ south ∣
          ma i = ∣ merid a i ∣

          σ' : (n : ℕ) (a : EM-raw G (suc n)) → fst ((Ω (EM∙ G (suc (suc n)))))
          σ' n a i = ∣ (merid a ∙ sym (merid ptEM-raw)) i ∣ₕ

          delTransp : (p : _) → transport (λ i → Path K2 ∣ north ∣ ∣ merid a i ∣) p
                       ≡ p ∙ cong ∣_∣ₕ (merid a)
          delTransp p i = transp (λ j → Path K2 ∣ north ∣ ∣ merid a (j ∨ i) ∣) i
                         (compPath-filler p (cong ∣_∣ₕ (merid a)) i)

          σ-sym : (n : ℕ) (a : _) → sym (σ' n a) ≡ σ' n a
          σ-sym zero a = sym (EM→ΩEM+1-sym 1 a)
                       ∙ cong (EM→ΩEM+1 1) (-ₖConst 0 a)
          σ-sym (suc n) a = sym (EM→ΩEM+1-sym (2 +ℕ n) ∣ a ∣)
                          ∙ cong (EM→ΩEM+1 (2 +ℕ n)) (-ₖConst (suc n) ∣ a ∣)

          p₁ : (p : Path K2 ∣ north ∣ ∣ north ∣)
            → p ∙ σ' n a ≡ (p ∙ ma) ∙ sym m∙
          p₁ p = (λ i → p ∙ (cong-∙ ∣_∣ₕ (merid a) (sym (merid ptEM-raw))) i)
               ∙ assoc p ma (sym m∙)

          p₂ : (p : _) → m∙ ∙ sym (p ∙ ma) ≡ sym (sym (σ' n a) ∙ p)
          p₂ p =
              (((λ i → m∙ ∙ (symDistr p ma i))
              ∙ assoc _ _ _
              ∙ (λ i → symDistr ma (sym m∙) (~ i) ∙ sym p)
              ∙ λ i → sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid ptEM-raw)) (~ i))
                     ∙ sym p)
              ∙ (isCommΩEM _ _ _))
            ∙ sym (symDistr (σ' n a) p)
            ∙ cong sym (cong (_∙ p) (sym (σ-sym n a)))

          p₃ : (p : _) → (p ≡ sym p) ≡ (p ∙ σ' n a ≡ sym (sym (σ' n a) ∙ p))
          p₃ p i = compPath-filler p (σ' n a) i
                 ≡ sym (compPath-filler' (sym (σ' n a)) p i)

      hLevCode : (a : EM-raw G (suc (suc n))) (p : 0ₖ (suc (suc n)) ≡ ∣ a ∣ₕ)
        → isOfHLevel (suc (suc n)) (Code a p)
      hLevCode =
        suspToPropElim ptEM-raw
          (λ _ → isPropΠ λ _ → isPropIsOfHLevel (2 +ℕ n))
          λ p → hLevelEM _ (2 +ℕ n) _ _ _ _

    encode-sym : (n : ℕ) (x : EM G (suc n)) (p : 0ₖ (suc n) ≡ x)
              → symCode n x p .fst
    encode-sym zero = J> refl
    encode-sym (suc n) = J> refl

  symConstEM : (n : ℕ) (x : EM G n) (p : x ≡ x) → p ≡ sym p
  symConstEM zero x p = is-set (snd G) _ _ _ _
  symConstEM (suc zero) =
    EM.EM-raw'-elim G 1
      (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (hLevelEM G 1 _ _) _ _)
    (EM-raw'-trivElim G zero (λ _ → isPropΠ λ _ → hLevelEM G 1 _ _ _ _)
     (encode-sym 0 embase))
  symConstEM (suc (suc n)) =
    EM.EM-raw'-elim G (2 +ℕ n) (λ _ → isOfHLevelΠ (3 +ℕ n)
      λ _ → isOfHLevelPath (3 +ℕ n) (hLevelEM G (2 +ℕ n) _ _) _ _)
        (EM-raw'-trivElim G (suc n)
         (λ _ → isOfHLevelΠ (2 +ℕ n) λ _ → hLevelEM G (2 +ℕ n) _ _ _ _)
          (encode-sym (suc n) ∣ north ∣))

  symConstEM-refl : {n : ℕ} → symConstEM n (0ₖ n) refl ≡ refl
  symConstEM-refl {n = zero} = isOfHLevelPath 2 (is-set (snd G)) _ _ _ _ _ _
  symConstEM-refl {n = suc zero} = transportRefl refl
  symConstEM-refl {n = suc (suc n)} = transportRefl refl

private
  module EMZ/2 = EM2 ℤ/2 -Const-ℤ/2

-ₖConst-ℤ/2 : (n : ℕ) → (x : EM ℤ/2 (suc n)) → -ₖ x ≡ x
-ₖConst-ℤ/2 = EMZ/2.-ₖConst

-ₖConst-ℤ/2-gen : (n : ℕ) → (x : EM ℤ/2 n) → -ₖ x ≡ x
-ₖConst-ℤ/2-gen zero = -Const-ℤ/2
-ₖConst-ℤ/2-gen (suc n) = -ₖConst-ℤ/2 n

symConst-ℤ/2 : (n : ℕ) (x : EM ℤ/2 n) (p : x ≡ x) → p ≡ sym p
symConst-ℤ/2 = EMZ/2.symConstEM

symConst-ℤ/2-refl : {n : ℕ} → symConst-ℤ/2 n (0ₖ n) refl ≡ refl
symConst-ℤ/2-refl = EMZ/2.symConstEM-refl

+ₖ≡id-ℤ/2 : (n : ℕ) (x : EM ℤ/2 n) → x +ₖ x ≡ 0ₖ n
+ₖ≡id-ℤ/2 zero = ℤ/2-elim refl refl
+ₖ≡id-ℤ/2 (suc n) x = cong (x +ₖ_) (sym (-ₖConst-ℤ/2 n x)) ∙ rCancelₖ (suc n) x

-- Commutativity of cup product with ℤ/2 coeffs
-ₖ^[_·_]-const : (n m : ℕ) {k : ℕ} (x : EM ℤ/2 k) → -ₖ^[ n · m ] x ≡ x
-ₖ^[_·_]-const n m x =
  ⊎.rec
   (λ p → -ₖ^[ n · m ]-even (inl p) x)
   (λ p → ⊎.rec
     (λ q → -ₖ^[ n · m ]-even (inr q) x)
     (λ q → -ₖ^[ n · m ]-odd (p , q) x ∙ -ₖConst-ℤ/2-gen _ x)
     (evenOrOdd m))
   (evenOrOdd n)

⌣ₖ-commℤ/2 : (n m : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m)
  → (x ⌣[ ℤ/2Ring R]ₖ y) ≡ subst (EM ℤ/2) (+'-comm m n) (y ⌣[ ℤ/2Ring R]ₖ x)
⌣ₖ-commℤ/2 n m x y = ⌣ₖ-comm {G'' = ℤ/2CommRing} n m x y
                   ∙ cong (subst (EM ℤ/2) (+'-comm m n))
                      (-ₖ^[ n · m ]-const _)
