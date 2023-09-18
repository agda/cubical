{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.GradedCommTensor where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; elim to ℕelim)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

open import Cubical.HITs.EilenbergMacLane1 as EM₁
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group.MorphismProperties

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open PlusBis

private
  variable
    ℓ ℓ' : Level

-- specialised lemmas
private
  -- elim rule for ℕ to help convince termination checker
  ⌣-ℕ-elim2 : {A : ℕ → ℕ → Type ℓ}
    → ((n : ℕ) → A zero n)
    → ((n : ℕ) → A (suc n) zero)
    → ((n m : ℕ) → A (suc n) m × A n (suc m) × A n m → A (suc n) (suc m))
    → (n m : ℕ) → A n m
  ⌣-ℕ-elim2 l r ind zero m = l m
  ⌣-ℕ-elim2 l r ind (suc n) zero = r n
  ⌣-ℕ-elim2 {A = A} l r ind (suc n) (suc m) =
    ind n m ((⌣-ℕ-elim2 {A = A} l r ind (suc n) m)
            , ⌣-ℕ-elim2 {A = A} l r ind n (suc m)
            , ⌣-ℕ-elim2 {A = A} l r ind n m)

  -- lemma about cong (subst ...)
  cong-subst-lem : (n m : ℕ) (q' : n ≡ m) (q : suc n ≡ suc m)
        (A : ℕ → Pointed ℓ)
        (F : (x : ℕ) → fst (A x) → fst (Ω (A (suc x))))
        (F∙ : (x : ℕ) → F x (pt (A x)) ≡ refl)
     → (x : fst (A n))
     → (s : (n m : ℕ) (q : n ≡ m)
       → snd (A m) ≡ subst (λ n₁ → A n₁ .fst) q (snd (A n)))
     → ((n : ℕ) → s n n refl ≡ sym (transportRefl _))
     → (cong (subst (λ n → A n .fst) q) (F n x))
     ≡ (sym (s _ _ q) ∙∙ F m (subst (λ n → A n .fst) q' x) ∙∙ s _ _ q)
  cong-subst-lem {ℓ} n = J> λ q → lem2 q (isSetℕ _ _ refl q)
    where
    lem2 : (q : suc n ≡ suc n) (r : refl ≡ q)
      → (A : ℕ → Pointed ℓ)
        (F : (x : ℕ) → fst (A x) → fst (Ω (A (suc x)))) →
        ((x : ℕ) → F x (pt (A x)) ≡ refl) →
        (x : fst (A n))
        (s : (n₁ m : ℕ) (q₁ : n₁ ≡ m)
            → snd (A m) ≡ subst (λ n₂ → A n₂ .fst) q₁ (snd (A n₁))) →
        ((n₁ : ℕ) → s n₁ n₁ refl ≡ sym (transportRefl (snd (A n₁)))) →
        cong (subst (λ n₁ → A n₁ .fst) q) (F n x) ≡
        (sym (s (suc n) (suc n) q) ∙∙ F n (subst (λ n₁ → A n₁ .fst) refl x)
         ∙∙ s (suc n) (suc n) q)
    lem2 = J> λ A F substId k s id
        → rUnit _
        ∙∙ (λ j → (λ i → transportRefl (snd (A (suc n))) (j ∧ i))
                ∙∙ (λ i → transportRefl (F n (transportRefl k (~ j)) i) j)
                ∙∙ λ i → transportRefl (snd (A (suc n))) (j ∧ ~ i))
        ∙∙ cong (λ p → sym p ∙∙ F n (subst (λ n₁ → A n₁ .fst) refl k) ∙∙ p)
                (sym (id (suc n)))

-- Preliminary definition of -ₖⁿ*ᵐ (easier to work with)
module _ {G' : AbGroup ℓ} where
   private
     _+G_ = _+Gr_ (snd G')
     -G_ = -Gr_ (snd G')

   -ₖ^<_·_> : (n m k : ℕ)
     → isEvenT n ⊎ isOddT n
     → isEvenT m ⊎ isOddT m
     → EM G' k → EM G' k
   -ₖ^< n · m > zero (inl x) q r = r
   -ₖ^< n · m > zero (inr x) (inl x₁) r = r
   -ₖ^< n · m > zero (inr x) (inr x₁) r = -ₖ r
   -ₖ^< n · m > (suc zero) p q =
     EM₁.rec  (AbGroup→Group G')
       (hLevelEM _ 1)
       embase
       (eml p q)
       (sq p q)
     where
     eml : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
       (g : fst G') → Path (EM G' 1) embase embase
     eml (inl x) q g = emloop g
     eml (inr x) (inl x₁) g = emloop g
     eml (inr x) (inr x₁) g = sym (emloop g)

     sq : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m) (g h : fst G')
       → Square (eml p q g) (eml p q (g +G h)) refl (eml p q h)
     sq (inl x) q g h = emcomp g h
     sq (inr x) (inl x₁) g h = emcomp g h
     sq (inr x) (inr x₁) g h =
         sym (emloop-sym _ g)
       ◁ (flipSquare (flipSquare (emcomp (-G g) (-G h))
        ▷ emloop-sym _ h)
       ▷ (cong emloop (+Comm (snd G') (-G g) (-G h)
               ∙ sym (GroupTheory.invDistr (AbGroup→Group G') g h))
       ∙ emloop-sym _ (g +G h)))
   -ₖ^< n · m > (suc (suc k)) p q =
     TR.rec (isOfHLevelTrunc (4 +ℕ k))
       λ { north → 0ₖ _
         ; south → 0ₖ _
         ; (merid a i) → loopCase p q a i}
       where
       loopCase : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
              (a : EM-raw G' (suc k))
           → Path (EM G' (suc (suc k))) (0ₖ (suc (suc k))) (0ₖ (suc (suc k)))
       loopCase (inl x) q a = EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a)
       loopCase (inr x) (inl x₁) a = EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a)
       loopCase (inr x) (inr x₁) a = sym (EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a))

   -- -ₖⁿ*ᵐ pres. 0ₖ
   -ₖ^<_·_>∙ : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
     → -ₖ^< n · m > k p q (0ₖ k) ≡ 0ₖ k
   -ₖ^< n · m >∙ zero (inl x) q = refl
   -ₖ^< n · m >∙ zero (inr x) (inl x₁) = refl
   -ₖ^< n · m >∙ zero (inr x) (inr x₁) =
     GroupTheory.inv1g (AbGroup→Group G')
   -ₖ^< n · m >∙ (suc zero) p q = refl
   -ₖ^< n · m >∙ (suc (suc k)) p q = refl

   private
     EM→ΩEM+1-PP : (k : _) (a : _)
       → PathP (λ i → EM→ΩEM+1 (suc k) (EM-raw→EM G' (suc k) a) i ≡ ∣ merid a i ∣)
                refl
                (cong ∣_∣ₕ (merid ptEM-raw))
     EM→ΩEM+1-PP k a = flipSquare (EM→ΩEM+1∘EM-raw→EM k a
           ◁ λ i j → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ i) j ∣ₕ)


   -- -ₖⁿ*ᵐ for even/odd values of n and m
   -ₖ^<_·_>-inl-left : (n m k : ℕ)
      (p : _)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^< n · m > k (inl p) q x ≡ x
   -ₖ^< n · m >-inl-left zero p q x = refl
   -ₖ^< n · m >-inl-left (suc zero) p q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ^< n · m >-inl-left (suc (suc k)) p q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → EM→ΩEM+1-PP k a i}

   -ₖ^<_·_>-inl-right : (n m k : ℕ)
      (p : _)
      (q : isEvenT m)
      (x : EM G' k)
     → -ₖ^< n · m > k p (inl q) x ≡ x
   -ₖ^< n · m >-inl-right zero (inl p) q x = refl
   -ₖ^< n · m >-inl-right (suc zero) (inl p) q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ^< n · m >-inl-right (suc (suc k)) (inl p) q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → EM→ΩEM+1-PP k a i}
   -ₖ^< n · m >-inl-right zero (inr x) q _ = refl
   -ₖ^< n · m >-inl-right (suc zero) (inr x) q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ^< n · m >-inl-right (suc (suc k)) (inr x) q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → EM→ΩEM+1-PP k a i}

   -ₖ^<_·_>-inr : (n m k : ℕ)
      (p : _)
      (q : isOddT m)
      (x : EM G' k)
     → -ₖ^< n · m > k (inr p) (inr q) x ≡ -ₖ x
   -ₖ^< n · m >-inr zero p q x = refl
   -ₖ^< n · m >-inr (suc zero) p q x = refl
   -ₖ^< n · m >-inr (suc (suc k)) p q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl ; south → refl ; (merid a i) j → l2 k a j i}
       where
       l2 : (k : ℕ) (a : EM-raw G' (suc k))
         → cong (-ₖ^< n · m > (suc (suc k)) (inr p) (inr q)) (cong ∣_∣ₕ (merid a))
          ≡ cong -ₖ_ (cong ∣_∣ₕ (merid a))
       l2 zero a = refl
       l2 (suc k) a = refl

   cong-ₖ^<_·_>₂ : (n m k : ℕ)
       (p : isEvenT n ⊎ isOddT n)
       (q : isEvenT m ⊎ isOddT m)
      → (x : EM G' (suc k))
      → cong (-ₖ^< n · m > (suc (suc k)) p q) (EM→ΩEM+1 (suc k) x)
      ≡ EM→ΩEM+1 (suc k) (-ₖ^< n · m > (suc k) p q x)
   cong-ₖ^< n · m >₂ k (inl p) q x =
     (λ i j → -ₖ^< n · m >-inl-left (suc (suc k)) p q (EM→ΩEM+1 (suc k) x j) i)
     ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^< n · m >-inl-left (suc k) p q x))
   cong-ₖ^< n · m >₂ k (inr p) (inl q) x =
     (λ i j → -ₖ^< n · m >-inl-right (suc (suc k)) (inr p) q
                (EM→ΩEM+1 (suc k) x j) i)
     ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^< n · m >-inl-right (suc k) (inr p) q x))
   cong-ₖ^< n · m >₂ k (inr p) (inr q) x =
     (λ i j → -ₖ^< n · m >-inr (suc (suc k)) p q
                (EM→ΩEM+1 (suc k) x j) i)
           ∙∙ cong-₂ k (EM→ΩEM+1 (suc k) x)
           ∙∙ sym (EM→ΩEM+1-sym (suc k) x)
            ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^< n · m >-inr (suc k) p q x))

   -- -ₖⁿ*ᵐ is its own inverse
   -ₖ^<_·_>² : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^< n · m > k p q (-ₖ^< n · m > k p q x) ≡ x
   -ₖ^< n · m >² k (inl x₁) q x =
       -ₖ^< n · m >-inl-left k x₁ q _
     ∙ -ₖ^< n · m >-inl-left k x₁ q x
   -ₖ^< n · m >² k (inr x₁) (inl x₂) x =
       -ₖ^< n · m >-inl-right k (inr x₁) x₂ _
     ∙ -ₖ^< n · m >-inl-right k (inr x₁) x₂ x
   -ₖ^< n · m >² k (inr x₁) (inr x₂) x =
       -ₖ^< n · m >-inr k x₁ x₂ _
     ∙ cong -ₖ_ (-ₖ^< n · m >-inr k x₁ x₂ x)
     ∙ -ₖ² k x

   -- so is -ₖᵐ*ⁿ
   -ₖ^<_·_>²-swap : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^< n · m > k p q (-ₖ^< m · n > k q p x) ≡ x
   -ₖ^< n · m >²-swap k (inl p) q x =
       -ₖ^< n · m >-inl-left k p q _
     ∙ -ₖ^< m · n >-inl-right k q p x
   -ₖ^< n · m >²-swap k (inr p) (inl q) x =
       -ₖ^< n · m >-inl-right k (inr p) q _
     ∙ -ₖ^< m · n >-inl-left k q (inr p) x
   -ₖ^< n · m >²-swap k (inr p) (inr q) x =
       -ₖ^< n · m >-inr k p q _
     ∙ cong -ₖ_ (-ₖ^< m · n >-inr k q p _)
     ∙ -ₖ² k x

   -- Another common construction (ΩKₙ → Ω²Kₙ₊₁)
   wrap : (n : ℕ) (p : Path (EM G' n) (0ₖ n) (0ₖ n))
     → typ ((Ω^ 2) (EM∙ G' (suc n)))
   wrap n p = sym (EM→ΩEM+1-0ₖ n) ∙∙ cong (EM→ΩEM+1 n) p ∙∙ EM→ΩEM+1-0ₖ n

   wrapEq : (n : ℕ) (p q : EM→ΩEM+1 {G = G'} n (0ₖ n) ≡ EM→ΩEM+1 n (0ₖ n))
     → p ≡ q → sym (EM→ΩEM+1-0ₖ n) ∙∙ p ∙∙ EM→ΩEM+1-0ₖ n
              ≡ (sym (EM→ΩEM+1-0ₖ n) ∙∙ q ∙∙ EM→ΩEM+1-0ₖ n)
   wrapEq n p q r = cong (sym (EM→ΩEM+1-0ₖ n) ∙∙_∙∙ EM→ΩEM+1-0ₖ n) r

   pp-wrap : (n : ℕ) (p : Path (EM G' n) (0ₖ n) (0ₖ n))
           → PathP (λ i → EM→ΩEM+1-0ₖ n i ≡ EM→ΩEM+1-0ₖ n i)
                    (cong (EM→ΩEM+1 n) p) (wrap n p)
   pp-wrap n p =
     doubleCompPath-filler
       (sym (EM→ΩEM+1-0ₖ n)) (cong (EM→ΩEM+1 n) p) (EM→ΩEM+1-0ₖ n)

   -- cong² -ₖⁿ*ᵐ commutes with wrap
   cong-cong-ₖ^<_·_>₂ : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
      → (x : Path (EM G' (2 +ℕ k)) (0ₖ (2 +ℕ k)) (0ₖ (2 +ℕ k)))
      → cong (cong (-ₖ^< n · m > (suc (suc (suc k))) p q)) (wrap (suc (suc k)) x)
      ≡ wrap (suc (suc k)) (cong (-ₖ^< n · m > (suc (suc k)) p q) x)
   cong-cong-ₖ^< n · m >₂ k (inl p) q x =
       (λ r i j → -ₖ^< n · m >-inl-left (suc (suc (suc k))) p q
                     (wrap (suc (suc k)) x i j) r)
     ∙ cong (wrap (suc (suc k)))
       λ r i → -ₖ^< n · m >-inl-left (suc (suc k)) p q (x i) (~ r)
   cong-cong-ₖ^< n · m >₂ k (inr p) (inl q) x =
     (λ r i j → -ₖ^< n · m >-inl-right (suc (suc (suc k))) (inr p) q
                     (wrap (suc (suc k)) x i j) r)
     ∙ cong (wrap (suc (suc k)))
       λ r i → -ₖ^< n · m >-inl-right (suc (suc k)) (inr p) q (x i) (~ r)
   cong-cong-ₖ^< n · m >₂ k (inr p) (inr q) x =
       (λ r i j → -ₖ^< n · m >-inr (suc (suc (suc k))) p q
                     (wrap (suc (suc k)) x i j) r)
     ∙ rUnit _
     ∙ (λ r →
          ((λ i j → cong-₂ (suc k) refl (r ∧ i) j))
       ∙∙ (λ i j → cong-₂ (suc k) (wrap (suc (suc k)) x i) r j)
       ∙∙ λ i j → cong-₂ (suc k) refl (r ∧ ~ i) j)
     ∙ cong₂ (λ x y → x ∙∙ y ∙∙ sym x)
             (transportRefl refl)
             (sym (sym≡cong-sym (wrap (suc (suc k)) x)))
     ∙ sym (rUnit _)
     ∙ cong (wrap (suc (suc k)))
            (sym ((λ r i → -ₖ^< n · m >-inr (suc (suc k)) p q (x i) r)
                ∙ cong-₂ k x))

    -- A key lemma for graded commutativity of ⌣ₖ
   ⌣ₖ-comm-final-lem : (n m k : ℕ)
          (p : _) (q : _) (p' : _) (q' : _)
          (x : EM G' k)
       → -ₖ^< n · suc m > k p' q x
       ≡ -ₖ^< suc n · suc m > k p q
         (-ₖ -ₖ^< suc n · m > k p q'
           (-ₖ^< n · m > k p' q' x))
   ⌣ₖ-comm-final-lem n m k (inl p) q (inl p') q' x =
     ⊥.rec (¬evenAndOdd n (p' , p))
   ⌣ₖ-comm-final-lem n m k (inl p) (inl q) (inr p') (inl q') x =
     ⊥.rec (¬evenAndOdd m (q' , q))
   ⌣ₖ-comm-final-lem n m k (inl p) (inl q) (inr p') (inr q') x =
       -ₖ^< n · suc m >-inl-right k (inr p') q x
     ∙ sym (-ₖ^< suc n · suc m >-inl-left k p (inl q) _
           ∙ cong -ₖ_ (-ₖ^< suc n · m >-inl-left k p (inr q') _
                     ∙ -ₖ^< n · m >-inr k p' q' x)
           ∙ -ₖ² k x)
   ⌣ₖ-comm-final-lem n m k (inl p) (inr q) (inr p') (inl q') x =
       -ₖ^< n · suc m >-inr k p' q x
     ∙ cong -ₖ_ (sym (-ₖ^< suc n · m >-inl-left k p (inl q') _
              ∙ -ₖ^< n · m >-inl-right k (inr p') q' x))
     ∙ sym (-ₖ^< suc n · suc m >-inl-left k p (inr q) _)
   ⌣ₖ-comm-final-lem n m k (inl p) (inr q) (inr p') (inr q') x =
     ⊥.rec (¬evenAndOdd m (q , q'))
   ⌣ₖ-comm-final-lem n m k (inr p) (inl q) (inl p') (inl q') x =
     ⊥.rec (¬evenAndOdd (suc m) (q , q'))
   ⌣ₖ-comm-final-lem n m k (inr p) (inl q) (inl p') (inr q') x =
     -ₖ^< n · suc m >-inl-left k p' (inl q) x
     ∙ sym (-ₖ^< suc n · suc m >-inl-right k (inr p) q _
          ∙ cong -ₖ_
             (-ₖ^< suc n · m >-inr k p q' _
             ∙ cong -ₖ_ (-ₖ^< n · m >-inl-left k p' (inr q') x))
          ∙ -ₖ² k x)
   ⌣ₖ-comm-final-lem n m k (inr p) (inr q) (inl p') (inl q') x =
       -ₖ^< n · suc m >-inl-left k p' (inr q) x
     ∙ sym (-ₖ^< suc n · suc m >-inr k p q _
          ∙ -ₖ² k _
          ∙ -ₖ^< suc n · m >-inl-right k (inr p) q' _
          ∙ -ₖ^< n · m >-inl-left k p' (inl q') x)
   ⌣ₖ-comm-final-lem n m k (inr p) (inr q) (inl p') (inr q') x =
     ⊥.rec (¬evenAndOdd m (q , q'))
   ⌣ₖ-comm-final-lem n m k (inr p) q (inr p') q' x =
     ⊥.rec (¬evenAndOdd (suc n) (p' , p))

-- Commutativity of -ₖⁿ*ᵐ with functions EM n G → EM n H
-- induced by homs G → H
-ₖ^<_·_>-Induced : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'}
  (n m k : ℕ) (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
  (ϕ : AbGroupHom G H) (x : EM G k)
  → inducedFun-EM ϕ k (-ₖ^< n · m > k p q x)
   ≡ -ₖ^< n · m > k p q (inducedFun-EM ϕ k x)
-ₖ^< n · m >-Induced k (inl x₁) q ϕ x =
  cong (inducedFun-EM ϕ k) (-ₖ^< n · m >-inl-left k x₁ q x)
  ∙ sym (-ₖ^< n · m >-inl-left k x₁ q _)
-ₖ^< n · m >-Induced k (inr x₁) (inl x₂) ϕ x =
  cong (inducedFun-EM ϕ k) (-ₖ^< n · m >-inl-right k (inr x₁) x₂ x)
  ∙ sym (-ₖ^< n · m >-inl-right k (inr x₁) x₂ _)
-ₖ^< n · m >-Induced k (inr x₁) (inr x₂) ϕ x =
    cong (inducedFun-EM ϕ k) (-ₖ^< n · m >-inr k x₁ x₂ x)
  ∙ inducedFun-EM-pres-ₖ ϕ k x
  ∙ sym (-ₖ^< n · m >-inr k x₁ x₂ _)


-- Truncation elimination principle for graded commutativity
⌣ₖ-comm-ind : {G' : AbGroup ℓ} {H' : AbGroup ℓ'} (n m : ℕ)
  → (f g : EM∙ G' (suc n) →∙ (EM∙ H' (suc m)
                           →∙ EM∙ (G' ⨂ H') (suc n +' suc m) ∙))
  → ((x : EM-raw' G' (suc n)) (y : EM-raw' H' (suc m))
  → f .fst (EM-raw'→EM _ _ x) .fst (EM-raw'→EM _ _ y)
   ≡ g .fst (EM-raw'→EM _ _ x) .fst (EM-raw'→EM _ _ y))
  → f ≡ g
⌣ₖ-comm-ind {G' = G'} {H' = H'} n m f g ind =
  →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
      (funExt (EM-raw'-elim G' (suc n)
        (λ _ → isOfHLevelPath' (suc (suc n))
                 (isOfHLevel↑∙ (suc n) m) _ _)
        λ x → →∙Homogeneous≡ (isHomogeneousEM _)
          (funExt λ y i → f'≡g' y i .fst x)))
  where
  f' : EM H' (suc m)
    → EM-raw'∙ G' (suc n) →∙ EM∙ (G' ⨂ H') (suc n +' suc m)
  fst (f' y) x = f .fst (EM-raw'→EM _ _ x) .fst y
  snd (f' y) = cong (λ x → f .fst x .fst y) (EM-raw'→EM∙ G' (suc n))
             ∙ funExt⁻ (cong fst (f .snd)) y

  g' : EM H' (suc m)
    → EM-raw'∙ G' (suc n) →∙ EM∙ (G' ⨂ H') (suc n +' suc m)
  fst (g' y) x = g .fst (EM-raw'→EM _ _ x) .fst y
  snd (g' y) = cong (λ x → g .fst x .fst y) (EM-raw'→EM∙ G' (suc n))
             ∙ funExt⁻ (cong fst (g .snd)) y

  f'≡g' : (x : EM H' (suc m)) → f' x ≡ g' x
  f'≡g' = EM-raw'-elim H' (suc m)
           (λ _ → isOfHLevelPath' (suc (suc m))
             (subst (λ x → isOfHLevel (2 +ℕ suc m)
                    (EM-raw'∙ G' (suc n) →∙ EM∙ (G' ⨂ H') x))
               (cong suc (+-comm m (suc n)))
               (isOfHLevel↑∙' {G = G'} {H = G' ⨂ H'} (suc m) (suc n))) _ _)
           λ y → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ x → ind x y)


module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   -- cup product, pointed
   cp∙ : (n m : ℕ) → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cp∙ = cup∙

   cp∙∙ : (n m : ℕ) → EM∙ G' n →∙ (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
   fst (cp∙∙ n m) = cp∙ n m
   snd (cp∙∙ n m) = ptd
     where
     abstract
       ptd : cp∙ n m (snd (EM∙ G' n)) ≡ ((λ _ → 0ₖ (n +' m)) , refl)
       ptd = →∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ y → 0ₖ-⌣ₖ n m y)

   -- commuting cup product, pointed
   cp'∙ : (n m : ℕ) → EM G' n → EM∙ H' m →∙ EM∙ (H' ⨂ G') (m +' n)
   fst (cp'∙ n m x) y = y ⌣ₖ x
   snd (cp'∙ n m x) = 0ₖ-⌣ₖ m n x

   -- some commutativity lemmas
   comm⨂-EM : (n : ℕ) → EM (H' ⨂ G') n → EM (G' ⨂ H') n
   comm⨂-EM n = Iso.fun (Iso→EMIso ⨂-comm _)

   comm⨂-EM' : (n : ℕ) → EM (H' ⨂ G') n → EM (G' ⨂ H') n
   comm⨂-EM' = λ n → Iso.inv (Iso→EMIso ⨂-comm _)

   comm⨂-EM≡comm⨂-EM' : (n : ℕ) (x : _) → comm⨂-EM n x ≡ comm⨂-EM' n x
   comm⨂-EM≡comm⨂-EM' n =
     funExt⁻ (cong (λ F → inducedFun-EM F n) h)
     where
     h : Path (AbGroupHom (H' ⨂ G') (G' ⨂ H'))
              (GroupEquiv→GroupHom ⨂-comm)
              (GroupEquiv→GroupHom (invGroupEquiv ⨂-comm))
     h = Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

   -- cong² comm⨂-EM commutes with wrap
   cong-cong-comm⨂-EM : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
     → cong (cong (comm⨂-EM (suc (suc (suc n))))) (wrap (suc (suc n)) p)
     ≡ wrap (suc (suc n)) (cong (comm⨂-EM (suc (suc n))) p)
   cong-cong-comm⨂-EM n p =
     TR.rec (hLevelEM _ (suc (suc (suc n))) _ _ _ _ _ _)
       (uncurry (λ x q k i j
         → hcomp (λ r → λ {
                 (i = i0) → comm⨂-EM (suc (suc (suc n)))
                              (EM→ΩEM+1-0ₖ (suc (suc n)) (r ∨ k) j)
               ; (i = i1) → comm⨂-EM (suc (suc (suc n)))
                              (EM→ΩEM+1-0ₖ (suc (suc n)) (r ∨ k) j)
               ; (j = i0) → 0ₖ (3 +ℕ n)
               ; (j = i1) → 0ₖ (3 +ℕ n)
               ; (k = i0) → comm⨂-EM (suc (suc (suc n)))
                              (pp-wrap (2 +ℕ n) (q r) r i j)
               ; (k = i1) → wrap (suc (suc n))
                              (cong (comm⨂-EM (suc (suc n))) (q r)) i j})
             (hcomp (λ r → λ {(i = i0) → comm⨂-EM (suc (suc (suc n)))
                               ∣ rCancel-filler (merid north) r k j ∣ₕ
               ; (i = i1) → comm⨂-EM (suc (suc (suc n)))
                               ∣ rCancel-filler (merid north) r k j ∣ₕ
               ; (j = i0) → 0ₖ (3 +ℕ n)
               ; (j = i1) → ∣ merid north (~ r ∧ ~ k) ∣ₕ
               ; (k = i0) → comm⨂-EM (suc (suc (suc n)))
                             ∣ compPath-filler (merid (x i))
                               (sym (merid north)) r j ∣ₕ
               ; (k = i1) → wrap (suc (suc n)) (cong (comm⨂-EM (suc (suc n)))
                                  (cong ∣_∣ₕ x)) i j})
               (hcomp (λ r → λ {
                  (i = i0) → ∣ rCancel-filler (merid north) (~ r) k j ∣ₕ
                ; (i = i1) → ∣ rCancel-filler (merid north) (~ r) k j ∣ₕ
                ; (j = i0) → 0ₖ (3 +ℕ n)
                ; (j = i1) → ∣ merid north (r ∧ ~ k) ∣ₕ
                ; (k = i0) → ∣ compPath-filler
                               (merid (inducedFun-EM-raw
                                       (GroupEquiv→GroupHom ⨂-comm)
                                 (suc (suc n)) (x i)))
                                 (sym (merid north)) (~ r) j ∣ₕ
                ; (k = i1) → wrap (suc (suc n))
                              (cong (comm⨂-EM (suc (suc n))) (cong ∣_∣ₕ x)) i j})
                (pp-wrap (suc (suc n))
                   (cong (comm⨂-EM (suc (suc n))) (cong ∣_∣ₕ x)) k i j)))))
       (ind-lem n p)
         where
         ind-lem : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
           → hLevelTrunc (2 +ℕ n)
            (Σ[ x ∈ north ≡ north ] cong ∣_∣ₕ x ≡ p)
         ind-lem n p =
           TR.map (λ {(x , p) → (fst (ind-lem₃ n x))
                   , (sym (snd (ind-lem₃ n x)) ∙ p)})
                  (ind-lem₂ n p (ind-lem₁ n p))
           where
           ind-lem₁ : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
                → Σ[ x ∈ EM (H' ⨂ G') (suc n) ] EM→ΩEM+1 (suc n) x ≡ p
           ind-lem₁ n p = _ , Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) p

           ind-lem₂ : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
                 → Σ[ x ∈ EM (H' ⨂ G') (suc n) ] EM→ΩEM+1 (suc n) x ≡ p
                 → hLevelTrunc (2 +ℕ n) (Σ[ x ∈ EM-raw' (H' ⨂ G') (suc n) ]
                     EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x) ≡ p)
           ind-lem₂ n p =
             uncurry (EM-raw'-elim _ _
               (λ _ → isOfHLevelΠ (2 +ℕ n)
                λ _ → (isOfHLevelTrunc (2 +ℕ n)))
               λ x → J (λ p _ → hLevelTrunc (2 +ℕ n)
                                  (Σ[ x ∈ EM-raw' (H' ⨂ G') (suc n) ]
                     EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x) ≡ p))
                 ∣ x , refl ∣)

           ind-lem₃ : (n : ℕ)
                   (x : EM-raw' (H' ⨂ G') (suc n))
                → Σ[ r ∈ north ≡ north ] EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x)
                 ≡ cong ∣_∣ₕ r
           ind-lem₃ zero x = _ , refl
           ind-lem₃ (suc n) x = _ , refl

   -- commuting cup product, doubly pointed
   cp'∙∙ : (n m : ℕ) (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
     → EM∙ G' n →∙ (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
   fst (fst (cp'∙∙ n m p q) x) y =
     subst (EM (G' ⨂ H')) (+'-comm m n)
       (-ₖ^< n · m > (m +' n) p q
       (comm⨂-EM (m +' n) (y ⌣ₖ x)))
   snd (fst (cp'∙∙ n m p q) x) =
     cong (subst (EM (G' ⨂ H')) (+'-comm m n))
        (cong (-ₖ^< n · m > (m +' n) p q)
          (cong (comm⨂-EM (m +' n)) (0ₖ-⌣ₖ m n x) ∙ Iso→EMIso∙ ⨂-comm _)
         ∙ -ₖ^< n · m >∙ (m +' n) p q)
      ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
        (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _)
   snd (cp'∙∙ n m p q) =
     →∙Homogeneous≡ (isHomogeneousEM _)
       (funExt λ y
       → cong (subst (EM (G' ⨂ H')) (+'-comm m n))
        (cong (-ₖ^< n · m > (m +' n) p q)
          (cong (comm⨂-EM (m +' n)) (⌣ₖ-0ₖ m n y) ∙ Iso→EMIso∙ ⨂-comm _)
         ∙ -ₖ^< n · m >∙ (m +' n) p q)
      ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
        (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _))

   flip-⌣ₖ-comm : (n m n' m' : ℕ) (l r : ℕ) (s : l ≡ r)
        (x : EM (H' ⨂ G') l) (y : EM (G' ⨂ H') r)
        (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
        (p' : isEvenT n' ⊎ isOddT n') (q' : isEvenT m' ⊎ isOddT m')
     → y ≡ subst (EM (G' ⨂ H')) s (-ₖ^< n' · m' > l p' q' (comm⨂-EM l x))
     → subst (EM (G' ⨂ H')) s (-ₖ^< n · m > l p q (comm⨂-EM l x))
      ≡ -ₖ^< n · m > r p q (-ₖ^< n' · m' > r p' q' y)
   flip-⌣ₖ-comm n m n' m' l = J> λ x y p q p' q' id
    → transportRefl _
    ∙ sym (cong (-ₖ^< n · m > l p q) (-ₖ^< n' · m' >² l p' q' (comm⨂-EM l x)))
    ∙ sym (cong (λ y → -ₖ^< n · m > l p q
                         (-ₖ^< n' · m' > l p' q' y))
          (id ∙ transportRefl _))


   -- Finally, graded commutativity proofs:
   -- graded commutativity of ⌣ₖ with one arg in dim 0.
   ⌣ₖ-comm₀ : (m : ℕ) (x : fst G') (y : EM H' (suc m))
     → cp∙ zero (suc m) x .fst y
      ≡ comm⨂-EM (suc m) (cp'∙ zero (suc m) x .fst y)
   ⌣ₖ-comm₀ zero x =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl
         ; (emloop-raw g i) j → EM→ΩEM+1 _ (x ⊗ g) i}
   ⌣ₖ-comm₀ (suc m) x =
     TR.elim
       (λ _ → isOfHLevelPath (4 +ℕ m) (hLevelEM _ (suc (suc m))) _ _)
       λ { north → refl
         ; south → refl
         ; (merid a i) j → lem a j i}
       where
       lem : (a : EM-raw H' (suc m))
         → EM→ΩEM+1 (suc m) (cp∙ zero (suc m) x .fst (EM-raw→EM _ _ a))
         ≡ cong (comm⨂-EM (suc (suc m)))
            (EM→ΩEM+1 (suc m) (cp'∙ zero (suc m) x
              .fst (EM-raw→EM _ _ a)))
       lem a = cong (EM→ΩEM+1 (suc m)) (⌣ₖ-comm₀ m x (EM-raw→EM _ _ a))
          ∙ EMFun-EM→ΩEM+1 (suc m) (cp'∙ zero (suc m) x .fst (EM-raw→EM _ _ a))

   -- graded commutativity of ⌣ₖ with one arg in dim 1.
   ⌣ₖ-comm₁ : (m : ℕ) (p : isEvenT m ⊎ isOddT m)
     → cp∙∙ 1 m ≡ cp'∙∙ 1 m (inr tt) p
   ⌣ₖ-comm₁ =
     elim+2 (λ { (inl x) →
             →∙Homogeneous≡
               (isHomogeneous→∙ (isHomogeneousEM _))
                 (funExt (EM-raw'-elim _ 1
                   (λ _ → isOfHLevelPath' 2 (isOfHLevel→∙ 3 (hLevelEM _ 1)) _ _)
                     λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                       (funExt λ y
                     → 1-0 x y
                     ∙∙ sym (-ₖ^< 1 · zero >-inl-right 1
                         (inr tt) tt (comm⨂-EM 1
                           (_⌣ₖ_ {n = zero} {m = suc zero}
                            y (EM-raw'→EM G' (suc zero) x))))
                     ∙∙ sym (transportRefl
                         (-ₖ^< 1 · zero > 1 (inr tt) (inl tt)
                         (comm⨂-EM 1 (_⌣ₖ_ {n = zero} {m = suc zero} y
                         (EM-raw'→EM G' (suc zero) x))))))))})
          (λ { (inr x)
             → ⌣ₖ-comm-ind 0 0 _ _
              λ x y → 1-1 x y
                     ∙ sym (transportRefl
                       (-ₖ^< 1 · 1 > 2 (inr tt) (inr tt)
                       (comm⨂-EM 2 (_⌣ₖ_ {n = suc zero} {m = suc zero}
                         (EM-raw'→EM H' (suc zero) y)
                       (EM-raw'→EM G' (suc zero) x)))))})
          λ { n ind p → ⌣ₖ-comm-ind 0 (suc n) _ _ (1-suc n ind p)}

     where
     -- dimensions (0,1)
     1-0 : (x : EM-raw' G' 1) (y : fst H')
        → cp∙ 1 0 (EM-raw'→EM G' 1 x) .fst y
         ≡ comm⨂-EM 1 (_⌣ₖ_ {n = zero} y (EM-raw'→EM G' 1 x))
     1-0 embase-raw y = refl
     1-0 (emloop-raw g i) y = refl

     -- dimensions (1,1)
     1-1 : (x : EM-raw' G' 1) (y : EM-raw' H' 1)
       → cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst (EM-raw'→EM H' (suc 0) y)
         ≡ -ₖ^< 1 · 1 > 2 (inr tt) (inr tt)
           (comm⨂-EM 2
             (_⌣ₖ_ {n = suc zero} {m = suc zero}
               (EM-raw'→EM H' 1 y) (EM-raw'→EM G' 1 x)))
     1-1 x embase-raw = ⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x)
     1-1 x (emloop-raw h i) = flipSquare PP2 i
       where
       PP1 : (x : EM-raw' G' 1)
         → PathP (λ i → Path (EM (G' ⨂ H') 2)
                  (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i)
                  (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i))
                (cong (cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst)
                      (emloop h))
                (EM→ΩEM+1 (suc 0)
                 (-ₖ (comm⨂-EM 1
                 (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)))))
       PP1 embase-raw = sym (EM→ΩEM+1-0ₖ 1)
       PP1 (emloop-raw g i) j k =
         hcomp (λ r → λ {
            (i = i0) → ∣ rCancel (merid embase) (~ j ∨ ~ r) k ∣
          ; (i = i1) → ∣ rCancel (merid embase) (~ j ∨ ~ r) k ∣
          ; (j = i0) → pp-wrap 1 (λ i →
                         (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i)))
                         (~ r) k i
          ; (j = i1) → pp-wrap 1 (λ i →
                         (-ₖ (comm⨂-EM 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i)))))
                         (~ r) i k
          ; (k = i0) → ⌣ₖ-0ₖ 1 1 (emloop g i) (j ∨ ~ r)
          ; (k = i1) → ⌣ₖ-0ₖ 1 1 (emloop g i) (j ∨ ~ r)})
               (help j i k)
        where
        help : flipSquare (wrap 1 λ i → (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i)))
             ≡ wrap 1 λ i →
                (-ₖ (comm⨂-EM 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i))))
        help =
            sym (sym≡flipSquare (wrap 1 λ i →
                                  (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i))))
          ∙ wrapEq 1 _ _
             (cong (cong (EM→ΩEM+1 1))
               (sym (cong-₁ (λ i →
                     comm⨂-EM 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i))))))

       PP2 : PathP (λ i → Path (EM (G' ⨂ H') 2)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i))
                   (cong (cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst)
                         (emloop h))
                   (λ i → -ₖ^< 1 · 1 > 2 (inr tt) (inr tt)
                       (comm⨂-EM 2 (EM→ΩEM+1 (suc zero)
                       (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)) i)))
       PP2 = PP1 x
         ▷ (sym (cong-ₖ^< 1 · 1 >₂ 0 (inr tt) (inr tt)
                (comm⨂-EM 1
                 (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)))))
              ∙ cong (cong (-ₖ^< 1 · 1 > 2 (inr tt) (inr tt)))
                     (EMFun-EM→ΩEM+1 1 (_⌣ₖ_ {n = zero} {m = suc zero}
                                        h (EM-raw'→EM G' 1 x)))
     -- higher cases
     module _ (n : ℕ)
       (ind : (p : isEvenT (suc n) ⊎ isOddT (suc n))
            → cp∙∙ 1 (suc n) ≡ cp'∙∙ 1 (suc n) (inr tt) p)
       where
       south-c : (x : EM-raw' G' 1) (p : _)
        → cp∙∙ 1 (suc (suc n)) .fst (EM-raw'→EM G' (suc 0) x) .fst
           (EM-raw'→EM H' (suc (suc n)) south)
         ≡ cp'∙∙ 1 (suc (suc n)) (inr tt) p .fst (EM-raw'→EM G' (suc 0) x)
           .fst (EM-raw'→EM H' (suc (suc n)) south)
       south-c embase-raw p = refl
       south-c (emloop-raw g i) p j = EM→ΩEM+1-0ₖ (suc (suc n)) j i

       1-suc : (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
               (x : EM-raw' G' (suc zero))
               (y : EM-raw' H' (suc (suc n)))
            → cp∙∙ 1 (suc (suc n)) .fst
               (EM-raw'→EM G' (suc 0) x) .fst
               (EM-raw'→EM H' (suc (suc n)) y)
             ≡ cp'∙∙ 1 (suc (suc n)) (inr tt) p .fst
                (EM-raw'→EM G' (suc 0) x) .fst
                (EM-raw'→EM H' (suc (suc n)) y)
       1-suc p x north = ⌣ₖ-0ₖ 1 (suc (suc n)) (EM-raw'→EM G' (suc 0) x)
       1-suc p x south = south-c x p
       1-suc p x (merid a i) j = main j i
         where
         good : (x : EM-raw' G' 1)
           → PathP (λ i₁ →
                  ⌣ₖ-0ₖ 1 (suc (suc n)) (EM-raw'→EM G' (suc 0) x) i₁ ≡
                  south-c x p i₁)
               (λ i₁ →
                  cp∙∙ 1 (suc (suc n)) .fst (EM-raw'→EM G' (suc 0) x) .fst
                  (EM-raw'→EM H' (suc (suc n)) (merid a i₁)))
               (sym
                (EM→ΩEM+1 (suc (suc n))
                 (fst (fst (cp∙∙ 1 (suc n)) (EM-raw'→EM G' 1 x))
                  (EM-raw→EM H' (suc n) a))))
         good embase-raw j k = EM→ΩEM+1-0ₖ (suc (suc n)) (~ j) (~ k)
         good (emloop-raw g i) j k =
           hcomp (λ r → λ {
               (i = i0) → ∣ rCancel (merid north) (~ j ∨ ~ r) (~ k) ∣
             ; (i = i1) → ∣ rCancel (merid north) (~ j ∨ ~ r) (~ k) ∣
             ; (j = i0) → l-f (~ r) k i
             ; (j = i1) → l-f (~ r) i (~ k)
             ; (k = i0) → ∣ rCancel (merid north) (j ∨ ~ r) i ∣
             ; (k = i1) → ∣ rCancel (merid north) (j ∨ ~ r) i ∣})
              (flipSq-lem j i k)

           where
           l-f = pp-wrap (suc (suc n))
                  (EM→ΩEM+1 (suc n)
                   (_⌣ₖ_ {G' = G'} {H' = H'} {n = 0} {m = suc n}
                     g (EM-raw→EM H' (suc n) a)))
           l = wrap (suc (suc n)) (EM→ΩEM+1 (suc n)
                (_⌣ₖ_ {n = 0} {m = suc n} g (EM-raw→EM H' (suc n) a)))

           flipSq-lem : flipSquare l ≡ cong sym l
           flipSq-lem = sym (sym≡flipSquare l) ∙ sym≡cong-sym l

         -ₖ-lem : (n : ℕ) (p : _) (q : _)
           →  -ₖ^< 1 · suc (suc n) > (1 +' suc n) (inr tt) p
             ∘ (-ₖ^< 1 · suc n > (1 +' suc n) (inr tt) q)
             ≡ -ₖ_ {G = G' ⨂ H'}
         -ₖ-lem n (inl x) (inl x₁) = ⊥.rec (¬evenAndOdd _ (x , x₁))
         -ₖ-lem n (inl x) (inr x₁) i z =
           -ₖ^< 1 · suc (suc n) >-inl-right (1 +' suc n) (inr tt) x
             (-ₖ^< 1 · suc n >-inr (1 +' suc n) tt x₁ z i) i
         -ₖ-lem n (inr x) (inl x₁) i z =
           -ₖ^< 1 · suc (suc n) >-inr (1 +' suc n) tt x
             (-ₖ^< 1 · suc n >-inl-right (1 +' suc n) (inr tt) x₁ z i) i
         -ₖ-lem n (inr x) (inr x₁) = ⊥.rec (¬evenAndOdd _ (x , x₁))

         main : PathP (λ i → ⌣ₖ-0ₖ 1 (suc (suc n)) (EM-raw'→EM G' (suc 0) x) i
                           ≡ south-c x p i)
                 (λ i → cp∙∙ 1 (suc (suc n)) .fst (EM-raw'→EM G' (suc 0) x) .fst
                          (EM-raw'→EM H' (suc (suc n)) (merid a i)))
                 λ i → cp'∙∙ 1 (suc (suc n)) (inr tt) p .fst
                          (EM-raw'→EM G' (suc 0) x) .fst
                          (EM-raw'→EM H' (suc (suc n)) (merid a i))
         main = good x
          ▷ ((sym (EM→ΩEM+1-sym (suc (suc n))
                 (fst (fst (cp∙∙ 1 (suc n)) (EM-raw'→EM G' 1 x))
                  (EM-raw→EM H' (suc n) a)))
           ∙ cong (EM→ΩEM+1 (suc (suc n)))
              (sym (funExt⁻
                (-ₖ-lem n p (evenOrOdd (suc n)))
                  ((fst (fst (cp∙∙ 1 (suc n)) (EM-raw'→EM G' 1 x))
                             (EM-raw→EM H' (suc n) a))))))
           ∙ cong (EM→ΩEM+1 (suc (suc n)))
             (sym (flip-⌣ₖ-comm 1 (suc (suc n)) 1 (suc n) _ _
               (+'-comm (suc n) 1) a⌣x (_⌣ₖ_ {n = 1} {m = suc n}
               (EM-raw'→EM G' (suc zero) x) (EM-raw→EM H' (suc n) a))
               (inr tt) p (inr tt) (evenOrOdd (suc n))
               (funExt⁻
                (cong fst (funExt⁻
                 (cong fst (ind (evenOrOdd (suc n))))
                  (EM-raw'→EM G' 1 x))) (EM-raw→EM H' (suc n) a))))
           ∙ sym main-lem
           ∙ cong (cong (subst (EM (G' ⨂ H')) (+'-comm (suc (suc n)) 1)))
               (sym (cong-ₖ^< 1 · (suc (suc n)) >₂ (suc (n +ℕ 0)) (inr tt) p
                     (comm⨂-EM (suc (suc (n +ℕ 0))) a⌣x))
               ∙ cong (cong (-ₖ^< 1 · (suc (suc n)) > ((suc (suc n)) +' 1)
                                                      (inr tt) p))
                  (EMFun-EM→ΩEM+1 _ a⌣x)))

           where
           a⌣x = _⌣ₖ_ {n = suc n} {m = 1}
                  (EM-raw→EM H' (suc n) a) (EM-raw'→EM G' (suc zero) x)

           mid = EM→ΩEM+1 (suc (suc (n +ℕ 0)))
                  (-ₖ^< 1 · suc (suc n) > (suc (suc (n +ℕ 0))) (inr tt) p
                   (comm⨂-EM (suc (suc (n +ℕ 0))) a⌣x))

           substPres0 : (n₁ m : ℕ) (q : n₁ ≡ m)
             → snd (EM∙ (G' ⨂ H') m)
             ≡ subst (λ n₂ → EM∙ (G' ⨂ H') n₂ .fst) q (snd (EM∙ (G' ⨂ H') n₁))
           substPres0 n = J> sym (transportRefl _)

           substPres0-refl : (n : ℕ)
             → sym (substPres0 (suc (suc n +' 1)) (suc (1 +' suc n))
                                (+'-comm (suc (suc n)) 1))
              ≡ refl
           substPres0-refl n = transportRefl _

           lem = cong-subst-lem _ _
                  (+'-comm (suc n) 1) (+'-comm (suc (suc n)) 1) (EM∙ (G' ⨂ H'))
                   EM→ΩEM+1 (λ x → EM→ΩEM+1-0ₖ _)
                   ((-ₖ^< 1 · suc (suc n) > (suc (suc (n +ℕ 0))) (inr tt) p
                        (comm⨂-EM (suc (suc (n +ℕ 0))) a⌣x)))
                   substPres0
                   λ n → transportRefl (sym (transportRefl _))

           main-lem : cong (subst (EM (G' ⨂ H')) (+'-comm (suc (suc n)) 1)) mid
                ≡ EM→ΩEM+1 (suc (suc n))
                    (subst (EM (G' ⨂ H')) (+'-comm (suc n) 1)
                      (-ₖ^< 1 · suc (suc n) > (suc (suc (n +ℕ 0))) (inr tt) p
                        (comm⨂-EM (suc (suc (n +ℕ 0))) a⌣x)))
           main-lem = lem
                ∙ cong (λ x → sym x
                  ∙∙ EM→ΩEM+1 (suc (suc n))
                    (subst (EM (G' ⨂ H')) (+'-comm (suc n) 1)
                      (-ₖ^< 1 · suc (suc n) > (suc (suc (n +ℕ 0))) (inr tt) p
                        (comm⨂-EM (suc (suc (n +ℕ 0))) a⌣x)))
                        ∙∙ x) (substPres0-refl n)
                ∙ sym (rUnit _)

-- Graded commutativity for higher dimensions
module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   cp∙∙₂ = cp∙∙ {G' = G'} {H' = H'}
   cp'∙∙₂ = cp'∙∙ {G' = G'} {H' = H'}

   ⌣ₖ-comm₂ : (n m : ℕ)
     (p : isEvenT (suc n) ⊎ isOddT (suc n))
     (q : isEvenT (suc m) ⊎ isOddT (suc m))
     → cp∙∙₂ (suc n) (suc m) ≡ cp'∙∙₂ (suc n) (suc m) p q
   ⌣ₖ-comm₂ =
     ⌣-ℕ-elim2
       (λ {n (inr tt) q → ⌣ₖ-comm₁ (suc n) q})
       (λ {n p (inr tt) →
         →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
           (funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ y
        → (((sym (Iso.leftInv (Iso→EMIso (⨂-comm {A = G'} {B = H'})
                  (suc (suc n) +' 1)) (cp∙∙₂ (suc (suc n)) 1 .fst x .fst y))
          ∙ sym (comm⨂-EM≡comm⨂-EM' {G' = G'} {H' = H'} (suc (suc n) +' 1) _)
          ∙ cong (comm⨂-EM _) (sym (-ₖ^< suc (suc n) · 1 >²-swap _ p (inr tt) _))
          ∙ -ₖ^< suc (suc n) · 1 >-Induced (suc (suc n) +' 1) p (inr tt)
              (GroupEquiv→GroupHom ⨂-comm) _)
         ∙ sym (transportRefl _)
          ∙ sym (compSubstℕ {A = EM (G' ⨂ H')} (+'-comm (suc (suc n)) 1)
                  (+'-comm 1 (suc (suc n))) refl))
          ∙ cong (subst (EM (G' ⨂ H')) (+'-comm 1 (suc (suc n))))
                 (substCommSlice (EM (H' ⨂ G')) (EM (G' ⨂ H'))
                                 (λ k x → -ₖ^< suc (suc n) · 1 > k p (inr tt)
                                             (comm⨂-EM k x))
                                 (+'-comm (suc (suc n)) 1)
                   (-ₖ^< 1 · suc (suc n) > _ (inr tt) p (comm⨂-EM _ (x ⌣ₖ y)))))
         ∙ λ i → subst (EM (G' ⨂ H')) (+'-comm 1 (suc (suc n)))
                  (-ₖ^< suc (suc n) · 1 > (1 +' suc (suc n)) p (inr tt)
                  (comm⨂-EM (1 +' suc (suc n)) (⌣ₖ-comm₁ {G' = H'} {H' = G'}
                    (suc (suc n)) p (~ i) .fst y .fst x)))))})
       λ n m ind p q → ⌣ₖ-comm-ind _ _ _ _
         λ x y → main n m (ind .fst) (ind .snd .fst) (ind .snd .snd) p q x y
                ∙ λ i → subst (EM (G' ⨂ H'))
                   (isSetℕ _ _
                     (cong (3 +ℕ_) (+-comm m (suc n) ∙ sym (+-suc n m)))
                     (+'-comm (suc (suc m)) (suc (suc n))) i)
                   (-ₖ^< (2 +ℕ n) · (2 +ℕ m) > ((2 +ℕ m) +' (2 +ℕ n)) p q
                    (comm⨂-EM ((2 +ℕ m) +' (2 +ℕ n))
                     (_⌣ₖ_ {n = suc (suc m)} {m = suc (suc n)}
                     (EM-raw'→EM H' (suc (suc m)) y)
                     (EM-raw'→EM G' (suc (suc n)) x))))
       where
       -- dimension n,m ≥ 2
       module _ (n m : ℕ)
         (indₗ : ((p₁ : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
                 (q₁ : isEvenT (suc m) ⊎ isOddT (suc m))
              → cp∙∙ (suc (suc n)) (suc m) ≡ cp'∙∙ (suc (suc n)) (suc m) p₁ q₁))
         (indᵣ : ((p₁ : isEvenT (suc n) ⊎ isOddT (suc n))
                  (q₁ : isEvenT (suc (suc m)) ⊎ isOddT (suc (suc m)))
              → cp∙∙ (suc n) (suc (suc m)) ≡ cp'∙∙ (suc n) (suc (suc m)) p₁ q₁))
         (indₘ : (p₁ : isEvenT (suc n) ⊎ isOddT (suc n))
                 (q₁ : isEvenT (suc m) ⊎ isOddT (suc m)) →
                 cp∙∙ (suc n) (suc m) ≡ cp'∙∙ (suc n) (suc m) p₁ q₁)
         where
         -- recurring path
         ℕpath = cong (2 +ℕ_) (+-comm m (suc n) ∙ sym (+-suc n m))

         -- improved coherence functions (better comp. behaviour)
         Fᵣ : (p : _) (q : _)
           → EM (H' ⨂ G') (suc (suc m) +' suc n)
           → EM (G' ⨂ H') (2 +ℕ (n +ℕ suc m))
         Fᵣ p q x =
           subst (EM (G' ⨂ H')) (cong (2 +ℕ_) (+-comm (suc m) n))
              (-ₖ^< suc n · suc (suc m) > (suc (suc m) +' (suc n)) p q
              (comm⨂-EM (suc (suc m) +' suc n)  x))

         Fₗ : (p : _) (q : _)
          → EM (G' ⨂ H') (suc (suc n) +' suc m)
          → EM (H' ⨂ G') (suc m +' suc (suc n))
         Fₗ p q x =
           Iso.inv (Iso→EMIso ⨂-comm _)
              (-ₖ^< suc (suc n) · suc m > _ p q
               (subst (EM (G' ⨂ H'))
                 (cong (2 +ℕ_) (sym (+-comm m (suc n)))) x))

         improveᵣ : (p : _) (q : _) (x : EM G' (suc n))
             (y : EM H' (suc (suc m)))
           → _⌣ₖ_ {n = suc n} {m = (suc (suc m))} x y
           ≡ Fᵣ p q (_⌣ₖ_ {n = suc (suc m)} {m = suc n} y x)
         improveᵣ p q x y =
            (λ i → indᵣ p q i .fst x .fst y)
           ∙ λ i → subst (EM (G' ⨂ H'))
             (isSetℕ _ _ (+'-comm (suc (suc m)) (suc n))
                          (cong (2 +ℕ_) (+-comm (suc m) n)) i)
              (-ₖ^< suc n · suc (suc m) > (suc (suc m) +' (suc n)) p q
              (comm⨂-EM (suc (suc m) +' suc n)
                (_⌣ₖ_ {n = suc (suc m)} {m = suc n} y x)))

         improveₗ : (p : _) (q : _) (x : EM G' (suc (suc n))) (y : EM H' (suc m))
           → _⌣ₖ_ {n = suc m} {m = suc (suc n)} y x
           ≡ Fₗ p q (_⌣ₖ_ {n = suc (suc n)} {m = (suc m)} x y)
         improveₗ p q x y =
           (sym (Iso.leftInv (Iso→EMIso ⨂-comm (suc m +' (suc (suc n)))) (y ⌣ₖ x))
           ∙ cong (Iso.inv (Iso→EMIso ⨂-comm (suc m +' (suc (suc n)))))
                  (sym (-ₖ^< suc (suc n) · suc m >² _ p q _)
                 ∙ cong (-ₖ^< suc (suc n) · suc m > _ p q)
                   (sym (transport⁻Transport
                         (λ i → EM (G' ⨂ H') (2 +ℕ (+-comm m (suc n) i))) _)
                  ∙ cong (subst (EM (G' ⨂ H'))
                           (cong (2 +ℕ_) (sym (+-comm m (suc n)))))
                    λ i → subst (EM (G' ⨂ H'))
                            (isSetℕ _ _
                             (cong (2 +ℕ_) (+-comm m (suc n)))
                             (+'-comm (suc m) (suc (suc n))) i)
                             (-ₖ^< suc (suc n) · suc m > (suc m +' suc (suc n)) p q
                             (comm⨂-EM (suc m +' suc (suc n)) (y ⌣ₖ x)))))
           ∙ cong (Fₗ p q) (λ i → indₗ p q (~ i) .fst x .fst y))

         -- alt. statement of graded-commuter
         st : (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
              (q : isEvenT (suc (suc m)) ⊎ isOddT (suc (suc m)))
           → EM (H' ⨂ G') ((2 +ℕ m) +' (2 +ℕ n))
           → EM (G' ⨂ H') ((2 +ℕ n) +' (2 +ℕ m))
         st p q x = subst (EM (G' ⨂ H')) (cong suc ℕpath)
                   (-ₖ^< (2 +ℕ n) · (2 +ℕ m) > ((2 +ℕ m) +' (2 +ℕ n)) p q
                    (comm⨂-EM ((2 +ℕ m) +' (2 +ℕ n)) x ))

         main : (p : _) (q : _)
           → (x : EM-raw' G' (suc (suc n))) (y : EM-raw' H' (suc (suc m)))
           → cp∙∙ (suc (suc n)) (suc (suc m)) .fst
                    (EM-raw'→EM G' (suc (suc n)) x) .fst
                    (EM-raw'→EM H' (suc (suc m)) y)
            ≡ st p q (_⌣ₖ_ {n = suc (suc m)} {m = suc (suc n)}
                       (EM-raw'→EM H' (suc (suc m)) y)
                       (EM-raw'→EM G' (suc (suc n)) x))
         main p q north north = refl
         main p q south north = refl
         main p q (merid a i) north k =
            (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
              (improveᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ a) ∣ north ∣)
           ∙ EM→ΩEM+1-0ₖ _) k i
         main p q north south = refl
         main p q south south = refl
         main p q (merid a i) south k =
           (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
             (improveᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ a) ∣ south ∣)
           ∙ EM→ΩEM+1-0ₖ _) k i
         main p q north (merid a i) k =
           st p q ((cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                (improveₗ p (evenOrOdd (suc m))  ∣ north ∣ (EM-raw→EM _ _ a))
                ∙ EM→ΩEM+1-0ₖ _) (~ k) i)
         main p q south (merid a i) k =
           st p q ((cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                  (improveₗ p (evenOrOdd (suc m)) ∣ south ∣ (EM-raw→EM _ _ a))
                 ∙ EM→ΩEM+1-0ₖ _) (~ k) i)
         main p q (merid b i) (merid a j) k =
           hcomp (λ r → λ {
               (i = i0) → st p q
                 (compPath-filler'
                   (cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                   (improveₗ p (evenOrOdd (suc m)) ∣ north ∣ (EM-raw→EM _ _ a)))
                   (EM→ΩEM+1-0ₖ _) r (~ k) j)
             ; (i = i1) → st p q
                  (compPath-filler'
                    (cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                    (improveₗ p (evenOrOdd (suc m)) ∣ south ∣ (EM-raw→EM _ _ a)))
                    (EM→ΩEM+1-0ₖ _) r (~ k) j)
             ; (j = i0) →
               compPath-filler'
                 (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
                 (improveᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b) ∣ north ∣))
                 (EM→ΩEM+1-0ₖ _) r k i
             ; (j = i1) →
               compPath-filler'
                 (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
                 (improveᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b) ∣ south ∣))
                 (EM→ΩEM+1-0ₖ _) r k i
             ; (k = i0) → EM→ΩEM+1 (suc (suc (n +ℕ suc m)))
                            (improveᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b)
                              ∣ merid a j ∣ (~ r)) i
             ; (k = i1) → st p q
                            (EM→ΩEM+1 _
                             (improveₗ p (evenOrOdd (suc m)) ∣ (merid b i) ∣
                               (EM-raw→EM _ _ a) (~ r)) j)})
             (hcomp (λ r → λ {
               (i = i0) → st p q ((EM→ΩEM+1-0ₖ _) (~ k ∨ ~ r) j)
             ; (i = i1) → st p q ((EM→ΩEM+1-0ₖ _) (~ k ∨ ~ r) j)
             ; (j = i0) → EM→ΩEM+1-0ₖ (suc (suc (n +ℕ suc m))) (k ∨ ~ r) i
             ; (j = i1) → EM→ΩEM+1-0ₖ (suc (suc (n +ℕ suc m))) (k ∨ ~ r) i
             ; (k = i0) → pp-wrap _ (cong (Fᵣ (evenOrOdd (suc n)) q)
                                (EM→ΩEM+1 (suc m +' suc n)
                                 (_⌣ₖ_ {n = suc m} {m = suc n}
                                  (EM-raw→EM H' (suc m) a)
                                  (EM-raw→EM G' (suc n) b)))) (~ r) j i
             ; (k = i1) → st p q (pp-wrap (suc (suc (m +ℕ suc n)))
                                   (cong (Fₗ p (evenOrOdd (suc m)))
                                (EM→ΩEM+1 (suc n +' suc m)
                                 (_⌣ₖ_ {n = suc n} {m = suc m}
                                  (EM-raw→EM G' (suc n) b)
                                  (EM-raw→EM H' (suc m) a)))) (~ r) i j)})
               (final k i j))
          where
          cong-transpLem : (x : _)
            → cong (subst (EM (G' ⨂ H'))
                    (cong (2 +ℕ_) (sym (+-comm m (suc n)))))
                (EM→ΩEM+1 (suc n +' suc m) x)
              ≡ EM→ΩEM+1 (suc (m +ℕ suc n))
                 (subst (EM (G' ⨂ H'))
                   (cong suc (sym (+-comm m (suc n)))) x)
          cong-transpLem x j i =
            transp (λ i → EM (G' ⨂ H')
                              (2 +ℕ (+-comm m (suc n) (~ i ∧ ~ j)))) j
              (EM→ΩEM+1 (suc (+-comm m (suc n) (~ j)))
                (transp (λ i → EM (G' ⨂ H')
                               (suc (+-comm m (suc n) (~ i ∨ ~ j)))) (~ j) x) i)

          expr₁ =
            cong (Fₗ p (evenOrOdd (suc m)))
              (EM→ΩEM+1 (suc n +' suc m)
               (_⌣ₖ_ {n = suc n} {m = suc m}
                (EM-raw→EM G' (suc n) b)
                (EM-raw→EM H' (suc m) a)))

          ↑expr₁ = transport (λ i → fst (Ω (EM∙ (H' ⨂ G') (ℕpath i)))) expr₁

          expr₂ : EM (H' ⨂ G') (suc (m +ℕ suc n))
          expr₂  =
            subst (EM (H' ⨂ G')) (cong suc (sym (+-suc m n)))
              (-ₖ^< suc (suc n) · suc m > (suc m +' suc n) p (evenOrOdd (suc m))
                (-ₖ^< suc n · suc m > (suc m +' suc n)
                    (evenOrOdd (suc n)) (evenOrOdd (suc m))
                  (_⌣ₖ_ {n = suc m} {m = suc n}
                     (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b))))

          expr₃ =
            Iso.inv (Iso→EMIso ⨂-comm _)
              (-ₖ^< suc (suc n) · suc m > (suc (m +ℕ suc n)) p (evenOrOdd (suc m))
              (subst (EM (G' ⨂ H')) (cong suc (sym (+-comm m (suc n))))
                (_⌣ₖ_ {n = suc n} {m = suc m}
                  (EM-raw→EM G' (suc n) b)
                  (EM-raw→EM H' (suc m) a))))

          expr₃≡expr₂ : expr₃ ≡ expr₂
          expr₃≡expr₂ =
              cong (Iso.inv (Iso→EMIso ⨂-comm _))
                   (cong (-ₖ^< suc (suc n) · suc m >
                           (suc (m +ℕ suc n)) p (evenOrOdd (suc m)))
                    (cong (subst (EM (G' ⨂ H'))
                          (cong suc (sym (+-comm m (suc n)))))
                        (λ i → indₘ (evenOrOdd (suc n))
                                     (evenOrOdd (suc m)) i .fst
                                     (EM-raw→EM G' (suc n) b) .fst
                                     (EM-raw→EM H' (suc m) a)
                                    )
                 ∙ compSubstℕ (+'-comm (suc m) (suc n))
                               (sym (cong suc (+-comm m (suc n))))
                               (cong suc (sym (+-suc m n)))
                  ∙ cong (subst (EM (G' ⨂ H')) (cong suc (sym (+-suc m n))))
                         (sym (-ₖ^< suc n · suc m >-Induced (suc m +' suc n)
                             (evenOrOdd (suc n)) (evenOrOdd (suc m))
                             (GroupEquiv→GroupHom ⨂-comm)
                             (_⌣ₖ_ {n = suc m} {m = suc n}
                             (EM-raw→EM H' (suc m) a)
                             (EM-raw→EM G' (suc n) b))))))
            ∙ sym (substCommSlice (EM (G' ⨂ H')) (EM (H' ⨂ G'))
                (λ k x → Iso.inv (Iso→EMIso ⨂-comm k)
                           (-ₖ^< suc (suc n) · suc m > k p
                            (evenOrOdd (suc m)) x))
                (cong suc (sym (+-suc m n))) _)
            ∙ cong (subst (EM (H' ⨂ G')) (cong suc (sym (+-suc m n))))
                   (cong (Iso.inv (Iso→EMIso ⨂-comm _))
                    (sym (-ₖ^< suc (suc n) · suc m >-Induced (suc (suc (m +ℕ n)))
                          p (evenOrOdd (suc m)) (GroupEquiv→GroupHom ⨂-comm) _))
                 ∙ Iso.leftInv (Iso→EMIso ⨂-comm (suc (suc (m +ℕ n)))) _)

          cong-Fₗ-expr₁ : expr₁ ≡ EM→ΩEM+1 (suc (m +ℕ suc n)) expr₂
          cong-Fₗ-expr₁ = cong (cong (Iso.inv (Iso→EMIso ⨂-comm _) ∘
                            (-ₖ^< suc (suc n) · suc m > _ p (evenOrOdd (suc m)))))
                          (cong-transpLem (_⌣ₖ_ {n = suc n} {m = suc m}
                             (EM-raw→EM G' (suc n) b)
                             (EM-raw→EM H' (suc m) a)))
                   ∙ cong (cong (Iso.inv (Iso→EMIso ⨂-comm _)))
                          (cong-ₖ^< suc (suc n) · suc m >₂ _
                            p (evenOrOdd (suc m)) _)
                   ∙ sym (EMFun-EM→ΩEM+1 _ _)
                   ∙ cong (EM→ΩEM+1 (suc (m +ℕ suc n))) expr₃≡expr₂

          lem₁ :
              cong (-ₖ^< 2 +ℕ n · 2 +ℕ m > (suc (suc (n +ℕ suc m))) p q)
              (λ i₁ → comm⨂-EM (suc (suc (n +ℕ suc m))) (↑expr₁ (~ i₁)))
             ≡ transport (λ i → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i))))
                 (cong (-ₖ^< 2 +ℕ n · 2 +ℕ m > (suc (suc (m +ℕ suc n))) p q)
                   (cong (comm⨂-EM (suc (suc (m +ℕ suc n))))
                    (EM→ΩEM+1 (suc (m +ℕ suc n))
                      (-ₖ expr₂))))
          lem₁ = (λ i → transp
            (λ j → fst (Ω (EM∙ (G' ⨂ H') (ℕpath (~ i ∨ j))))) (~ i)
             (cong (-ₖ^< 2 +ℕ n · 2 +ℕ m > (ℕpath (~ i)) p q)
               (cong (comm⨂-EM (ℕpath (~ i)))
                (transp (λ j → fst (Ω (EM∙ (H' ⨂ G') (ℕpath (~ i ∧ j))))) i
                  (sym expr₁)))))
            ∙ cong (transport (λ i → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i))))
                   ∘ (cong (-ₖ^< 2 +ℕ n · 2 +ℕ m > (suc (suc (m +ℕ suc n))) p q)
                   ∘ (cong (comm⨂-EM (suc (suc (m +ℕ suc n)))))))
                   (cong sym cong-Fₗ-expr₁
                   ∙ sym (EM→ΩEM+1-sym (suc (m +ℕ suc n)) expr₂))


          substLem : {n : ℕ} (m : ℕ) (p : n ≡ m) (x : typ (Ω (EM∙ (G' ⨂ H') _)))
            → subst (λ n → typ (Ω (EM∙ (G' ⨂ H') n))) (cong (suc ∘ suc) p) x
            ≡ cong (subst (EM (G' ⨂ H')) (cong (suc ∘ suc) p)) x
          substLem =
            J> λ x → transportRefl x ∙ λ j i → transportRefl (x i) (~ j)

          final : flipSquare
                    (wrap (suc (suc (n +ℕ suc m)))
                      (cong (Fᵣ (evenOrOdd (suc n)) q)
                                 (EM→ΩEM+1 (suc m +' suc n)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))))
                ≡ cong (cong (st p q))
                       (wrap (suc m +' suc (suc n)) expr₁)
          final =
              sym (sym≡flipSquare _)
            ∙ cong (sym ∘ wrap (suc (suc (n +ℕ suc m))))
                   ((λ _ → (cong (Fᵣ (evenOrOdd (suc n)) q)
                             (EM→ΩEM+1 (suc m +' suc n)
                              (_⌣ₖ_ {n = suc m} {m = suc n}
                               (EM-raw→EM H' (suc m) a)
                               (EM-raw→EM G' (suc n) b)))))
                  ∙ (sym (substLem _ (+-comm (suc m) n) (cong
                   (-ₖ^< suc n · suc (suc m) > (suc (suc m) +' (suc n))
                        (evenOrOdd (suc n)) q
                     ∘ (comm⨂-EM (suc (suc m) +' suc n)))
                   (EM→ΩEM+1 (suc m +' suc n)
                              (_⌣ₖ_ {n = suc m} {m = suc n}
                               (EM-raw→EM H' (suc m) a)
                               (EM-raw→EM G' (suc n) b)))))
                 ∙ cong (subst (λ n → typ (Ω (EM∙ (G' ⨂ H') n)))
                               (cong (suc ∘ suc) (+-comm (suc m) n)))
                        (cong (cong (-ₖ^< suc n · suc (suc m) >
                                      (suc (suc m) +' suc n)
                              (evenOrOdd (suc n)) q))
                              (sym (EMFun-EM→ΩEM+1 _
                                 (_⌣ₖ_ {n = suc m} {m = suc n}
                                 (EM-raw→EM H' (suc m) a)
                                 (EM-raw→EM G' (suc n) b))))
                       ∙ cong-ₖ^< suc n · suc (suc m) >₂ _ (evenOrOdd (suc n)) q
                           (comm⨂-EM _ (_⌣ₖ_ {n = suc m} {m = suc n}
                                 (EM-raw→EM H' (suc m) a)
                                 (EM-raw→EM G' (suc n) b)))
                       ∙ cong (EM→ΩEM+1 (suc (suc (m +ℕ n))))
                              (sym (-ₖ^< suc n · suc (suc m) >-Induced
                                  (suc m +' suc n)
                                  (evenOrOdd (suc n)) q
                                  (GroupEquiv→GroupHom ⨂-comm)
                                  ((_⌣ₖ_ {n = suc m} {m = suc n}
                                 (EM-raw→EM H' (suc m) a)
                                 (EM-raw→EM G' (suc n) b))))
                             ∙ cong (comm⨂-EM (suc m +' suc n))
                               (⌣ₖ-comm-final-lem (suc n) (suc m)
                                 (suc m +' suc n) p q
                                 (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                 (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))
                             ∙ -ₖ^< suc (suc n) · suc (suc m) >-Induced
                                 (suc (suc (m +ℕ n))) p q
                                 (GroupEquiv→GroupHom ⨂-comm) _)))
                  ∙ sym (compSubstℕ {A = λ n → typ (Ω (EM∙ (G' ⨂ H') n))}
                         (cong (suc ∘ suc) (sym (+-suc m n))) ℕpath
                        (cong (suc ∘ suc) (+-comm (suc m) n)))
                  ∙ cong (transport (λ i₁ → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i₁)))))
                         ((substCommSlice (EM (H' ⨂ G'))
                           (λ n → typ (Ω (EM∙ (G' ⨂ H') (suc n))))
                           (λ k x → EM→ΩEM+1 k (-ₖ^< 2 +ℕ n · 2 +ℕ m >
                                                 k p q (comm⨂-EM k (-ₖ x))))
                           (cong suc (sym (+-suc m n)))
                           ((-ₖ^< suc (suc n) · suc m > (suc m +' suc n) p
                                (evenOrOdd (suc m))
                            (-ₖ^< suc n · suc m > (suc m +' suc n)
                                (evenOrOdd (suc n)) (evenOrOdd (suc m))
                              ((_⌣ₖ_ {n = suc m} {m = suc n}
                             (EM-raw→EM H' (suc m) a)
                             (EM-raw→EM G' (suc n) b)))))))
                        ∙ sym (cong-ₖ^< 2 +ℕ n · 2 +ℕ m >₂ (m +ℕ suc n) p q _)
                        ∙ cong (cong (-ₖ^< 2 +ℕ n · 2 +ℕ m >
                                     (suc (suc (m +ℕ suc n))) p q))
                            (EMFun-EM→ΩEM+1 _ _))
                  ∙ sym lem₁)
            ∙ cong sym (sym (cong-cong-ₖ^< (2 +ℕ n) · (2 +ℕ m) >₂
                    (n +ℕ suc m) p q
                    (cong (comm⨂-EM (suc (suc (n +ℕ suc m))))
                      (sym ↑expr₁))))
            ∙∙ cong (cong (cong (-ₖ^< (2 +ℕ n) · (2 +ℕ m) >
                          (suc (ℕpath i1)) p q)))
                    (sym (cong-cong-comm⨂-EM _ ↑expr₁))
            ∙∙ λ k i j
             → transp (λ j
               → EM (G' ⨂ H') (suc (ℕpath (j ∨ ~ k))))
                 (~ k)
                 (-ₖ^< (2 +ℕ n) · (2 +ℕ m) >
                   (suc (ℕpath (~ k))) p q
                  (comm⨂-EM (suc (ℕpath (~ k)))
                    (wrap (ℕpath (~ k))
                      (transp (λ i → fst (Ω (EM∙ (H' ⨂ G')
                                       (ℕpath (~ k ∧ i))))) k
                       expr₁) i j)))

-- better definition -ₖⁿ*ᵐ
module _ {G : AbGroup ℓ} where
  -ₖ^[_·_] : (n m : ℕ) {k : ℕ} (x : EM G k) → EM G k
  -ₖ^[ n · m ] {k = k} = -ₖ^< n · m > k (evenOrOdd n) (evenOrOdd m)

  -ₖ^[_·_]-even : (n m : ℕ) → isEvenT n ⊎ isEvenT m
    → {k : ℕ} (x : EM G k) → -ₖ^[ n · m ] x ≡ x
  -ₖ^[_·_]-even n m (inl p) {k = k} x =
     (λ i → -ₖ^< n · m > k
       (isPropEvenOrOdd n (evenOrOdd n) (inl p) i)
       (evenOrOdd m) x)
    ∙ -ₖ^< n · m >-inl-left k p (evenOrOdd m) x
  -ₖ^[_·_]-even n m (inr p) {k = k} x =
    (λ i → -ₖ^< n · m > k
        (evenOrOdd n)
        (isPropEvenOrOdd m (evenOrOdd m) (inl p) i) x)
    ∙ -ₖ^< n · m >-inl-right k (evenOrOdd n) p x

  -ₖ^[_·_]-odd : (n m : ℕ) → isOddT n × isOddT m
    → {k : ℕ} (x : EM G k) → -ₖ^[ n · m ] x ≡ -ₖ x
  -ₖ^[_·_]-odd n m (p , q) {k = k} x =
      cong₂ (λ p q → -ₖ^< n · m > k p q x)
        (isPropEvenOrOdd n _ _) (isPropEvenOrOdd m _ _)
    ∙ -ₖ^< n · m >-inr k p q x

module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
  ⌣ₖ-comm : (n m : ℕ) (x : EM G' n) (y : EM H' m)
    → x ⌣ₖ y ≡ subst (EM (G' ⨂ H')) (+'-comm m n)
                 (-ₖ^[ n · m ] (comm⨂-EM (m +' n) (y ⌣ₖ x)))
  ⌣ₖ-comm zero zero x y =
    sym (transportRefl
         (comm⨂-EM zero (_⌣ₖ_ {n = zero} {m = zero} y x)))
  ⌣ₖ-comm zero (suc m) x y =
       ⌣ₖ-comm₀ m x y
     ∙ sym ((λ i → subst (EM (G' ⨂ H'))
           (isSetℕ _ _ (+'-comm (suc m) zero) refl i)
           ((-ₖ^< zero · suc m > (suc m) (inl tt) (evenOrOdd (suc m))
             (comm⨂-EM (suc m) (_⌣ₖ_ {m = zero} y x)))))
         ∙ transportRefl _
         ∙ -ₖ^< zero · suc m >-inl-left (suc m) tt
             (evenOrOdd (suc m))
             (comm⨂-EM (suc m) (_⌣ₖ_ {m = zero} y x)))
  ⌣ₖ-comm (suc n) zero x y =
         sym (Iso.leftInv (Iso→EMIso ⨂-comm _)
              (_⌣ₖ_ {n = suc n} {m = zero} x y))
       ∙ sym (comm⨂-EM≡comm⨂-EM' (suc n) _)
       ∙ cong (comm⨂-EM (suc n)) (sym (⌣ₖ-comm₀ n y x))
      ∙ sym (-ₖ^< suc n · zero >-inl-right (suc n) (evenOrOdd (suc n)) tt
            (comm⨂-EM (suc n) (_⌣ₖ_ {n = zero} {m = suc n} y x)))
     ∙ sym (transportRefl _)
     ∙ λ i → subst (EM (G' ⨂ H')) (isSetℕ _ _ refl (+'-comm zero (suc n)) i)
      (-ₖ^< suc n · zero > (suc n) (evenOrOdd (suc n)) (inl tt)
       (comm⨂-EM (suc n) (_⌣ₖ_ {n = zero} {m = suc n} y x)))
  ⌣ₖ-comm (suc n) (suc m) x y i =
    ⌣ₖ-comm₂ n m (evenOrOdd (suc n)) (evenOrOdd (suc m)) i .fst x .fst y
