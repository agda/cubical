{-# OPTIONS --safe --experimental-lossy-unification #-}

{- This file contains properties of K(G,n) for G of order 2
(in particular of ℤ/2) -}

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
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; elim to ℕelim)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.EilenbergMacLane1 as EM₁
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Sum
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group.MorphismProperties

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open PlusBis

ℕ-elim2 : ∀ {ℓ} {A : ℕ → ℕ → Type ℓ}
  → ((n : ℕ) → A zero n)
  → ((n : ℕ) → A (suc n) zero)
  → ((n m : ℕ) → A (suc n) m × A n (suc m) × A n m → A (suc n) (suc m))
  → (n m : ℕ) → A n m
ℕ-elim2 l r ind zero m = l m
ℕ-elim2 l r ind (suc n) zero = r n
ℕ-elim2 {A = A} l r ind (suc n) (suc m) =
  ind n m ((ℕ-elim2 {A = A} l r ind (suc n) m)
          , ℕ-elim2 {A = A} l r ind n (suc m)
          , ℕ-elim2 {A = A} l r ind n m)

substℕ-lem : ∀ {ℓ} {A : ℕ → Type ℓ} (n m : ℕ)
  (p : n ≡ m) (l : ℕ) (q : m ≡ l) (r : n ≡ l)
   → {x : _}
   → subst A q (subst A p x)
   ≡ subst A r x
substℕ-lem {A = A}n =
  J> (J> λ r {x} → transportRefl (transport refl x)
   ∙ λ i → subst A(isSetℕ _ _ refl r i) x)


cong-subst' : ∀ {ℓ} (n m : ℕ) (q' : n ≡ m) (q : suc n ≡ suc m)
      (A : ℕ → Pointed ℓ)
      (F : (x : ℕ) → fst (A x) → fst (Ω (A (suc x))))
      (F∙ : (x : ℕ) → F x (pt (A x)) ≡ refl)
   → (x : fst (A n))
   → (s : (n m : ℕ) (q : n ≡ m)
     → snd (A m) ≡ subst (λ n₁ → A n₁ .fst) q (snd (A n)))
   → ((n : ℕ) → s n n refl ≡ sym (transportRefl _))
   → (cong (subst (λ n → A n .fst) q) (F n x))
   ≡ (sym (s _ _ q) ∙∙ F m (subst (λ n → A n .fst) q' x) ∙∙ s _ _ q)
cong-subst' {ℓ} n = J> λ q → lem2 q (isSetℕ _ _ refl q)
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

variable
  ℓ ℓ' : Level

module _ {G' : AbGroup ℓ} where
   private
     G = fst G'

     strG = snd G'

     0G = 0g strG

     _+G_ = _+Gr_ strG

     -G_ = -Gr_ strG

   id' : (n : ℕ) → EM G' n → EM G' n
   id' zero x = x
   id' (suc zero) x = x
   id' (suc (suc n)) =
     TR.rec (isOfHLevelTrunc (4 +ℕ n))
       λ { north → 0ₖ (2 +ℕ n)
         ; south → 0ₖ (2 +ℕ n)
         ; (merid a i) → EM→ΩEM+1 _ (EM-raw→EM G' (suc n) a) i}

   id'≡id : (n : ℕ) (x : EM G' n) → id' n x ≡ x
   id'≡id zero x = refl
   id'≡id (suc zero) x = refl
   id'≡id (suc (suc n)) =
     TR.elim
       (λ _ → isOfHLevelPath (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) j → lem a j i}
     where
     lem : (a : _) → PathP (λ i → Path (EM G' (suc (suc n))) ∣ north ∣ ∣ merid ptEM-raw i ∣)
                            (EM→ΩEM+1 (suc n) (EM-raw→EM G' (suc n) a))
                            (cong ∣_∣ₕ (merid a))
     lem a = EM→ΩEM+1∘EM-raw→EM n a
           ◁ λ i j → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ i) j ∣ₕ

   -ₖ^[_·_] : (n m k : ℕ)
     → isEvenT n ⊎ isOddT n
     → isEvenT m ⊎ isOddT m
     → EM G' k → EM G' k
   -ₖ^[ n · m ] zero (inl x) q r = r
   -ₖ^[ n · m ] zero (inr x) (inl x₁) r = r
   -ₖ^[ n · m ] zero (inr x) (inr x₁) r = -ₖ r
   -ₖ^[ n · m ] (suc zero) p q =
     EM₁.rec  (AbGroup→Group G')
       (hLevelEM _ 1)
       embase
       (eml p q)
       (ts2 p q)
     where
     eml : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
       (g : fst G') → Path (EM G' 1) embase embase
     eml (inl x) q g = emloop g
     eml (inr x) (inl x₁) g = emloop g
     eml (inr x) (inr x₁) g = sym (emloop g)

     ts2 : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m) (g h : fst G')
       → Square (eml p q g) (eml p q (g +G h)) refl (eml p q h)
     ts2 (inl x) q g h = emcomp g h
     ts2 (inr x) (inl x₁) g h = emcomp g h
     ts2 (inr x) (inr x₁) g h =
         sym (emloop-sym _ g)
       ◁ (flipSquare (flipSquare (emcomp (-G g) (-G h))
        ▷ emloop-sym _ h)
       ▷ (cong emloop (+Comm (snd G') (-G g) (-G h)
               ∙ sym (GroupTheory.invDistr (AbGroup→Group G') g h))
       ∙ emloop-sym _ (g +G h)))
   -ₖ^[ n · m ] (suc (suc k)) p q =
     TR.rec (isOfHLevelTrunc (4 +ℕ k))
       λ { north → 0ₖ _
         ; south → 0ₖ _
         ; (merid a i) → help p q a i}
       where
       help : (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
              (a : EM-raw G' (suc k))
           → Path (EM G' (suc (suc k))) (0ₖ (suc (suc k))) (0ₖ (suc (suc k)))
       help (inl x) q a = EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a)
       help (inr x) (inl x₁) a = EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a)
       help (inr x) (inr x₁) a = sym (EM→ΩEM+1 _ (EM-raw→EM G' (suc k) a))

   -ₖ^[_·_]∙ : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
     → -ₖ^[ n · m ] k p q (0ₖ k) ≡ 0ₖ k
   -ₖ^[ n · m ]∙ zero (inl x) q = refl
   -ₖ^[ n · m ]∙ zero (inr x) (inl x₁) = refl
   -ₖ^[ n · m ]∙ zero (inr x) (inr x₁) = GroupTheory.inv1g (AbGroup→Group G')
   -ₖ^[ n · m ]∙ (suc zero) p q = refl
   -ₖ^[ n · m ]∙ (suc (suc k)) p q = refl

   lem : (k : _) (a : _)
     → PathP (λ i → EM→ΩEM+1 (suc k) (EM-raw→EM G' (suc k) a) i ≡ ∣ merid a i ∣)
              refl
              (cong ∣_∣ₕ (merid ptEM-raw))
   lem k a = flipSquare (EM→ΩEM+1∘EM-raw→EM k a
         ◁ λ i j → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ i) j ∣ₕ)


   -ₖ^[_·_]-inl-left : (n m k : ℕ)
      (p : _)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k (inl p) q x ≡ x
   -ₖ^[ n · m ]-inl-left zero p q x = refl
   -ₖ^[ n · m ]-inl-left (suc zero) p q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl} 
   -ₖ^[ n · m ]-inl-left (suc (suc k)) p q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → lem k a i}

   -ₖ^[_·_]-inl-right : (n m k : ℕ)
      (p : _)
      (q : isEvenT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k p (inl q) x ≡ x
   -ₖ^[ n · m ]-inl-right zero (inl p) q x = refl
   -ₖ^[ n · m ]-inl-right (suc zero) (inl p) q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ^[ n · m ]-inl-right (suc (suc k)) (inl p) q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → lem k a i}
   -ₖ^[ n · m ]-inl-right zero (inr x) q _ = refl
   -ₖ^[ n · m ]-inl-right (suc zero) (inr x) q =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ^[ n · m ]-inl-right (suc (suc k)) (inr x) q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → lem k a i}


   -ₖ^[_·_]-inr : (n m k : ℕ)
      (p : _)
      (q : isOddT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k (inr p) (inr q) x ≡ -ₖ x
   -ₖ^[ n · m ]-inr zero p q x = refl
   -ₖ^[ n · m ]-inr (suc zero) p q x = refl
   -ₖ^[ n · m ]-inr (suc (suc k)) p q =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl ; south → refl ; (merid a i) j → l2 k a j i}
       where
       l2 : (k : ℕ) (a : EM-raw G' (suc k))
         → cong (-ₖ^[ n · m ] (suc (suc k)) (inr p) (inr q)) (cong ∣_∣ₕ (merid a))
          ≡ cong -ₖ_ (cong ∣_∣ₕ (merid a)) 
       l2 zero a = refl
       l2 (suc k) a = refl

   cong-ₖ^[_·_]₂ : (n m k : ℕ)
       (p : isEvenT n ⊎ isOddT n)
       (q : isEvenT m ⊎ isOddT m)
      → (x : EM G' (suc k))
      → cong (-ₖ^[ n · m ] (suc (suc k)) p q) (EM→ΩEM+1 (suc k) x)
      ≡ EM→ΩEM+1 (suc k) (-ₖ^[ n · m ] (suc k) p q x)
   cong-ₖ^[ n · m ]₂ k (inl p) q x =
     (λ i j → -ₖ^[ n · m ]-inl-left (suc (suc k)) p q (EM→ΩEM+1 (suc k) x j) i)
     ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^[ n · m ]-inl-left (suc k) p q x))
   cong-ₖ^[ n · m ]₂ k (inr p) (inl q) x =
     (λ i j → -ₖ^[ n · m ]-inl-right (suc (suc k)) (inr p) q (EM→ΩEM+1 (suc k) x j) i)
     ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^[ n · m ]-inl-right (suc k) (inr p) q x))
   cong-ₖ^[ n · m ]₂ k (inr p) (inr q) x =
     (λ i j → -ₖ^[ n · m ]-inr (suc (suc k)) p q
                (EM→ΩEM+1 (suc k) x j) i)
           ∙∙ cong-₂ k (EM→ΩEM+1 (suc k) x)
           ∙∙ sym (EM→ΩEM+1-sym (suc k) x)
            ∙ cong (EM→ΩEM+1 (suc k)) (sym (-ₖ^[ n · m ]-inr (suc k) p q x))

   -ₖ² : (k : ℕ) (x : EM G' k) → (-ₖ (-ₖ x)) ≡ x
   -ₖ² zero x = GroupTheory.invInv (AbGroup→Group G') x
   -ₖ² (suc zero) = EM-raw'-elim _ _ (λ _ → hLevelEM _ 1 _ _)
     λ { embase-raw → refl ; (emloop-raw g i) → refl}
   -ₖ² (suc (suc k)) =
     TR.elim (λ _ → isOfHLevelPath (4 +ℕ k) (isOfHLevelTrunc (4 +ℕ k)) _ _)
       λ { north → refl
         ; south → cong ∣_∣ₕ (merid ptEM-raw)
         ; (merid a i) → help a i}
       where
       help : (a : _) → PathP (λ i → Path (EM G' (suc (suc k))) (-ₖ (-ₖ ∣ merid a i ∣ₕ)) ∣ merid a i ∣ₕ)
                               refl
                               (cong ∣_∣ₕ (merid ptEM-raw))
       help a = flipSquare ((cong (cong (-ₖ_ {n = suc (suc k)}))
                             (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid ptEM-raw)))
                           ∙ cong-∙ ∣_∣ₕ (merid (ptEM-raw)) (sym (merid a)))
                           ∙ cong-∙ (-ₖ_ {n = suc (suc k)})
                              (cong ∣_∣ₕ (merid ptEM-raw)) (sym (cong ∣_∣ₕ (merid a)))
                           ∙ cong (_∙ cong (-ₖ_ {n = suc (suc k)})
                                        (sym (cong ∣_∣ₕ (merid a))))
                                  (λ i j → ∣ rCancel (merid ptEM-raw) i (~ j) ∣ₕ)
                           ∙ sym (lUnit _))
                           ◁ λ i j → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ i) j ∣ₕ)

   -ₖ^[_·_]² : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k p q (-ₖ^[ n · m ] k p q x) ≡ x
   -ₖ^[ n · m ]² k (inl x₁) q x = -ₖ^[ n · m ]-inl-left k x₁ q _ ∙ -ₖ^[ n · m ]-inl-left k x₁ q x
   -ₖ^[ n · m ]² k (inr x₁) (inl x₂) x =
     -ₖ^[ n · m ]-inl-right k (inr x₁) x₂ _ ∙ -ₖ^[ n · m ]-inl-right k (inr x₁) x₂ x
   -ₖ^[ n · m ]² k (inr x₁) (inr x₂) x =
       -ₖ^[ n · m ]-inr k x₁ x₂ _
     ∙ cong -ₖ_ (-ₖ^[ n · m ]-inr k x₁ x₂ x)
     ∙ -ₖ² k x

   -ₖ^[_·_]²-swap : (n m k : ℕ)
      (p : isEvenT n ⊎ isOddT n)
      (q : isEvenT m ⊎ isOddT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k p q (-ₖ^[ m · n ] k q p x) ≡ x
   -ₖ^[ n · m ]²-swap k (inl p) q x =
     -ₖ^[ n · m ]-inl-left k p q _ ∙ -ₖ^[ m · n ]-inl-right k q p x
   -ₖ^[ n · m ]²-swap k (inr p) (inl q) x =
     -ₖ^[ n · m ]-inl-right k (inr p) q _ ∙ -ₖ^[ m · n ]-inl-left k q (inr p) x
   -ₖ^[ n · m ]²-swap k (inr p) (inr q) x =
       -ₖ^[ n · m ]-inr k p q _
     ∙ cong -ₖ_ (-ₖ^[ m · n ]-inr k q p _)
     ∙ -ₖ² k x

   wrap : (n : ℕ) (p : Path (EM G' n) (0ₖ n) (0ₖ n))
     → typ ((Ω^ 2) (EM∙ G' (suc n)))
   wrap n p = sym (EM→ΩEM+1-0ₖ n) ∙∙ cong (EM→ΩEM+1 n) p ∙∙ EM→ΩEM+1-0ₖ n

   wrapEq : (n : ℕ) (p q : EM→ΩEM+1 {G = G'} n (0ₖ n) ≡ EM→ΩEM+1 n (0ₖ n))
     → p ≡ q → sym (EM→ΩEM+1-0ₖ n) ∙∙ p ∙∙ EM→ΩEM+1-0ₖ n
               ≡ (sym (EM→ΩEM+1-0ₖ n) ∙∙ q ∙∙ EM→ΩEM+1-0ₖ n)
   wrapEq n p q r = cong (sym (EM→ΩEM+1-0ₖ n) ∙∙_∙∙ EM→ΩEM+1-0ₖ n) r

   pp-wrap : (n : ℕ) (p : Path (EM G' n) (0ₖ n) (0ₖ n))
           → PathP (λ i → EM→ΩEM+1-0ₖ n i ≡ EM→ΩEM+1-0ₖ n i) (cong (EM→ΩEM+1 n) p) (wrap n p)
   pp-wrap n p =
     doubleCompPath-filler
       (sym (EM→ΩEM+1-0ₖ n)) (cong (EM→ΩEM+1 n) p) (EM→ΩEM+1-0ₖ n)

   cong-cong-ₖ^[_·_]₂ : (n m k : ℕ)
       (p : isEvenT n ⊎ isOddT n)
       (q : isEvenT m ⊎ isOddT m)
      → (x : Path (EM G' (2 +ℕ k)) (0ₖ (2 +ℕ k)) (0ₖ (2 +ℕ k)))
      → cong (cong (-ₖ^[ n · m ] (suc (suc (suc k))) p q)) (wrap (suc (suc k)) x)
      ≡ wrap (suc (suc k)) (cong (-ₖ^[ n · m ] (suc (suc k)) p q) x)
   cong-cong-ₖ^[ n · m ]₂ k (inl p) q x =
       (λ r i j → -ₖ^[ n · m ]-inl-left (suc (suc (suc k))) p q
                     (wrap (suc (suc k)) x i j) r)
     ∙ cong (wrap (suc (suc k)))
       λ r i → -ₖ^[ n · m ]-inl-left (suc (suc k)) p q (x i) (~ r)
   cong-cong-ₖ^[ n · m ]₂ k (inr p) (inl q) x =
     (λ r i j → -ₖ^[ n · m ]-inl-right (suc (suc (suc k))) (inr p) q
                     (wrap (suc (suc k)) x i j) r)
     ∙ cong (wrap (suc (suc k)))
       λ r i → -ₖ^[ n · m ]-inl-right (suc (suc k)) (inr p) q (x i) (~ r)
   cong-cong-ₖ^[ n · m ]₂ k (inr p) (inr q) x =
       (λ r i j → -ₖ^[ n · m ]-inr (suc (suc (suc k))) p q (wrap (suc (suc k)) x i j) r)
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
            (sym ((λ r i → -ₖ^[ n · m ]-inr (suc (suc k)) p q (x i) r)
                ∙ cong-₂ k x))

   -Lem : (n m k : ℕ)
          (p : _) (q : _) (p' : _) (q' : _)
          (x : EM G' k)
       → -ₖ^[ n · suc m ] k p' q x
       ≡ -ₖ^[ suc n · suc m ] k p q
         (-ₖ -ₖ^[ suc n · m ] k p q'
           (-ₖ^[ n · m ] k p' q' x))
   -Lem n m k (inl p) q (inl p') q' x = 
     ⊥.rec (¬evenAndOdd n (p' , p))
   -Lem n m k (inl p) (inl q) (inr p') (inl q') x =
     ⊥.rec (¬evenAndOdd m (q' , q))
   -Lem n m k (inl p) (inl q) (inr p') (inr q') x =
       -ₖ^[ n · suc m ]-inl-right k (inr p') q x
     ∙ sym (-ₖ^[ suc n · suc m ]-inl-left k p (inl q) _
           ∙ cong -ₖ_ (-ₖ^[ suc n · m ]-inl-left k p (inr q') _
                     ∙ -ₖ^[ n · m ]-inr k p' q' x)
           ∙ -ₖ² k x)
   -Lem n m k (inl p) (inr q) (inr p') (inl q') x =
       -ₖ^[ n · suc m ]-inr k p' q x
     ∙ cong -ₖ_ (sym (-ₖ^[ suc n · m ]-inl-left k p (inl q') _
              ∙ -ₖ^[ n · m ]-inl-right k (inr p') q' x))
     ∙ sym (-ₖ^[ suc n · suc m ]-inl-left k p (inr q) _)
   -Lem n m k (inl p) (inr q) (inr p') (inr q') x =
     ⊥.rec (¬evenAndOdd m (q , q'))
   -Lem n m k (inr p) (inl q) (inl p') (inl q') x =
     ⊥.rec (¬evenAndOdd (suc m) (q , q'))
   -Lem n m k (inr p) (inl q) (inl p') (inr q') x =
     -ₖ^[ n · suc m ]-inl-left k p' (inl q) x
     ∙ sym (-ₖ^[ suc n · suc m ]-inl-right k (inr p) q _
          ∙ cong -ₖ_
             (-ₖ^[ suc n · m ]-inr k p q' _
             ∙ cong -ₖ_ (-ₖ^[ n · m ]-inl-left k p' (inr q') x))
          ∙ -ₖ² k x)
   -Lem n m k (inr p) (inr q) (inl p') (inl q') x =
       -ₖ^[ n · suc m ]-inl-left k p' (inr q) x
     ∙ sym (-ₖ^[ suc n · suc m ]-inr k p q _
          ∙ -ₖ² k _
          ∙ -ₖ^[ suc n · m ]-inl-right k (inr p) q' _
          ∙ -ₖ^[ n · m ]-inl-left k p' (inl q') x)
   -Lem n m k (inr p) (inr q) (inl p') (inr q') x =
     ⊥.rec (¬evenAndOdd m (q , q'))
   -Lem n m k (inr p) q (inr p') q' x =
     ⊥.rec (¬evenAndOdd (suc n) (p' , p))

module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   private
     G = fst G'
     H = fst H'

     strG = snd G'
     strH = snd H'

     0G = 0g strG
     0H = 0g strH

     _+G_ = _+Gr_ strG
     _+H_ = _+Gr_ strH

     -H_ = -Gr_ strH
     -G_ = -Gr_ strG
     open PlusBis


   trFun : (n m : ℕ) → EM (G' ⨂ H') (n +' m) → EM (H' ⨂ G') (m +' n)
   trFun n m x =
     subst (EM (H' ⨂ G'))
       (+'-comm n m)
       (Iso.fun (Iso→EMIso ⨂-comm (n +' m)) x )

   trFun∙ : (n m : ℕ) → EM∙ (G' ⨂ H') (n +' m) →∙ EM∙ (H' ⨂ G') (m +' n)
   fst (trFun∙ n m) = trFun n m
   snd (trFun∙ n m) =
     cong (subst (EM (H' ⨂ G')) (+'-comm n m)) (Iso→EMIso∙ ⨂-comm (n +' m))
     ∙ substCommSlice (λ _ → EM (H' ⨂ G') (m +' n)) (EM (H' ⨂ G'))
                      (λ n _ → 0ₖ n) (+'-comm n m) (0ₖ (m +' n))

   cpInd : (n m : ℕ) → (f g : EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ EM∙ (G' ⨂ H') (suc n +' suc m) ∙))
                      → ((x : EM-raw' G' (suc n)) (y : EM-raw' H' (suc m))
                      → f .fst (EM-raw'→EM _ _ x) .fst (EM-raw'→EM _ _ y)
                       ≡ g .fst (EM-raw'→EM _ _ x) .fst (EM-raw'→EM _ _ y))
                      → f ≡ g
   cpInd n m f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt (EM-raw'-elim G' (suc n)
           (λ _ → isOfHLevelPath' (suc (suc n)) (isOfHLevel↑∙ (suc n) m) _ _)
           λ x → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y i → f'≡g' y i .fst x)))
     where
     f' : EM H' (suc m) → EM-raw'∙ G' (suc n) →∙ EM∙ (G' ⨂ H') (suc n +' suc m)
     fst (f' y) x = f .fst (EM-raw'→EM _ _ x) .fst y
     snd (f' y) = cong (λ x → f .fst x .fst y) (EM-raw'→EM∙ G' (suc n))
                ∙ funExt⁻ (cong fst (f .snd)) y

     g' : EM H' (suc m) → EM-raw'∙ G' (suc n) →∙ EM∙ (G' ⨂ H') (suc n +' suc m)
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


-ₖ^[_·_]-Induced : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'}
  (n m k : ℕ) (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
  (ϕ : AbGroupHom G H) (x : EM G k)
  → inducedFun-EM ϕ k (-ₖ^[ n · m ] k p q x)
   ≡ -ₖ^[ n · m ] k p q (inducedFun-EM ϕ k x)
-ₖ^[ n · m ]-Induced k (inl x₁) q ϕ x =
  cong (inducedFun-EM ϕ k) (-ₖ^[ n · m ]-inl-left k x₁ q x)
  ∙ sym (-ₖ^[ n · m ]-inl-left k x₁ q _)
-ₖ^[ n · m ]-Induced k (inr x₁) (inl x₂) ϕ x =
  cong (inducedFun-EM ϕ k) (-ₖ^[ n · m ]-inl-right k (inr x₁) x₂ x)
  ∙ sym (-ₖ^[ n · m ]-inl-right k (inr x₁) x₂ _)
-ₖ^[ n · m ]-Induced k (inr x₁) (inr x₂) ϕ x =
    cong (inducedFun-EM ϕ k) (-ₖ^[ n · m ]-inr k x₁ x₂ x)
  ∙ inducedFun-EM-pres-ₖ ϕ k x
  ∙ sym (-ₖ^[ n · m ]-inr k x₁ x₂ _)


module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   private
     G = fst G'
     H = fst H'

     strG = snd G'
     strH = snd H'

     0G = 0g strG
     0H = 0g strH

     _+G_ = _+Gr_ strG
     _+H_ = _+Gr_ strH

     -H_ = -Gr_ strH
     -G_ = -Gr_ strG

   open PlusBis

   cp∙ : (n m : ℕ) → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cp∙ = cup∙

   cp'∙ : (n m : ℕ) → EM G' n → EM∙ H' m →∙ EM∙ (H' ⨂ G') (m +' n)
   fst (cp'∙ n m x) y = y ⌣ₖ x
   snd (cp'∙ n m x) = 0ₖ-⌣ₖ m n x

   cp∙∙ : (n m : ℕ) → EM∙ G' n →∙ (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
   fst (cp∙∙ n m) = cp∙ n m
   snd (cp∙∙ n m) = ptd
     where
     abstract
       ptd : cp∙ n m (snd (EM∙ G' n)) ≡ ((λ _ → 0ₖ (n +' m)) , refl)
       ptd = →∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ y → 0ₖ-⌣ₖ n m y)

   commF : (n : ℕ) → EM (H' ⨂ G') n → EM (G' ⨂ H') n
   commF n = Iso.fun (Iso→EMIso ⨂-comm _)

   commF' : (n : ℕ) → EM (H' ⨂ G') n → EM (G' ⨂ H') n
   commF' = λ n → Iso.inv (Iso→EMIso ⨂-comm _)

   commF≡commF' : (n : ℕ) → (x : _) → commF n x ≡ commF' n x
   commF≡commF' n =
     funExt⁻ (cong (λ F → inducedFun-EM F n) h)
     where
     h : Path (AbGroupHom (H' ⨂ G') (G' ⨂ H'))
              (GroupEquiv→GroupHom ⨂-comm)
              (GroupEquiv→GroupHom (invGroupEquiv ⨂-comm))
     h = Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl


{-
cong-ₖ^[_·_]₂ : (n m k : ℕ)
     (p : isEvenT n ⊎ isOddT n)
     (q : isEvenT m ⊎ isOddT m)
    → (x : EM G' (suc k))
-}

   cong-commF : (n : ℕ) (x : _)
     → cong (commF (suc (suc n))) (EM→ΩEM+1 (suc n) x) ≡ EM→ΩEM+1 (suc n) (commF (suc n) x)
   cong-commF n x = sym (EMFun-EM→ΩEM+1 (suc n) x)

   cong-cong-commF : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
     → cong (cong (commF (suc (suc (suc n))))) (wrap (suc (suc n)) p)
     ≡ wrap (suc (suc n)) (cong (commF (suc (suc n))) p)
   cong-cong-commF n p =
     TR.rec (hLevelEM _ (suc (suc (suc n))) _ _ _ _ _ _)
       (uncurry (λ x q k i j
         → hcomp (λ r → λ {(i = i0) → commF (suc (suc (suc n)))
                                   (EM→ΩEM+1-0ₖ (suc (suc n)) (r ∨ k) j)
                    ; (i = i1) → commF (suc (suc (suc n)))
                                   (EM→ΩEM+1-0ₖ (suc (suc n)) (r ∨ k) j)
                    ; (j = i0) → 0ₖ (3 +ℕ n)
                    ; (j = i1) → 0ₖ (3 +ℕ n)
                    ; (k = i0) → commF (suc (suc (suc n))) (pp-wrap (2 +ℕ n) (q r) r i j)
                    ; (k = i1) → wrap (suc (suc n)) (cong (commF (suc (suc n))) (q r)) i j})
                  (hcomp (λ r → λ {(i = i0) → commF (suc (suc (suc n)))
                                    ∣ rCancel-filler (merid north) r k j ∣ₕ
                    ; (i = i1) → commF (suc (suc (suc n)))
                                    ∣ rCancel-filler (merid north) r k j ∣ₕ
                    ; (j = i0) → 0ₖ (3 +ℕ n)
                    ; (j = i1) → ∣ merid north (~ r ∧ ~ k) ∣ₕ
                    ; (k = i0) → commF (suc (suc (suc n)))
                                  ∣ compPath-filler (merid (x i)) (sym (merid north)) r j ∣ₕ
                    ; (k = i1) → wrap (suc (suc n)) (cong (commF (suc (suc n))) (cong ∣_∣ₕ x)) i j})
                    (hcomp (λ r → λ {
                       (i = i0) → ∣ rCancel-filler (merid north) (~ r) k j ∣ₕ
                     ; (i = i1) → ∣ rCancel-filler (merid north) (~ r) k j ∣ₕ
                     ; (j = i0) → 0ₖ (3 +ℕ n)
                     ; (j = i1) → ∣ merid north (r ∧ ~ k) ∣ₕ
                     ; (k = i0) → ∣ compPath-filler
                                    (merid (inducedFun-EM-raw (GroupEquiv→GroupHom ⨂-comm)
                                      (suc (suc n)) (x i))) (sym (merid north)) (~ r) j ∣ₕ
                     ; (k = i1) → wrap (suc (suc n))
                                   (cong (commF (suc (suc n))) (cong ∣_∣ₕ x)) i j})
                     (pp-wrap (suc (suc n))
                                   (cong (commF (suc (suc n))) (cong ∣_∣ₕ x)) k i j)))))
       (asd n p)
         where
         asd : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
           → hLevelTrunc (2 +ℕ n)
            (Σ[ x ∈ north ≡ north ] cong ∣_∣ₕ x ≡ p)
         asd n p = TR.map (λ {(x , p) → (fst (asd4 n x)) , (sym (snd (asd4 n x)) ∙ p)})
                          (asd2 n p (asd3 n p))
           where
           asd3 : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
                → Σ[ x ∈ EM (H' ⨂ G') (suc n) ] EM→ΩEM+1 (suc n) x ≡ p
           asd3 n p = _ , Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) p

           asd2 : (n : ℕ) (p : fst (Ω (EM∙ (H' ⨂ G') (suc (suc n)))))
                 → Σ[ x ∈ EM (H' ⨂ G') (suc n) ] EM→ΩEM+1 (suc n) x ≡ p
                 → hLevelTrunc (2 +ℕ n) (Σ[ x ∈ EM-raw' (H' ⨂ G') (suc n) ]
                     EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x) ≡ p)
           asd2 n p =
             uncurry (EM-raw'-elim _ _
               (λ _ → isOfHLevelΠ (2 +ℕ n)
                λ _ → (isOfHLevelTrunc (2 +ℕ n)))
               λ x → J (λ p _ → hLevelTrunc (2 +ℕ n) (Σ[ x ∈ EM-raw' (H' ⨂ G') (suc n) ]
                     EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x) ≡ p))
                 ∣ x , refl ∣)

           asd4 : (n : ℕ)
                   (x : EM-raw' (H' ⨂ G') (suc n))
                → Σ[ r ∈ north ≡ north ] EM→ΩEM+1 (suc n) (EM-raw'→EM _ _ x) ≡ cong ∣_∣ₕ r
           asd4 zero x = _ , refl
           asd4 (suc n) x = _ , refl

   cp*∙∙ : (n m : ℕ) (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
     → EM∙ G' n →∙ (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
   fst (fst (cp*∙∙ n m p q) x) y =
     subst (EM (G' ⨂ H')) (+'-comm m n)
       (-ₖ^[ n · m ] (m +' n) p q
       (commF (m +' n) (y ⌣ₖ x)))
   snd (fst (cp*∙∙ n m p q) x) =
     cong (subst (EM (G' ⨂ H')) (+'-comm m n))
        (cong (-ₖ^[ n · m ] (m +' n) p q)
          (cong (commF (m +' n)) (0ₖ-⌣ₖ m n x) ∙ Iso→EMIso∙ ⨂-comm _)
         ∙ -ₖ^[ n · m ]∙ (m +' n) p q)
      ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
        (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _)
   snd (cp*∙∙ n m p q) =
     →∙Homogeneous≡ (isHomogeneousEM _)
       (funExt λ y
       → cong (subst (EM (G' ⨂ H')) (+'-comm m n))
        (cong (-ₖ^[ n · m ] (m +' n) p q)
          (cong (commF (m +' n)) (⌣ₖ-0ₖ m n y) ∙ Iso→EMIso∙ ⨂-comm _)
         ∙ -ₖ^[ n · m ]∙ (m +' n) p q)
      ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
        (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _))

   flipIt : (n m n' m' : ℕ) (l r : ℕ) (s : l ≡ r)
        (x : EM (H' ⨂ G') l) (y : EM (G' ⨂ H') r)
        (p : isEvenT n ⊎ isOddT n) (q : isEvenT m ⊎ isOddT m)
        (p' : isEvenT n' ⊎ isOddT n') (q' : isEvenT m' ⊎ isOddT m')
     → y ≡ subst (EM (G' ⨂ H')) s (-ₖ^[ n' · m' ] l p' q' (commF l x))
     → subst (EM (G' ⨂ H')) s (-ₖ^[ n · m ] l p q (commF l x))
      ≡ -ₖ^[ n · m ] r p q (-ₖ^[ n' · m' ] r p' q' y)
   flipIt n m n' m' l = J> λ x y p q p' q' id
    → transportRefl _
    ∙ sym (cong (-ₖ^[ n · m ] l p q) (-ₖ^[ n' · m' ]² l p' q' (commF l x)))
    ∙ sym (cong (λ y → -ₖ^[ n · m ] l p q (-ₖ^[ n' · m' ] l p' q' y)) (id ∙ transportRefl _))

   cp'∙∙ : (n m : ℕ) → EM∙ G' n →∙ (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
   fst (fst (cp'∙∙ n m) x) y =
     subst (EM (G' ⨂ H')) (+'-comm m n) (commF (m +' n) (y ⌣ₖ x))
   snd (fst (cp'∙∙ n m) x) =
       cong (subst (EM (G' ⨂ H')) (+'-comm m n))
            (cong (commF (m +' n)) (0ₖ-⌣ₖ m n x) ∙ Iso→EMIso∙ ⨂-comm _)
     ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
        (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _)
   snd (cp'∙∙ n m) = ptd
     where
     abstract
       ptd : fst (cp'∙∙ n m) (snd (EM∙ G' n)) ≡ snd (EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m) ∙)
       ptd = →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ y → cong (subst (EM (G' ⨂ H')) (+'-comm m n))
                           (cong (commF (m +' n)) (⌣ₖ-0ₖ m n y)
                           ∙ Iso→EMIso∙ ⨂-comm _)
                        ∙ substCommSlice (λ _ → EM (G' ⨂ H') (n +' m))
                           (EM (G' ⨂ H')) (λ n _ → 0ₖ n) (+'-comm m n) (0ₖ _))

   comm₀ : (m : ℕ) (x : fst G') (y : EM H' (suc m))
     → cp∙ zero (suc m) x .fst y
      ≡ commF (suc m) (cp'∙ zero (suc m) x .fst y)
   comm₀ zero x =
     EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
       λ { embase-raw → refl
         ; (emloop-raw g i) j → EM→ΩEM+1 _ (x ⊗ g) i}
   comm₀ (suc m) x =
     TR.elim
       (λ _ → isOfHLevelPath (4 +ℕ m) (hLevelEM _ (suc (suc m))) _ _)
       λ { north → refl
         ; south → refl
         ; (merid a i) j → l a j i}
       where
       l : (a : EM-raw H' (suc m))
         → EM→ΩEM+1 (suc m) (cp∙ zero (suc m) x .fst (EM-raw→EM _ _ a))
         ≡ cong (commF (suc (suc m)))
            (EM→ΩEM+1 (suc m) (cp'∙ zero (suc m) x
              .fst (EM-raw→EM _ _ a)))
       l a = cong (EM→ΩEM+1 (suc m)) (comm₀ m x (EM-raw→EM _ _ a))
          ∙ EMFun-EM→ΩEM+1 (suc m) (cp'∙ zero (suc m) x .fst (EM-raw→EM _ _ a))

   comm₁ : (m : ℕ) (p : isEvenT m ⊎ isOddT m) → cp∙∙ 1 m ≡ cp*∙∙ 1 m (inr tt) p
   comm₁ =
     elim+2 (λ { (inl x) →
               →∙Homogeneous≡
                 (isHomogeneous→∙ (isHomogeneousEM _))
                   (funExt (EM-raw'-elim _ 1
                     (λ _ → isOfHLevelPath' 2 (isOfHLevel→∙ 3 (hLevelEM _ 1)) _ _)
                       λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                         (funExt λ y → 1-0 x y
                                     ∙∙ sym (-ₖ^[ 1 · zero ]-inl-right 1
                                         (inr tt) tt (commF 1 (_⌣ₖ_ {n = zero} {m = suc zero} y
                                         (EM-raw'→EM G' (suc zero) x))))
                                     ∙∙ sym (transportRefl
                                         (-ₖ^[ 1 · zero ] 1 (inr tt) (inl tt)
                                         (commF 1 (_⌣ₖ_ {n = zero} {m = suc zero} y
                                         (EM-raw'→EM G' (suc zero) x))))))))})
            (λ { (inr x)
               → cpInd 0 0 _ _ λ x y → 1-1 x y
                                       ∙ sym (transportRefl
                                         (-ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
                                         (commF 2 (_⌣ₖ_ {n = suc zero} {m = suc zero}
                                           (EM-raw'→EM H' (suc zero) y)
                                         (EM-raw'→EM G' (suc zero) x)))))})
            λ { n ind p → cpInd 0 (suc n) _ _ (1-suc n ind p)}

     where
     1-0 : (x : EM-raw' G' 1) (y : fst H')
        → cp∙ 1 0 (EM-raw'→EM G' 1 x) .fst y
         ≡ commF 1 (_⌣ₖ_ {n = zero} y (EM-raw'→EM G' 1 x))
     1-0 embase-raw y = refl
     1-0 (emloop-raw g i) y = refl

     1-1 : (x : EM-raw' G' 1) (y : EM-raw' H' 1)
       → cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst
      (EM-raw'→EM H' (suc 0) y)
      ≡
      -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
      (commF 2 (_⌣ₖ_ {n = suc zero} {m = suc zero} (EM-raw'→EM H' 1 y) (EM-raw'→EM G' 1 x)))
     1-1 x embase-raw = ⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x)
     1-1 x (emloop-raw h i) = flipSquare help i
       where
       PP1 : (x : EM-raw' G' 1)
            → PathP (λ i → Path (EM (G' ⨂ H') 2)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i))
                   (cong (cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst) (emloop h))
                   (EM→ΩEM+1 (suc 0)
                    (-ₖ (commF 1 (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)))))
       PP1 embase-raw = sym (EM→ΩEM+1-0ₖ 1)
       PP1 (emloop-raw g i) j k =
         hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid embase) (~ j ∨ ~ r) k ∣
                        ; (i = i1) → ∣ rCancel (merid embase) (~ j ∨ ~ r) k ∣
                        ; (j = i0) → pp-wrap 1
                                       (λ i → (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i))) (~ r) k i
                        ; (j = i1) → pp-wrap 1
                                       (λ i → (-ₖ (commF 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i))))) (~ r) i k
                        ; (k = i0) → ⌣ₖ-0ₖ 1 1 (emloop g i) (j ∨ ~ r)
                        ; (k = i1) → ⌣ₖ-0ₖ 1 1 (emloop g i) (j ∨ ~ r)})
               (help j i k)
        where
        help : flipSquare (wrap 1 λ i → (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i)))
             ≡ wrap 1 λ i → (-ₖ (commF 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i))))
        help = sym (sym≡flipSquare (wrap 1 λ i → (_⌣ₖ_ {n = zero} {m = 1} g (emloop h i))))
             ∙ wrapEq 1 _ _
                (cong (cong (EM→ΩEM+1 1))
                  (sym (cong-₁ (λ i → commF 1 (_⌣ₖ_ {n = zero} {m = 1} h (emloop g i))))))

       help : PathP (λ i → Path (EM (G' ⨂ H') 2)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i))
                   (cong (cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst)
                         (emloop h))
                   (λ i → -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
                            (commF 2 (EM→ΩEM+1 (suc zero)
                            (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)) i)))
       help = PP1 x ▷ (sym (cong-ₖ^[ 1 · 1 ]₂ 0 (inr tt) (inr tt)
                             (commF 1 (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)))))
                      ∙ cong (cong (-ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)))
                             (EMFun-EM→ΩEM+1 1 (_⌣ₖ_ {n = zero} {m = suc zero}
                                                h (EM-raw'→EM G' 1 x)))

     module _ (n : ℕ) (ind : (p : isEvenT (suc n) ⊎ isOddT (suc n))
                                → cp∙∙ 1 (suc n) ≡ cp*∙∙ 1 (suc n) (inr tt) p)
       where
       south-c : (x : EM-raw' G' 1) (p : _)
        → cp∙∙ 1 (suc (suc n)) .fst (EM-raw'→EM G' (suc 0) x) .fst
           (EM-raw'→EM H' (suc (suc n)) south)
           ≡
           cp*∙∙ 1 (suc (suc n)) (inr tt) p .fst (EM-raw'→EM G' (suc 0) x)
           .fst (EM-raw'→EM H' (suc (suc n)) south)
       south-c embase-raw p = refl
       south-c (emloop-raw g i) p j = EM→ΩEM+1-0ₖ (suc (suc n)) j i


       1-suc : (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
               (x : EM-raw' G' (suc zero))
               (y : EM-raw' H' (suc (suc n))) →
               cp∙∙ 1 (suc (suc n)) .fst
                 (EM-raw'→EM G' (suc 0) x) .fst
                 (EM-raw'→EM H' (suc (suc n)) y)
               ≡ cp*∙∙ 1 (suc (suc n)) (inr tt) p .fst
                  (EM-raw'→EM G' (suc 0) x) .fst
                  (EM-raw'→EM H' (suc (suc n)) y)
       1-suc p x north = ⌣ₖ-0ₖ 1 (suc (suc n)) (EM-raw'→EM G' (suc 0) x)
       1-suc p x south = south-c x p
       1-suc p x (merid a i) j = main j i
         where
         good : (x : EM-raw' G' 1)
           → PathP
               (λ i₁ →
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
           hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (~ j ∨ ~ r) (~ k) ∣
                          ; (i = i1) → ∣ rCancel (merid north) (~ j ∨ ~ r) (~ k) ∣
                          ; (j = i0) → l-f (~ r) k i
                          ; (j = i1) → l-f (~ r) i (~ k)
                          ; (k = i0) → ∣ rCancel (merid north) (j ∨ ~ r) i ∣
                          ; (k = i1) → ∣ rCancel (merid north) (j ∨ ~ r) i ∣})
                 (phew j i k)

           where
           l-f = pp-wrap (suc (suc n))
                  (EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = G'} {H' = H'} {n = 0} {m = suc n} g (EM-raw→EM H' (suc n) a))) 
           l = wrap (suc (suc n)) (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = 0} {m = suc n} g (EM-raw→EM H' (suc n) a)))

           phew : flipSquare l ≡ cong sym l
           phew = sym (sym≡flipSquare l) ∙ sym≡cong-sym l


         lem5 : (n : ℕ) (p : _) (q : _) →  -ₖ^[ 1 · suc (suc n) ] (1 +' suc n) (inr tt) p
                  ∘ (-ₖ^[ 1 · suc n ] (1 +' suc n) (inr tt) q)
                  ≡ -ₖ_ {G = G' ⨂ H'}
         lem5 n (inl x) (inl x₁) = ⊥.rec (¬evenAndOdd _ (x , x₁))
         lem5 n (inl x) (inr x₁) i z =
           -ₖ^[ 1 · suc (suc n) ]-inl-right (1 +' suc n) (inr tt) x
             (-ₖ^[ 1 · suc n ]-inr (1 +' suc n) tt x₁ z i) i
         lem5 n (inr x) (inl x₁) i z =
           -ₖ^[ 1 · suc (suc n) ]-inr (1 +' suc n) tt x
             (-ₖ^[ 1 · suc n ]-inl-right (1 +' suc n) (inr tt) x₁ z i) i
         lem5 n (inr x) (inr x₁) = ⊥.rec (¬evenAndOdd _ (x , x₁))
   
         main : PathP (λ i → ⌣ₖ-0ₖ 1 (suc (suc n)) (EM-raw'→EM G' (suc 0) x) i
                           ≡ south-c x p i)
                      (λ i → cp∙∙ 1 (suc (suc n)) .fst (EM-raw'→EM G' (suc 0) x) .fst
                               (EM-raw'→EM H' (suc (suc n)) (merid a i)))
                      λ i → cp*∙∙ 1 (suc (suc n)) (inr tt) p .fst
                               (EM-raw'→EM G' (suc 0) x) .fst
                               (EM-raw'→EM H' (suc (suc n)) (merid a i))
         main = good x
              ▷ ((sym (EM→ΩEM+1-sym (suc (suc n))
                     (fst (fst (cp∙∙ 1 (suc n)) (EM-raw'→EM G' 1 x))
                      (EM-raw→EM H' (suc n) a)))
               ∙ cong (EM→ΩEM+1 (suc (suc n)))
                  (sym (funExt⁻ (lem5 n p (evenOrOdd (suc n))) ((fst (fst (cp∙∙ 1 (suc n)) (EM-raw'→EM G' 1 x))
                                 (EM-raw→EM H' (suc n) a))))))
               ∙ cong (EM→ΩEM+1 (suc (suc n)))
                 (sym (flipIt 1 (suc (suc n)) 1 (suc n) _ _ (+'-comm (suc n) 1) t1 (_⌣ₖ_ {n = 1} {m = suc n}
                   (EM-raw'→EM G' (suc zero) x) (EM-raw→EM H' (suc n) a))
                   (inr tt) p (inr tt) (evenOrOdd (suc n))
                   (funExt⁻
                    (cong fst (funExt⁻
                     (cong fst (ind (evenOrOdd (suc n))))
                      (EM-raw'→EM G' 1 x))) (EM-raw→EM H' (suc n) a))))
               ∙ sym lem3
               ∙ cong (cong (subst (EM (G' ⨂ H')) (+'-comm (suc (suc n)) 1)))
                   (sym (cong-ₖ^[ 1 · (suc (suc n)) ]₂ (suc (n +ℕ 0)) (inr tt) p
                         (commF (suc (suc (n +ℕ 0))) t1))
                   ∙ cong (cong (-ₖ^[ 1 · (suc (suc n)) ] ((suc (suc n)) +' 1) (inr tt) p))
                      (EMFun-EM→ΩEM+1 _ t1)))

           where
           t1 = _⌣ₖ_ {n = suc n} {m = 1} (EM-raw→EM H' (suc n) a) (EM-raw'→EM G' (suc zero) x)
           mid = EM→ΩEM+1 (suc (suc (n +ℕ 0)))
                  (-ₖ^[ 1 · suc (suc n) ] (suc (suc (n +ℕ 0))) (inr tt) p
                   (commF (suc (suc (n +ℕ 0))) t1))

           qq : (n₁ m : ℕ) (q : n₁ ≡ m)
             → snd (EM∙ (G' ⨂ H') m)
             ≡ subst (λ n₂ → EM∙ (G' ⨂ H') n₂ .fst) q (snd (EM∙ (G' ⨂ H') n₁))
           qq n = J> sym (transportRefl _)

           r2 : (n : ℕ) → (sym (qq (suc (suc n +' 1)) (suc (1 +' suc n)) (+'-comm (suc (suc n)) 1))) ≡ refl
           r2 n = transportRefl _

           bzt = cong-subst' _ _ (+'-comm (suc n) 1) (+'-comm (suc (suc n)) 1) (EM∙ (G' ⨂ H'))
                   EM→ΩEM+1 (λ x → EM→ΩEM+1-0ₖ _)
                   ((-ₖ^[ 1 · suc (suc n) ] (suc (suc (n +ℕ 0))) (inr tt) p
                        (commF (suc (suc (n +ℕ 0))) t1)))
                   qq
                   λ n → transportRefl (sym (transportRefl _))

           lem3 : cong (subst (EM (G' ⨂ H')) (+'-comm (suc (suc n)) 1)) mid
                ≡ EM→ΩEM+1 (suc (suc n))
                    (subst (EM (G' ⨂ H')) (+'-comm (suc n) 1)
                      (-ₖ^[ 1 · suc (suc n) ] (suc (suc (n +ℕ 0))) (inr tt) p
                        (commF (suc (suc (n +ℕ 0))) t1)))
           lem3 = bzt
                ∙ cong (λ x → sym x
                  ∙∙ EM→ΩEM+1 (suc (suc n))
                    (subst (EM (G' ⨂ H')) (+'-comm (suc n) 1)
                      (-ₖ^[ 1 · suc (suc n) ] (suc (suc (n +ℕ 0))) (inr tt) p
                        (commF (suc (suc (n +ℕ 0))) t1)))
                        ∙∙ x) (r2 n)
                ∙ sym (rUnit _)

module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   private
     G = fst G'
     H = fst H'

     strG = snd G'
     strH = snd H'

     0G = 0g strG
     0H = 0g strH

     _+G_ = _+Gr_ strG
     _+H_ = _+Gr_ strH

     -H_ = -Gr_ strH
     -G_ = -Gr_ strG

     open PlusBis

   cp∙∙' = cp∙∙ {G' = G'} {H' = H'}
   cp*∙∙' = cp*∙∙ {G' = G'} {H' = H'}

   comm₂ : (n m : ℕ)
     (p : isEvenT (suc n) ⊎ isOddT (suc n))
     (q : isEvenT (suc m) ⊎ isOddT (suc m))
     → cp∙∙' (suc n) (suc m) ≡ cp*∙∙' (suc n) (suc m) p q
   comm₂ =
     ℕ-elim2
       (λ {n (inr tt) q → comm₁ (suc n) q})
       (λ {n p (inr tt) →
         →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
           (funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ y
        → (((sym (Iso.leftInv (Iso→EMIso (⨂-comm {A = G'} {B = H'})
                  (suc (suc n) +' 1)) (cp∙∙' (suc (suc n)) 1 .fst x .fst y))
          ∙ sym (commF≡commF' {G' = G'} {H' = H'} (suc (suc n) +' 1) _)
          ∙ cong (commF _) (sym (-ₖ^[ suc (suc n) · 1 ]²-swap _ p (inr tt) _))
          ∙ -ₖ^[ suc (suc n) · 1 ]-Induced (suc (suc n) +' 1) p (inr tt) (GroupEquiv→GroupHom ⨂-comm) _)
         ∙ sym (transportRefl _)
          ∙ sym (substℕ-lem {A = EM (G' ⨂ H')} _ _ (+'-comm (suc (suc n)) 1) _ (+'-comm 1 (suc (suc n))) refl))
          ∙ cong (subst (EM (G' ⨂ H')) (+'-comm 1 (suc (suc n))))
                 (substCommSlice (EM (H' ⨂ G')) (EM (G' ⨂ H'))
                                 (λ k x → -ₖ^[ suc (suc n) · 1 ] k p (inr tt) (commF k x))
                                 (+'-comm (suc (suc n)) 1)
                   (-ₖ^[ 1 · suc (suc n) ] _ (inr tt) p (commF _ (x ⌣ₖ y)))))
         ∙ λ i → subst (EM (G' ⨂ H')) (+'-comm 1 (suc (suc n)))
                  (-ₖ^[ suc (suc n) · 1 ] (1 +' suc (suc n)) p (inr tt)
                  (commF (1 +' suc (suc n)) (comm₁ {G' = H'} {H' = G'}
                    (suc (suc n)) p (~ i) .fst y .fst x)))))}) -- comm₁ {G' = H'} {H' = G'} (suc (suc n)) p
       λ n m ind p q → cpInd _ _ _ _
         λ x y → main n m (ind .fst) (ind .snd .fst) (ind .snd .snd) p q x y
                ∙ λ i → subst (EM (G' ⨂ H'))
                   (isSetℕ _ _ (cong (3 +ℕ_) (+-comm m (suc n) ∙ sym (+-suc n m)))
                                (+'-comm (suc (suc m)) (suc (suc n))) i)
                   (-ₖ^[ (2 +ℕ n) · (2 +ℕ m) ] ((2 +ℕ m) +' (2 +ℕ n)) p q
                    (commF ((2 +ℕ m) +' (2 +ℕ n))
                     (_⌣ₖ_ {n = suc (suc m)} {m = suc (suc n)}
                     (EM-raw'→EM H' (suc (suc m)) y)
                     (EM-raw'→EM G' (suc (suc n)) x)))) -- (main n m (ind .fst) (ind .snd) p q)
       where
       module _ (n m : ℕ)
         (indₗ : ((p₁ : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
                 (q₁ : isEvenT (suc m) ⊎ isOddT (suc m))
              → cp∙∙ (suc (suc n)) (suc m) ≡ cp*∙∙ (suc (suc n)) (suc m) p₁ q₁))
         (indᵣ : ((p₁ : isEvenT (suc n) ⊎ isOddT (suc n))
                  (q₁ : isEvenT (suc (suc m)) ⊎ isOddT (suc (suc m)))
              → cp∙∙ (suc n) (suc (suc m)) ≡ cp*∙∙ (suc n) (suc (suc m)) p₁ q₁))
         (indₘ : (p₁ : isEvenT (suc n) ⊎ isOddT (suc n))
                 (q₁ : isEvenT (suc m) ⊎ isOddT (suc m)) →
                 cp∙∙ (suc n) (suc m) ≡ cp*∙∙ (suc n) (suc m) p₁ q₁)
         where
         Fᵣ : (p : _) (q : _) → EM (H' ⨂ G') (suc (suc m) +' suc n) → EM (G' ⨂ H') (2 +ℕ (n +ℕ suc m))
         Fᵣ p q x = subst (EM (G' ⨂ H')) (cong (2 +ℕ_) (+-comm (suc m) n))
              (-ₖ^[ suc n · suc (suc m) ] (suc (suc m) +' (suc n)) p q
              (commF (suc (suc m) +' suc n)  x))

         Fₗ : (p : _) (q : _)
          → EM (G' ⨂ H') (suc (suc n) +' suc m) → EM (H' ⨂ G') (suc m +' suc (suc n))
         Fₗ p q x =
           Iso.inv (Iso→EMIso ⨂-comm _)
              (-ₖ^[ suc (suc n) · suc m ] _ p q
               (subst (EM (G' ⨂ H')) (cong (2 +ℕ_) (sym (+-comm m (suc n)))) x))

         betterᵣ : (p : _) (q : _) (x : EM G' (suc n)) (y : EM H' (suc (suc m)))
           → _⌣ₖ_ {n = suc n} {m = (suc (suc m))} x y
           ≡ Fᵣ p q (_⌣ₖ_ {n = suc (suc m)} {m = suc n} y x)
         betterᵣ p q x y =
            (λ i → indᵣ p q i .fst x .fst y)
           ∙ λ i → subst (EM (G' ⨂ H'))
             (isSetℕ _ _ (+'-comm (suc (suc m)) (suc n)) (cong (2 +ℕ_) (+-comm (suc m) n)) i)
              (-ₖ^[ suc n · suc (suc m) ] (suc (suc m) +' (suc n)) p q
              (commF (suc (suc m) +' suc n) (_⌣ₖ_ {n = suc (suc m)} {m = suc n} y x)))

         betterₗ : (p : _) (q : _) (x : EM G' (suc (suc n))) (y : EM H' (suc m))
           → _⌣ₖ_ {n = suc m} {m = suc (suc n)} y x
           ≡ Fₗ p q (_⌣ₖ_ {n = suc (suc n)} {m = (suc m)} x y)
         betterₗ p q x y =
           (sym (Iso.leftInv (Iso→EMIso ⨂-comm (suc m +' (suc (suc n)))) (y ⌣ₖ x))
           ∙ cong (Iso.inv (Iso→EMIso ⨂-comm (suc m +' (suc (suc n)))))
                  (sym (-ₖ^[ suc (suc n) · suc m ]² _ p q _)
                 ∙ cong (-ₖ^[ suc (suc n) · suc m ] _ p q)
                   (sym (transport⁻Transport
                         (λ i → EM (G' ⨂ H') (2 +ℕ (+-comm m (suc n) i))) _)
                  ∙ cong (subst (EM (G' ⨂ H')) (cong (2 +ℕ_) (sym (+-comm m (suc n)))))
                    λ i → subst (EM (G' ⨂ H'))
                            (isSetℕ _ _ 
                             (cong (2 +ℕ_) (+-comm m (suc n)))
                             (+'-comm (suc m) (suc (suc n))) i)
                             (-ₖ^[ suc (suc n) · suc m ] (suc m +' suc (suc n)) p q
                             (commF (suc m +' suc (suc n)) (y ⌣ₖ x)))))
           ∙ cong (Fₗ p q) (λ i → indₗ p q (~ i) .fst x .fst y))

         ℕpath = cong (2 +ℕ_) (+-comm m (suc n) ∙ sym (+-suc n m))

         st : (p : isEvenT (suc (suc n)) ⊎ isOddT (suc (suc n)))
              (q : isEvenT (suc (suc m)) ⊎ isOddT (suc (suc m)))
           → EM (H' ⨂ G') ((2 +ℕ m) +' (2 +ℕ n)) → EM (G' ⨂ H') ((2 +ℕ n) +' (2 +ℕ m))
         st p q x = subst (EM (G' ⨂ H')) (cong suc ℕpath)
                   (-ₖ^[ (2 +ℕ n) · (2 +ℕ m) ] ((2 +ℕ m) +' (2 +ℕ n)) p q
                    (commF ((2 +ℕ m) +' (2 +ℕ n)) x ))

         main : (p : _) (q : _)
           → (x : EM-raw' G' (suc (suc n))) (y : EM-raw' H' (suc (suc m)))
              →    cp∙∙ (suc (suc n)) (suc (suc m)) .fst
                    (EM-raw'→EM G' (suc (suc n)) x) .fst
                    (EM-raw'→EM H' (suc (suc m)) y)
                    ≡ st p q (
                     _⌣ₖ_ {n = suc (suc m)} {m = suc (suc n)}
                      (EM-raw'→EM H' (suc (suc m)) y) (EM-raw'→EM G' (suc (suc n)) x))
         main p q north north = refl
         main p q south north = refl
         main p q (merid a i) north k =
            (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
              (betterᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ a) ∣ north ∣)
           ∙ EM→ΩEM+1-0ₖ _) k i
         main p q north south = refl
         main p q south south = refl
         main p q (merid a i) south k =
           (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
             (betterᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ a) ∣ south ∣)
           ∙ EM→ΩEM+1-0ₖ _) k i
         main p q north (merid a i) k =
           st p q ((cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                (betterₗ p (evenOrOdd (suc m))  ∣ north ∣ (EM-raw→EM _ _ a))
                ∙ EM→ΩEM+1-0ₖ _) (~ k) i)
         main p q south (merid a i) k =
           st p q ((cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                    (betterₗ p (evenOrOdd (suc m)) ∣ south ∣ (EM-raw→EM _ _ a))
                    ∙ EM→ΩEM+1-0ₖ _) (~ k) i)
         main p q (merid b i) (merid a j) k =
           hcomp (λ r →
            λ {(i = i0) → st p q (compPath-filler' (cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                              (betterₗ p (evenOrOdd (suc m)) ∣ north ∣ (EM-raw→EM _ _ a)))
                              (EM→ΩEM+1-0ₖ _) r (~ k) j)
              ; (i = i1) → st p q (compPath-filler' (cong (EM→ΩEM+1 (suc (suc (m +ℕ suc n))))
                              (betterₗ p (evenOrOdd (suc m)) ∣ south ∣ (EM-raw→EM _ _ a)))
                              (EM→ΩEM+1-0ₖ _) r (~ k) j)
              ; (j = i0) → compPath-filler'
                             (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
                              (betterᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b) ∣ north ∣))
                              (EM→ΩEM+1-0ₖ _) r k i
              ; (j = i1) → compPath-filler'
                             (cong (EM→ΩEM+1 (suc (suc (n +ℕ suc m))))
                              (betterᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b) ∣ south ∣))
                              (EM→ΩEM+1-0ₖ _) r k i
              ; (k = i0) → EM→ΩEM+1 (suc (suc (n +ℕ suc m)))
                             (betterᵣ (evenOrOdd (suc n)) q (EM-raw→EM _ _ b) ∣ merid a j ∣ (~ r)) i
              ; (k = i1) → st p q
                             (EM→ΩEM+1 _
                              (betterₗ p (evenOrOdd (suc m)) ∣ (merid b i) ∣
                                (EM-raw→EM _ _ a) (~ r)) j)})
              (hcomp (λ r →
            λ {(i = i0) → st p q ((EM→ΩEM+1-0ₖ _) (~ k ∨ ~ r) j)
              ; (i = i1) → st p q ((EM→ΩEM+1-0ₖ _) (~ k ∨ ~ r) j)
              ; (j = i0) → EM→ΩEM+1-0ₖ (suc (suc (n +ℕ suc m))) (k ∨ ~ r) i
              ; (j = i1) → EM→ΩEM+1-0ₖ (suc (suc (n +ℕ suc m))) (k ∨ ~ r) i
              ; (k = i0) → pp-wrap _ (cong (Fᵣ (evenOrOdd (suc n)) q)
                                 (EM→ΩEM+1 (suc m +' suc n)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))) (~ r) j i
              ; (k = i1) → st p q (pp-wrap (suc (suc (m +ℕ suc n))) (cong (Fₗ p (evenOrOdd (suc m)))
                                 (EM→ΩEM+1 (suc n +' suc m)
                                  (_⌣ₖ_ {n = suc n} {m = suc m}
                                   (EM-raw→EM G' (suc n) b)
                                   (EM-raw→EM H' (suc m) a)))) (~ r) i j)})
                (final k i j)) -- (final k i j))
          where

          Q = (cong (Fₗ p (evenOrOdd (suc m)))
                 (EM→ΩEM+1 (suc n +' suc m)
                  (_⌣ₖ_ {n = suc n} {m = suc m}
                   (EM-raw→EM G' (suc n) b)
                   (EM-raw→EM H' (suc m) a))))

          cong-transpLem : (x : _)
            → cong (subst (EM (G' ⨂ H')) (cong (2 +ℕ_) (sym (+-comm m (suc n)))))
                (EM→ΩEM+1 (suc n +' suc m) x)
              ≡ EM→ΩEM+1 (suc (m +ℕ suc n))
                 (subst (EM (G' ⨂ H')) (cong suc (sym (+-comm m (suc n))))
                   x)
          cong-transpLem x j i =
            transp (λ i → EM (G' ⨂ H') (2 +ℕ (+-comm m (suc n) (~ i ∧ ~ j)))) j
              (EM→ΩEM+1 (suc (+-comm m (suc n) (~ j)))
                (transp (λ i → EM (G' ⨂ H') (suc (+-comm m (suc n) (~ i ∨ ~ j)))) (~ j) x) i)

          Q''' : (x : EM (H' ⨂ G') (suc m +' suc n))
                (p : isEvenT (2 +ℕ n) ⊎ isOddT (2 +ℕ n))
                (q : (isEvenT (suc m) ⊎ isOddT (suc m)))
                (p' : _) → EM (H' ⨂ G') (suc (m +ℕ suc n))
          Q''' x p q p' =
            subst (EM (H' ⨂ G')) (cong suc (sym (+-suc m n)))
              (-ₖ^[ suc (suc n) · suc m ] (suc m +' suc n) p q
                (-ₖ^[ suc n · suc m ] (suc m +' suc n) p' q
                  x))



          Q' = (Iso.inv (Iso→EMIso ⨂-comm _)
                            (-ₖ^[ suc (suc n) · suc m ] (suc (m +ℕ suc n)) p (evenOrOdd (suc m))
                            (subst (EM (G' ⨂ H')) (cong suc (sym (+-comm m (suc n))))
                              (_⌣ₖ_ {n = suc n} {m = suc m}
                                (EM-raw→EM G' (suc n) b)
                                (EM-raw→EM H' (suc m) a)))))

          Q'≡Q'' : Q' ≡ Q''' (_⌣ₖ_ {n = suc m} {m = suc n}
                             (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b)) p
                             (evenOrOdd (suc m)) (evenOrOdd (suc n))
          Q'≡Q'' = cong (Iso.inv (Iso→EMIso ⨂-comm _))
                        (cong (-ₖ^[ suc (suc n) · suc m ] (suc (m +ℕ suc n)) p (evenOrOdd (suc m)))
                         (cong (subst (EM (G' ⨂ H')) (cong suc (sym (+-comm m (suc n)))))
                             (λ i → indₘ (evenOrOdd (suc n))
                                          (evenOrOdd (suc m)) i .fst
                                          (EM-raw→EM G' (suc n) b) .fst
                                          (EM-raw→EM H' (suc m) a)
                                         )
                      ∙ substℕ-lem _ _ (+'-comm (suc m) (suc n)) _
                                    (sym (cong suc (+-comm m (suc n))))
                                    (cong suc (sym (+-suc m n)))
                       ∙ cong (subst (EM (G' ⨂ H')) (cong suc (sym (+-suc m n))))
                              (sym (-ₖ^[ suc n · suc m ]-Induced (suc m +' suc n)
                                  (evenOrOdd (suc n)) (evenOrOdd (suc m)) (GroupEquiv→GroupHom ⨂-comm)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                  (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b))))))
                 ∙ sym (substCommSlice (EM (G' ⨂ H')) (EM (H' ⨂ G'))
                     (λ k x → Iso.inv (Iso→EMIso ⨂-comm k)
                                (-ₖ^[ suc (suc n) · suc m ] k p
                                 (evenOrOdd (suc m)) x))
                     (cong suc (sym (+-suc m n)))
                     _)
                 ∙ cong (subst (EM (H' ⨂ G')) (cong suc (sym (+-suc m n))))
                        (cong (Iso.inv (Iso→EMIso ⨂-comm _))
                          (sym (-ₖ^[ suc (suc n) · suc m ]-Induced (suc (suc (m +ℕ n)))
                                p (evenOrOdd (suc m)) (GroupEquiv→GroupHom ⨂-comm) _))
                       ∙ Iso.leftInv (Iso→EMIso ⨂-comm (suc (suc (m +ℕ n)))) _)
          cong-Fₗ-Q : Q ≡ EM→ΩEM+1 (suc (m +ℕ suc n))
            (Q''' (_⌣ₖ_ {n = suc m} {m = suc n}
                  (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b)) p
                  (evenOrOdd (suc m)) (evenOrOdd (suc n)))
          cong-Fₗ-Q = cong (cong (Iso.inv (Iso→EMIso ⨂-comm _) ∘ 
                            (-ₖ^[ suc (suc n) · suc m ] _ p (evenOrOdd (suc m)))))
                          (cong-transpLem (_⌣ₖ_ {n = suc n} {m = suc m}
                             (EM-raw→EM G' (suc n) b)
                             (EM-raw→EM H' (suc m) a)))
                   ∙ cong (cong (Iso.inv (Iso→EMIso ⨂-comm _)))
                          (cong-ₖ^[ suc (suc n) · suc m ]₂ _ p (evenOrOdd (suc m)) _)
                   ∙ sym (EMFun-EM→ΩEM+1 _ _)
                   ∙ cong (EM→ΩEM+1 (suc (m +ℕ suc n))) Q'≡Q''

          Q* = Q''' (_⌣ₖ_ {n = suc m} {m = suc n}
                             (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b)) p
                             (evenOrOdd (suc m)) (evenOrOdd (suc n))

          ℕP1 : suc (suc (m +ℕ suc n)) ≡ suc (suc (n +ℕ suc m))
          ℕP1 = cong (2 +ℕ_) (+-comm m (suc n) ∙ sym (+-suc n m))

          p3 = transport (λ i → fst (Ω (EM∙ (H' ⨂ G') (ℕpath i)))) Q

          lem₁ : cong (-ₖ^[ 2 +ℕ n · 2 +ℕ m ] (suc (suc (n +ℕ suc m))) p q)
                  (λ i₁ → commF (suc (suc (n +ℕ suc m))) (p3 (~ i₁)))
                 ≡ transport (λ i → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i))))
                     (cong (-ₖ^[ 2 +ℕ n · 2 +ℕ m ] (suc (suc (m +ℕ suc n))) p q)
                       (cong (commF (suc (suc (m +ℕ suc n))))
                        (EM→ΩEM+1 (suc (m +ℕ suc n)) (-ₖ Q*))))
          lem₁ = (λ i → transp (λ j → fst (Ω (EM∙ (G' ⨂ H') (ℕpath (~ i ∨ j))))) (~ i)
                               (cong (-ₖ^[ 2 +ℕ n · 2 +ℕ m ] (ℕpath (~ i)) p q)
                                 (cong (commF (ℕpath (~ i)))
                                  (transp (λ j → fst (Ω (EM∙ (H' ⨂ G') (ℕpath (~ i ∧ j))))) i
                                    (sym Q)))))
               ∙ cong (transport (λ i → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i))))
                      ∘ (cong (-ₖ^[ 2 +ℕ n · 2 +ℕ m ] (suc (suc (m +ℕ suc n))) p q)
                      ∘ (cong (commF (suc (suc (m +ℕ suc n)))))))
                      (cong sym cong-Fₗ-Q
                      ∙ sym (EM→ΩEM+1-sym (suc (m +ℕ suc n)) Q*))
               ∙ refl


          lem₃ : {n : ℕ} (m : ℕ) (p : n ≡ m) (x : typ (Ω (EM∙ (G' ⨂ H') _)))
            → subst (λ n → typ (Ω (EM∙ (G' ⨂ H') n))) (cong (suc ∘ suc) p)
                    x
            ≡ cong (subst (EM (G' ⨂ H')) (cong (suc ∘ suc) p)) x
          lem₃ = J> λ x → transportRefl x ∙ λ j i → transportRefl (x i) (~ j)

          final : flipSquare
                    (wrap (suc (suc (n +ℕ suc m)))
                      (cong (Fᵣ (evenOrOdd (suc n)) q)
                                 (EM→ΩEM+1 (suc m +' suc n)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))))
                ≡ cong (cong (st p q))
                       (wrap (suc m +' suc (suc n)) Q)
          final = sym (sym≡flipSquare _)
                ∙ cong (sym ∘ wrap (suc (suc (n +ℕ suc m))))
                       ((λ _ → (cong (Fᵣ (evenOrOdd (suc n)) q)
                                 (EM→ΩEM+1 (suc m +' suc n)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))))
                      ∙ (sym (lem₃ _ (+-comm (suc m) n) (cong 
                       (-ₖ^[ suc n · suc (suc m) ] (suc (suc m) +' (suc n)) (evenOrOdd (suc n)) q
                         ∘ (commF (suc (suc m) +' suc n)))
                       (EM→ΩEM+1 (suc m +' suc n)
                                  (_⌣ₖ_ {n = suc m} {m = suc n}
                                   (EM-raw→EM H' (suc m) a)
                                   (EM-raw→EM G' (suc n) b)))))
                     ∙ cong (subst (λ n → typ (Ω (EM∙ (G' ⨂ H') n)))
                                   (cong (suc ∘ suc) (+-comm (suc m) n)))
                            (cong (cong (-ₖ^[ suc n · suc (suc m) ] (suc (suc m) +' suc n)
                                  (evenOrOdd (suc n)) q))
                                  (sym (EMFun-EM→ΩEM+1 _ (_⌣ₖ_ {n = suc m} {m = suc n}
                                     (EM-raw→EM H' (suc m) a)
                                     (EM-raw→EM G' (suc n) b))))
                           ∙ cong-ₖ^[ suc n · suc (suc m) ]₂ _ (evenOrOdd (suc n)) q
                               (commF _ (_⌣ₖ_ {n = suc m} {m = suc n}
                                     (EM-raw→EM H' (suc m) a)
                                     (EM-raw→EM G' (suc n) b)))
                           ∙ cong (EM→ΩEM+1 (suc (suc (m +ℕ n))))
                                  (sym (-ₖ^[ suc n · suc (suc m) ]-Induced
                                      (suc m +' suc n)
                                      (evenOrOdd (suc n)) q
                                      (GroupEquiv→GroupHom ⨂-comm)
                                      ((_⌣ₖ_ {n = suc m} {m = suc n}
                                     (EM-raw→EM H' (suc m) a)
                                     (EM-raw→EM G' (suc n) b))))
                                 ∙ cong (commF (suc m +' suc n))
                                   (-Lem (suc n) (suc m) (suc m +' suc n) p q
                                     (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                     (_⌣ₖ_ {n = suc m} {m = suc n}
                                       (EM-raw→EM H' (suc m) a)
                                       (EM-raw→EM G' (suc n) b)))
                                 ∙ -ₖ^[ suc (suc n) · suc (suc m) ]-Induced
                                     (suc (suc (m +ℕ n))) p q
                                     (GroupEquiv→GroupHom ⨂-comm) _)))
                      ∙ sym (substℕ-lem {A = λ n → typ (Ω (EM∙ (G' ⨂ H') n))} _ _
                             (cong (suc ∘ suc) (sym (+-suc m n))) _ ℕpath
                            (cong (suc ∘ suc) (+-comm (suc m) n)))
                      ∙ cong (transport (λ i₁ → fst (Ω (EM∙ (G' ⨂ H') (ℕpath i₁)))))
                             ((substCommSlice (EM (H' ⨂ G'))
                               (λ n → typ (Ω (EM∙ (G' ⨂ H') (suc n))))
                               (λ k x → EM→ΩEM+1 k (-ₖ^[ 2 +ℕ n · 2 +ℕ m ]
                                                     k p q (commF k (-ₖ x))))
                               (cong suc (sym (+-suc m n)))
                               ((-ₖ^[ suc (suc n) · suc m ] (suc m +' suc n) p (evenOrOdd (suc m))
                                (-ₖ^[ suc n · suc m ] (suc m +' suc n) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                  ((_⌣ₖ_ {n = suc m} {m = suc n}
                                 (EM-raw→EM H' (suc m) a) (EM-raw→EM G' (suc n) b)))))))
                            ∙ sym (cong-ₖ^[ 2 +ℕ n · 2 +ℕ m ]₂ (m +ℕ suc n) p q _)
                            ∙ cong (cong (-ₖ^[ 2 +ℕ n · 2 +ℕ m ] (suc (suc (m +ℕ suc n))) p q))
                                (EMFun-EM→ΩEM+1 _ _))
                      ∙ sym lem₁)
                ∙ cong sym (sym (cong-cong-ₖ^[ (2 +ℕ n) · (2 +ℕ m) ]₂
                        (n +ℕ suc m) p q (cong (commF (suc (suc (n +ℕ suc m)))) (sym p3))))
                ∙∙ cong (cong (cong (-ₖ^[ (2 +ℕ n) · (2 +ℕ m) ] (suc (ℕpath i1)) p q)))
                        (sym (cong-cong-commF _ p3))
                ∙∙ λ k i j
                 → transp (λ j
                   → EM (G' ⨂ H') (suc (ℕpath (j ∨ ~ k))))
                     (~ k)
                     (-ₖ^[ (2 +ℕ n) · (2 +ℕ m) ] (suc (ℕpath (~ k))) p q
                      (commF (suc (ℕpath (~ k)))
                        (wrap (ℕpath (~ k))
                          (transp (λ i → fst (Ω (EM∙ (H' ⨂ G') (ℕpath (~ k ∧ i))))) k
                           Q) i j)))

module _ {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
  ⌣ₖ-comm : (n m : ℕ) (x : EM G' n) (y : EM H' m)
    → x ⌣ₖ y ≡ subst (EM (G' ⨂ H')) (+'-comm m n)
                 (-ₖ^[ n · m ] (m +' n) (evenOrOdd n) (evenOrOdd m)
                  (commF (m +' n) (y ⌣ₖ x)))
  ⌣ₖ-comm zero zero x y = sym (transportRefl (commF zero (_⌣ₖ_ {n = zero} {m = zero} y x)))
  ⌣ₖ-comm zero (suc m) x y =
       comm₀ m x y
     ∙ sym ((λ i → subst (EM (G' ⨂ H')) (isSetℕ _ _ (+'-comm (suc m) zero) refl i)
           ((-ₖ^[ zero · suc m ] (suc m) (inl tt) (evenOrOdd (suc m))
             (commF (suc m) (_⌣ₖ_ {m = zero} y x)))))
         ∙ transportRefl _
         ∙ -ₖ^[ zero · suc m ]-inl-left (suc m) tt
             (evenOrOdd (suc m))
             (commF (suc m) (_⌣ₖ_ {m = zero} y x)))
  ⌣ₖ-comm (suc n) zero x y =
       ((sym (Iso.leftInv (Iso→EMIso ⨂-comm _) (_⌣ₖ_ {n = suc n} {m = zero} x y))
       ∙ sym (commF≡commF' (suc n) _))
       ∙ cong (commF (suc n)) (sym (comm₀ n y x)))
      ∙ sym (-ₖ^[ suc n · zero ]-inl-right (suc n) (evenOrOdd (suc n)) tt
            (commF (suc n) (_⌣ₖ_ {n = zero} {m = suc n} y x)))
     ∙ sym (transportRefl _)
     ∙ λ i → subst (EM (G' ⨂ H')) (isSetℕ _ _ refl (+'-comm zero (suc n)) i)
      (-ₖ^[ suc n · zero ] (suc n) (evenOrOdd (suc n)) (inl tt)
       (commF (suc n) (_⌣ₖ_ {n = zero} {m = suc n} y x)))
  ⌣ₖ-comm (suc n) (suc m) x y i = comm₂ n m (evenOrOdd (suc n)) (evenOrOdd (suc m)) i .fst x .fst y
