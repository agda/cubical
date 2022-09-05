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

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)

variable
  ℓ ℓ' : Level

module _ {G' : AbGroup ℓ} where
   private
     G = fst G'

     strG = snd G'

     0G = 0g strG

     _+G_ = _+Gr_ strG

     -G_ = -Gr_ strG
     open PlusBis

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

   -ₖ^[_·_]-inr : {!(n m k : ℕ)
      (p : _)
      (q : isEvenT m)
      (x : EM G' k)
     → -ₖ^[ n · m ] k p (inl q) x ≡ ?!}
   -ₖ^[_·_]-inr = {!!}

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
                                     ∙∙ sym (-ₖ^[ 1 · zero ]-inl-right 1 (inr tt) tt (commF 1 (_⌣ₖ_ {n = zero} {m = suc zero} y
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
            {!!}

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
     1-1 x (emloop-raw h i) = flipSquare (help x) i
       where
       help : (x : EM-raw' G' 1)
            → PathP (λ i → Path (EM (G' ⨂ H') 2)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i)
                     (⌣ₖ-0ₖ (suc zero) (suc zero) (EM-raw'→EM _ 1 x) i))
                   (cong (cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) x) .fst)
                         (emloop h))
                   (λ i → -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
                            (commF 2 (EM→ΩEM+1 (suc zero)
                            (_⌣ₖ_ {n = zero} {m = suc zero} h (EM-raw'→EM G' 1 x)) i)))
       help x = {!!} ▷ (({!!}
                       ∙ {!!})
                      ∙ cong (cong (-ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)))
                             (EMFun-EM→ΩEM+1 1 (_⌣ₖ_ {n = zero} {m = suc zero}
                                                h (EM-raw'→EM G' 1 x))))
     

     -- 1-1 embase-raw embase-raw = refl
     -- 1-1 embase-raw (emloop-raw g k) j =
     --   -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
     --     (commF 2 (∣ rCancel (merid ptEM-raw) (~ j) k ∣ₕ))
     -- 1-1 (emloop-raw g i) embase-raw j = ∣ rCancel (merid ptEM-raw) j i ∣ₕ
     -- 1-1 (emloop-raw g i) (emloop-raw h k) j =
     --   hcomp (λ r → λ {(i = i0) → -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
     --                                 (commF 2 (∣ rCancel (merid ptEM-raw) (~ j ∨ ~ r) k ∣ₕ))
     --                  ; (i = i1) → -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
     --                                 (commF 2 (∣ rCancel (merid ptEM-raw) (~ j ∨ ~ r) k ∣ₕ))
     --                  ; (k = i0) → ∣ rCancel (merid ptEM-raw) (j ∨ ~ r) i ∣ₕ
     --                  ; (k = i1) → ∣ rCancel (merid ptEM-raw) (j ∨ ~ r) i ∣ₕ
     --                  ; (j = i0) → doubleCompPath-filler
     --                                 (λ j i → ∣ rCancel (merid ptEM-raw) (~ j) i ∣ₕ)
     --                                 (λ j i → cp∙∙ 1 1 .fst (EM-raw'→EM G' (suc 0) (emloop-raw g i)) .fst (emloop h j))
     --                                 (λ j i → ∣ rCancel (merid ptEM-raw) j i ∣ₕ) (~ r) k i
     --                  ; (j = i1) → -ₖ^[ 1 · 1 ] 2 (inr tt) (inr tt)
     --                                  (commF 2
     --                                    {!doubleCompPath-filler ?!})})
     --         {!!}
