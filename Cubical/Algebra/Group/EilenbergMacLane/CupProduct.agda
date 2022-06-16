{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.CupProduct where

open import Cubical.Algebra.Group.EilenbergMacLane.Base renaming (elim to EM-elim)
open import Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity
open import Cubical.Algebra.Group.EilenbergMacLane.GroupStructure
open import Cubical.Algebra.Group.EilenbergMacLane.Properties
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Functions.Morphism

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1 renaming (rec to EMrec)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat hiding (_·_) renaming (elim to ℕelim)
open import Cubical.HITs.Susp

open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)

open PlusBis

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Lemma for distributativity of cup product (used later)
pathType : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → Type ℓ
pathType n x p = sym (rUnitₖ (2 + n) x) ∙ (λ i → x +ₖ p i)
               ≡ sym (lUnitₖ (2 + n) x) ∙ λ i → p i +ₖ x

pathTypeMake : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x)
    → pathType n x p
pathTypeMake n x = J (λ x p → pathType n x p) refl


-- Definition of cup product (⌣ₖ, given by ·₀ when first argument is in K(G,0))
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

   ·₀' : H → (m : ℕ) → EM G' m → EM (G' ⨂ H') m
   ·₀' h =
     elim+2
       (_⊗ h)
       (elimGroupoid _ (λ _ → emsquash)
         embase
         (λ g → emloop (g ⊗ h))
         λ g l →
           compPathR→PathP
             (sym (∙assoc _ _ _
                ∙∙ cong₂ _∙_ (sym (emloop-comp _ _ _)
                            ∙ cong emloop (sym (⊗DistL+⊗ g l h))) refl
                ∙∙ rCancel _)))
       λ n f → trRec (isOfHLevelTrunc (4 + n))
                        λ { north → 0ₖ (suc (suc n))
                          ; south → 0ₖ (suc (suc n))
                          ; (merid a i) → EM→ΩEM+1 (suc n) (f (EM-raw→EM _ _ a)) i}

   ·₀ : G → (m : ℕ) → EM H' m → EM (G' ⨂ H') m
   ·₀ g =
     elim+2 (λ h → g ⊗ h)
               (elimGroupoid _ (λ _ → emsquash)
                 embase
                 (λ h → emloop (g ⊗ h))
                 λ h l → compPathR→PathP
                   (sym (∙assoc _ _ _
                      ∙∙ cong₂ _∙_ (sym (emloop-comp _ _ _) ∙ cong emloop (sym (⊗DistR+⊗ g h l))) refl
                      ∙∙ rCancel _)))
               λ n f
               → trRec (isOfHLevelTrunc (4 + n))
                        λ { north → 0ₖ (suc (suc n))
                          ; south → 0ₖ (suc (suc n))
                          ; (merid a i) → EM→ΩEM+1 (suc n) (f (EM-raw→EM _ _ a)) i}

   ·₀-distr : (g h : G) → (m : ℕ)  (x : EM H' m) → ·₀ (g +G h) m x ≡ ·₀ g m x +ₖ ·₀ h m x
   ·₀-distr g h =
     elim+2
       (⊗DistL+⊗ g h)
       (elimSet _ (λ _ → emsquash _ _)
         refl
         (λ w → compPathR→PathP (sym ((λ i → emloop (⊗DistL+⊗ g h w i)
                               ∙ (lUnit (sym (cong₂+₁ (emloop (g ⊗ w)) (emloop (h ⊗ w)) i)) (~ i)))
              ∙∙ cong₂ _∙_ (emloop-comp _ (g ⊗ w) (h ⊗ w)) refl
              ∙∙ rCancel _))))
       λ m ind →
         trElim (λ _ → isOfHLevelTruncPath)
                λ { north → refl
                  ; south → refl
                  ; (merid a i) k → z m ind a k i}

      where
      z : (m : ℕ) → ((x : EM H' (suc m))
        → ·₀ (g +G h) (suc m) x
         ≡ ·₀ g (suc m) x +ₖ ·₀ h (suc m) x) → (a : EM-raw H' (suc m))
        → cong (·₀ (g +G h) (suc (suc m))) (cong ∣_∣ₕ (merid a)) ≡
          cong₂ _+ₖ_
            (cong (·₀ g (suc (suc m))) (cong ∣_∣ₕ (merid a)))
            (cong (·₀ h (suc (suc m))) (cong ∣_∣ₕ (merid a)))
      z m ind a = (λ i → EM→ΩEM+1 _ (ind (EM-raw→EM _ _ a) i))
               ∙∙ EM→ΩEM+1-hom _ (·₀ g (suc m) (EM-raw→EM H' (suc m) a))
                                  (·₀ h (suc m) (EM-raw→EM H' (suc m) a))
               ∙∙ sym (cong₂+₂ m (cong (·₀ g (suc (suc m))) (cong ∣_∣ₕ (merid a)))
                                 (cong (·₀ h (suc (suc m))) (cong ∣_∣ₕ (merid a))))

   ·₀0 : (m : ℕ) → (g : G) → ·₀ g m (0ₖ m) ≡ 0ₖ m
   ·₀0 zero = ⊗AnnihilR
   ·₀0 (suc zero) g = refl
   ·₀0 (suc (suc m)) g = refl

   ·₀'0 : (m : ℕ) (h : H) → ·₀' h m (0ₖ m) ≡ 0ₖ m
   ·₀'0 zero = ⊗AnnihilL
   ·₀'0 (suc zero) g = refl
   ·₀'0 (suc (suc m)) g = refl

   0·₀ : (m : ℕ) → (x : _) → ·₀ 0G m x ≡ 0ₖ m
   0·₀ =
     elim+2 ⊗AnnihilL
       (elimSet _ (λ _ → emsquash _ _)
         refl
         λ g → compPathR→PathP ((sym (emloop-1g _)
                                ∙ cong emloop (sym (⊗AnnihilL g)))
                                ∙∙ (λ i → rUnit (rUnit (cong (·₀ 0G 1) (emloop g)) i) i)
                                ∙∙ sym (∙assoc _ _ _)))
       λ n f → trElim (λ _ → isOfHLevelTruncPath)
                       λ { north → refl
                         ; south → refl
                         ; (merid a i) j → (cong (EM→ΩEM+1 (suc n)) (f (EM-raw→EM _ _ a))
                                           ∙ EM→ΩEM+1-0ₖ _) j i}

   0·₀' : (m : ℕ) (g : _) → ·₀' 0H m g ≡ 0ₖ m
   0·₀' =
     elim+2
       ⊗AnnihilR
       (elimSet _ (λ _ → emsquash _ _)
         refl
         λ g → compPathR→PathP (sym (∙assoc _ _ _
                              ∙∙ sym (rUnit _) ∙ sym (rUnit _)
                              ∙∙ (cong emloop (⊗AnnihilR g)
                                ∙ emloop-1g _))))
       λ n f → trElim (λ _ → isOfHLevelTruncPath)
                       λ { north → refl
                         ; south → refl
                         ; (merid a i) j → (cong (EM→ΩEM+1 (suc n)) (f (EM-raw→EM _ _ a))
                                           ∙ EM→ΩEM+1-0ₖ _) j i}


-- Definition of the cup product
   cup∙ : ∀ n m → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cup∙ =
     ℕelim
       (λ m g → (·₀ g m) , ·₀0 m g)
         λ n f →
           ℕelim
             (λ g → (λ h → ·₀' h (suc n) g) , 0·₀' (suc n) g)
             λ m _ → main n m f

     where
     main : (n m : ℕ) (ind : ((m : ℕ) → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)))
         → EM G' (suc n) →  EM∙ H' (suc m) →∙ EM∙ (G' ⨂ H') (suc (suc (n + m)))
     main zero m ind =
       elimGroupoid _ (λ _ → isOfHLevel↑∙ _ _)
         ((λ _ → 0ₖ (2 + m)) , refl)
         (f m)
         λ n h → finalpp m n h
       where
       f : (m : ℕ) → G → typ (Ω (EM∙ H' (suc m) →∙ EM∙ (G' ⨂ H') (suc (suc m)) ∙))
       fst (f m g i) x = EM→ΩEM+1 _ (·₀ g _ x) i
       snd (f zero g i) j = EM→ΩEM+1-0ₖ (suc zero) j i
       snd (f (suc m) g i) j = EM→ΩEM+1-0ₖ (suc (suc m)) j i

       f-hom-fst : (m : ℕ) (g h : G) → cong fst (f m (g +G h)) ≡ cong fst (f m g ∙ f m h)
       f-hom-fst m g h =
            (λ i j x → EM→ΩEM+1 _ (·₀-distr g h (suc m) x i) j)
         ∙∙ (λ i j x → EM→ΩEM+1-hom _ (·₀ g (suc m) x) (·₀ h (suc m) x) i j)
         ∙∙ sym (cong-∙ fst (f m g) (f m h))

       f-hom : (m : ℕ) (g h : G) → f m (g +G h) ≡ f m g ∙ f m h
       f-hom m g h = →∙Homogeneous≡Path (isHomogeneousEM _) _ _ (f-hom-fst m g h)

       finalpp : (m : ℕ) (g h : G) → PathP (λ i → f m g i ≡ f m (g +G h) i) refl (f m h)
       finalpp m g h =
         compPathR→PathP (sym (rCancel _)
                       ∙∙ cong (_∙ sym (f m (g +G h))) (f-hom m g h)
                       ∙∙ sym (∙assoc _ _ _))

     main (suc n) m ind =
       trElim (λ _ → isOfHLevel↑∙ (2 + n) m)
         λ { north → (λ _ → 0ₖ (3 + (n + m))) , refl
           ; south → (λ _ → 0ₖ (3 + (n + m))) , refl
           ; (merid a i) → Iso.inv (ΩfunExtIso _ _)
                             (EM→ΩEM+1∙ _ ∘∙ ind (suc m) (EM-raw→EM _ _ a)) i}

   _⌣ₖ_ : {n m : ℕ} (x : EM G' n) (y : EM H' m) → EM (G' ⨂ H') (n +' m)
   _⌣ₖ_ x y = cup∙ _ _ x .fst y

   ⌣ₖ-0ₖ : (n m : ℕ) (x : EM G' n) → (x ⌣ₖ 0ₖ m) ≡ 0ₖ (n +' m)
   ⌣ₖ-0ₖ n m x = cup∙ n m x .snd

   0ₖ-⌣ₖ : (n m : ℕ) (x : EM H' m) → ((0ₖ n) ⌣ₖ x) ≡ 0ₖ (n +' m)
   0ₖ-⌣ₖ zero m = 0·₀ _
   0ₖ-⌣ₖ (suc zero) zero x = refl
   0ₖ-⌣ₖ (suc (suc n)) zero x = refl
   0ₖ-⌣ₖ (suc zero) (suc m) x = refl
   0ₖ-⌣ₖ (suc (suc n)) (suc m) x = refl

module LeftDistributivity {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
   private
     distrl1 : (n m : ℕ) → EM H' m → EM H' m
             → EM∙ G' n →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrl1 n m x y) z = z ⌣ₖ (x +ₖ y)
     snd (distrl1 n m x y) = 0ₖ-⌣ₖ n m _

     distrl2 : (n m : ℕ) → EM H' m → EM H' m
             → EM∙ G' n →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrl2 n m x y) z = (z ⌣ₖ x) +ₖ (z ⌣ₖ y)
     snd (distrl2 n m x y) =
       cong₂ _+ₖ_ (0ₖ-⌣ₖ n m x) (0ₖ-⌣ₖ n m y) ∙ rUnitₖ _ (0ₖ (n +' m))

   hLevLem : (n m : ℕ) → isOfHLevel (suc (suc m)) (EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H') ((suc n) +' m))
   hLevLem n m =
     subst (isOfHLevel (suc (suc m)))
           (λ i → EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H')
           ((cong suc (+-comm m n) ∙ sym (+'≡+ (suc n) m)) i)) (isOfHLevel↑∙ m n)

   mainDistrL : (n m : ℕ) (x y : EM H' (suc m))
     → distrl1 (suc n) (suc m) x y ≡ distrl2 (suc n) (suc m) x y
   mainDistrL n zero =
     wedgeConEM.fun H' H' 0 0
       (λ _ _ → hLevLem _ _ _ _)
       (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ z → l x z))
       (λ y → →∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ z → r y z ))
       λ i → →∙Homogeneous≡ (isHomogeneousEM (suc (suc (n + 0))))
                               (funExt (λ z → l≡r z i))
     where
     l : (x : EM H' 1) (z : _)
       → (distrl1 (suc n) 1 embase x .fst z) ≡ (distrl2 (suc n) 1 embase x .fst z)
     l x z = cong (z ⌣ₖ_) (lUnitₖ _ x)
            ∙∙ sym (lUnitₖ _ (z ⌣ₖ x))
            ∙∙ λ i → (⌣ₖ-0ₖ (suc n) (suc zero) z (~ i)) +ₖ (z ⌣ₖ x)

     r : (z : EM H' 1) (x : EM G' (suc n))
       → (distrl1 (suc n) 1 z embase .fst x) ≡ (distrl2 (suc n) 1 z embase .fst x)
     r y z = cong (z ⌣ₖ_) (rUnitₖ _ y)
            ∙∙ sym (rUnitₖ _ (z ⌣ₖ y))
            ∙∙ λ i → (z ⌣ₖ y) +ₖ (⌣ₖ-0ₖ (suc n) (suc zero) z (~ i))

     l≡r : (z : EM G' (suc n)) → l embase z ≡ r embase z
     l≡r z = sym (pathTypeMake _ _ (sym (⌣ₖ-0ₖ (suc n) (suc zero) z)))

   mainDistrL n (suc m) =
     elim2 (λ _ _ → isOfHLevelPath (4 + m) (hLevLem _ _) _ _)
           (wedgeConEM.fun H' H' (suc m) (suc m)
             (λ x y p q → isOfHLevelPlus {n = suc (suc m)} (suc m)
                             (hLevLem n (suc (suc m))
                               (distrl1 (suc n) (suc (suc m)) ∣ x ∣ ∣ y ∣)
                               (distrl2 (suc n) (suc (suc m)) ∣ x ∣ ∣ y ∣) p q))
             (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
               (funExt (l x)))
             (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
               (funExt (r x)))
             λ i → →∙Homogeneous≡ (isHomogeneousEM _)
                     (funExt (λ z → l≡r z i)))
    where
    l : (x : EM-raw H' (suc (suc m))) (z : EM G' (suc n))
     → (distrl1 (suc n) (suc (suc m)) (0ₖ _) ∣ x ∣ₕ .fst z)
      ≡ (distrl2 (suc n) (suc (suc m)) (0ₖ _) ∣ x ∣ₕ .fst z)
    l x z = cong (z ⌣ₖ_) (lUnitₖ (suc (suc m)) ∣ x ∣)
         ∙∙ sym (lUnitₖ _ (z ⌣ₖ ∣ x ∣))
         ∙∙ λ i → (⌣ₖ-0ₖ (suc n) (suc (suc m)) z (~ i)) +ₖ (z ⌣ₖ ∣ x ∣)

    r : (x : EM-raw H' (suc (suc m))) (z : EM G' (suc n))
      → (distrl1 (suc n) (suc (suc m)) ∣ x ∣ₕ (0ₖ _) .fst z)
       ≡ (distrl2 (suc n) (suc (suc m)) ∣ x ∣ₕ (0ₖ _) .fst z)
    r x z = cong (z ⌣ₖ_) (rUnitₖ (suc (suc m)) ∣ x ∣)
         ∙∙ sym (rUnitₖ _ (z ⌣ₖ ∣ x ∣))
         ∙∙ λ i → (z ⌣ₖ ∣ x ∣) +ₖ (⌣ₖ-0ₖ (suc n) (suc (suc m)) z (~ i))

    l≡r : (z : EM G' (suc n)) → l north z ≡ r north z
    l≡r z = sym (pathTypeMake _ _ (sym (⌣ₖ-0ₖ (suc n) (suc (suc m)) z)))

module RightDistributivity {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
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


     distrr1 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrr1 n m x y) z = (x +ₖ y) ⌣ₖ z
     snd (distrr1 n m x y) = ⌣ₖ-0ₖ n m _

     distrr2 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrr2 n m x y) z = (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
     snd (distrr2 n m x y) = cong₂ _+ₖ_ (⌣ₖ-0ₖ n m x) (⌣ₖ-0ₖ n m y) ∙ rUnitₖ _ (0ₖ (n +' m))

   mainDistrR : (n m : ℕ) (x y : EM G' (suc n))
     → distrr1 (suc n) (suc m) x y ≡ distrr2 (suc n) (suc m) x y
   mainDistrR zero m =
     wedgeConEM.fun G' G' 0 0
       (λ _ _ → isOfHLevel↑∙ 1 m _ _)
       (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt (l x)))
       (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt (r x)))
       λ i → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt λ z → l≡r z i)
     where
     l : (x : _) (z : _) → _ ≡ _
     l x z =
          (λ i → (lUnitₖ 1 x i) ⌣ₖ z)
       ∙∙ sym (lUnitₖ _ (x ⌣ₖ z))
       ∙∙ λ i → 0ₖ-⌣ₖ _ _ z (~ i) +ₖ (x ⌣ₖ z)

     r : (x : _) (z : _) → _ ≡ _
     r x z =
          ((λ i → (rUnitₖ 1 x i) ⌣ₖ z))
       ∙∙ sym (rUnitₖ _ _)
       ∙∙ λ i → (_⌣ₖ_ {n = 1} {m = suc m} x z) +ₖ 0ₖ-⌣ₖ (suc zero) (suc m) z (~ i)

     l≡r : (z : _) → l embase z ≡ r embase z
     l≡r z = pathTypeMake _ _ _

   mainDistrR (suc n) m =
     elim2 (λ _ _ → isOfHLevelPath (4 + n)
                      (isOfHLevel↑∙ (2 + n) m) _ _)
           (wedgeConEM.fun _ _ _ _
             (λ x y → isOfHLevelPath ((2 + n) + (2 + n))
                       (transport (λ i → isOfHLevel (((λ i → (+-comm n 2 (~ i) + (2 + n)))
                                                         ∙ sym (+-assoc n 2 (2 + n))) (~ i))
                                  (EM∙ H' (suc m) →∙ EM∙ ((fst (AbGroupPath (G' ⨂ H') (H' ⨂ G'))) ⨂-comm (~ i))
                                  ((+'-comm (suc m) (suc (suc n))) i)))
                                  (isOfHLevelPlus n
                                    (LeftDistributivity.hLevLem m (suc (suc n))))) _ _)
             (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt (l x)))
             (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt (r x)))
             λ i → →∙Homogeneous≡ (isHomogeneousEM _)
                        (funExt λ z → r≡l z i))
     where
     l : (x : _) (z : _) → _ ≡ _
     l x z = (λ i → (lUnitₖ _ ∣ x ∣ i) ⌣ₖ z)
        ∙∙ sym (lUnitₖ _ (∣ x ∣ ⌣ₖ z))
        ∙∙ λ i → 0ₖ-⌣ₖ _ _ z (~ i) +ₖ (∣ x ∣ ⌣ₖ z)

     r : (x : _) (z : _) → _ ≡ _
     r x z = (λ i → (rUnitₖ _ ∣ x ∣ i) ⌣ₖ z)
           ∙∙ sym (rUnitₖ _ (∣ x ∣ ⌣ₖ z))
           ∙∙ λ i → (∣ x ∣ ⌣ₖ z) +ₖ 0ₖ-⌣ₖ _ _ z (~ i)

     r≡l : (z : _) → l north z ≡ r north z
     r≡l z = pathTypeMake _ _ _

-- TODO: Summarise distributivity proofs
-- TODO: Associativity and graded commutativity, following Cubical.ZCohomology.RingStructure
-- The following lemmas will be needed to make the types match up.
