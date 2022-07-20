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
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Functions.Morphism

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1 renaming (rec to EMrec ; elim to EM₁elim)
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

+'-suc : (n m : ℕ) → suc (n +' m) ≡ suc n +' m
+'-suc zero zero = refl
+'-suc zero (suc m) = refl
+'-suc (suc n) zero = refl
+'-suc (suc n) (suc m) = refl

-- Lemma for distributativity of cup product (used later)
pathType : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → Type ℓ
pathType n x p = sym (rUnitₖ (2 + n) x) ∙ (λ i → x +ₖ p i)
               ≡ sym (lUnitₖ (2 + n) x) ∙ λ i → p i +ₖ x

pathTypeMake : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x)
    → pathType n x p
pathTypeMake n x = J (λ x p → pathType n x p) refl

EM₁→fun∙≡ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} (G' : Group ℓ'') {F G : EM₁ G' → A →∙ B} (h : isHomogeneous B)
          → ((x : _) → isSet (F x ≡ G x))
          → (p : (a : typ A) → F embase .fst a ≡ G embase .fst a)
          → ((g : _) (a : typ A) → PathP (λ i → p a i ≡ p a i)
                (cong (λ x → F x .fst a) (emloop g)) (cong (λ x → G x .fst a) (emloop g)))
          → (x : _) → F x ≡ G x
EM₁→fun∙≡ G' {F = F} {G = G} h isset p pp x = Trunc.rec (isset x) (λ id → →∙Homogeneous≡ h (funExt id)) (lem' x)
  where
  lem' : (x : _) → hLevelTrunc 2 ((a : _) → F x .fst a ≡ G x .fst a)
  lem' = elimSet _ (λ _ → isOfHLevelTrunc 2) ∣ p ∣
                   λ g i → ∣ (λ a → flipSquare (pp g a) i) ∣ₕ

EM₁→fun∙≡' : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
                 (G' : Group ℓ''') {F G : EM₁ G' → A →∙ (B →∙ C ∙)} (h : isHomogeneous C)
  → ((x : _) → isSet (F x ≡ G x))
  → (p : ((a : typ A) (b : typ B) → F embase .fst a .fst b ≡ G embase .fst a .fst b))
  → ((g : _) (a : typ A) (b : typ B) → PathP (λ i → p a b i ≡ p a b i)
              (cong (λ x → F x .fst a .fst b) (emloop g))
              (cong (λ x → G x .fst a .fst b) (emloop g)))
  → (x : _) → F x ≡ G x
EM₁→fun∙≡' G' {F = F} {G = G} h s p pp x =
  Trunc.rec (s x)
    (λ id → →∙Homogeneous≡ (isHomogeneous→∙ h) (funExt λ b → →∙Homogeneous≡ h (id b))) (help x)
  where
  open import Cubical.Data.Sigma
  help : (x : _) → hLevelTrunc 2 ((a : _) → F x .fst a .fst ≡ G x .fst a .fst)
  help = elimSet _ (λ _ → isOfHLevelTrunc 2)
          ∣ (λ a → funExt (p a)) ∣ₕ λ g i → ∣ (λ a j b → pp g a b j i) ∣ₕ

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
{-
   cup∙' : ∀ n m → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cup∙' zero m = {!!}
   cup∙' (suc zero) m = {!!}
   cup∙' (suc (suc n)) m =
     Trunc.elim {!!}
       λ { north → (λ y → 0ₖ ((2 + n) +' m)) , refl
         ; south → (λ y → 0ₖ ((2 + n) +' m)) , refl
         ; (merid a i) → (λ y → {!EM→ΩEM+1 (suc n +' m) (cup∙' (suc n) m (EM-raw→EM _ (suc n) a) .fst y) i!}) , {!!}}
-}

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

   EM→ΩEM-⌣ₗ' : (n m : ℕ) (x : EM G' (suc n))
     → EM∙ H' (suc m) →∙ Ω (EM∙ (G' ⨂ H') (suc (suc (suc (n + m)))))
   fst (EM→ΩEM-⌣ₗ' n m x) y = EM→ΩEM+1 (suc n +' (suc m)) (x ⌣ₖ y)
   snd (EM→ΩEM-⌣ₗ' n m x) = cong (EM→ΩEM+1 (suc n +' (suc m))) (⌣ₖ-0ₖ (suc n) (suc m) x)
                              ∙ EM→ΩEM+1-0ₖ _

   EM→ΩEM-⌣ᵣ' : (n m : ℕ) (x : EM G' (suc n))
     → EM∙ H' (suc m) →∙ Ω (EM∙ (G' ⨂ H') (suc (suc (suc (n + m)))))
   fst (EM→ΩEM-⌣ᵣ' n m x) y = cong (λ x → _⌣ₖ_ {n = suc (suc n)} {m = suc m} x y) (EM→ΩEM+1 (suc n) x)
   snd (EM→ΩEM-⌣ᵣ' n m x) j i = ⌣ₖ-0ₖ (2 + n) (suc m) (EM→ΩEM+1 (suc n) x i) j

   EM→ΩEM-⌣ₗᵣ₀₂ : (m : ℕ) (x : G) (y : EM H' (suc m))
                     → EM→ΩEM+1 (suc m) (_⌣ₖ_ {n = 0} x y)
                     ≡ cong (_⌣ₖ_ {n = 0} {m = (2 + m)} x) (EM→ΩEM+1 (suc m) y)
   EM→ΩEM-⌣ₗᵣ₀₂ zero x y =
       rUnit (EM→ΩEM+1 1 (_⌣ₖ_ {n = 0} {m = 1} x y))
      ∙ (λ i → EM→ΩEM+1 1 (_⌣ₖ_ {n = 0} {m = 1} x y) ∙ sym (EM→ΩEM+1-0ₖ 1 (~ i)))
     ∙ sym (cong-∙ (_⌣ₖ_ {n = 0} {m = 2} x) (cong ∣_∣ₕ (merid y)) (sym (cong ∣_∣ₕ (merid embase))))
                         ∙ sym (cong (cong (_⌣ₖ_ {n = 0} {m = 2} x)) (cong-∙ ∣_∣ₕ (merid y) (sym (merid embase))))
   EM→ΩEM-⌣ₗᵣ₀₂ (suc n) x =
     Trunc.elim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
                λ a → (rUnit _
                    ∙ cong (EM→ΩEM+1 (suc (suc n)) (_⌣ₖ_ {n = 0} {m = 2 + n} x ∣ a ∣) ∙_)
                           (sym (cong sym (cong (EM→ΩEM+1 (suc (suc n))) (⌣ₖ-0ₖ 0 _ x))
                           ∙ cong sym (EM→ΩEM+1-0ₖ (2 + n)))))
                    ∙∙ sym (cong-∙ (_⌣ₖ_ {n = 0} {m = suc (suc (suc n))} x)
                           (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (sym (merid north))))
                    ∙∙ cong (cong (_⌣ₖ_ {n = 0} {m = suc (suc (suc n))} x))
                            (sym (cong-∙ ∣_∣ₕ  (merid a) (sym (merid north))))


   EM→ΩEM-⌣ₗ : (n m : ℕ) (x : EM-raw G' (suc n))
     → EM∙ H' (suc m) →∙ Ω (EM∙ (G' ⨂ H') (suc (suc (suc (n + m)))))
   fst (EM→ΩEM-⌣ₗ n m x) y = EM→ΩEM+1 (suc n +' (suc m)) ((EM-raw→EM G' (suc n) x) ⌣ₖ y)
   snd (EM→ΩEM-⌣ₗ n m x) = cong (EM→ΩEM+1 (suc n +' (suc m))) (⌣ₖ-0ₖ (suc n) (suc m) (EM-raw→EM G' (suc n) x))
                              ∙ EM→ΩEM+1-0ₖ _

   EM→ΩEM-⌣ᵣ : (n m : ℕ) (x : EM-raw G' (suc n))
     → EM∙ H' (suc m) →∙ Ω (EM∙ (G' ⨂ H') (suc (suc (suc (n + m)))))
   fst (EM→ΩEM-⌣ᵣ n m x) y = cong (λ x → _⌣ₖ_ {n = suc (suc n)} {m = suc m} x y) (EM→ΩEM+1 (suc n) (EM-raw→EM G' (suc n) x))
   snd (EM→ΩEM-⌣ᵣ n m x) j i = ⌣ₖ-0ₖ (2 + n) (suc m) (EM→ΩEM+1 (suc n) (EM-raw→EM G' (suc n) x) i) j

   open import Cubical.Data.Sigma

   EM→ΩEM+1-⌣' : (n m : ℕ) (x : EM G' (suc n))
     → EM→ΩEM-⌣ₗ' n m x ≡ EM→ΩEM-⌣ᵣ' n m x
   EM→ΩEM+1-⌣' = {!!}

   EM→ΩEM+1-⌣ : (n m : ℕ) (x : EM-raw G' (suc n))
     → EM→ΩEM-⌣ₗ n m x ≡ EM→ΩEM-⌣ᵣ n m x
   EM→ΩEM+1-⌣ zero m =
     elimSet (AbGroup→Group G')
       {!!}
       (ΣPathP (funExt (λ y → EM→ΩEM+1-0ₖ (suc (suc m)) ∙ λ j i → _⌣ₖ_ {n = 2} {m = suc m} (EM→ΩEM+1-0ₖ 1 (~ j) i) y)
                     , {!!}))
       λ g → →∙HomogeneousSquare (isHomogeneousPath _ _) _ _ _ _
         {!raw-elim G'!} -- raw-elim G' 0 {!!} {!!}
   EM→ΩEM+1-⌣ (suc n) m x = →∙Homogeneous≡ (isHomogeneousPath _ _)
     (funExt λ y → rUnit (λ i → _⌣ₖ_ {n = 3 + n} {m = suc m} ∣ merid x i ∣ₕ y)
                  ∙ (λ j → (λ i → _⌣ₖ_ {n = 3 + n} {m = suc m} ∣ merid x i ∣ₕ y) ∙ sym (h (suc n) y (~ j)))
                  ∙ sym (cong-∙ (λ x → _⌣ₖ_ {n = 3 + n} {m = suc m} ∣ x ∣ₕ y) (merid x) (sym (merid north))))
     where
     ll : (n : ℕ) → EM-raw→EM G' (suc n) (EM-raw∙ G' (suc n) .snd) ≡ 0ₖ (suc n)
     ll zero = refl
     ll (suc n) = refl

     h : (n : ℕ) → (y : EM H' (suc m)) → cong (λ x → _⌣ₖ_ {n = 2 + n} {m = suc m} ∣ x ∣ₕ y) (merid (EM-raw∙ G' (suc n) .snd)) ≡ λ _ → ∣ north ∣ₕ
     h n y = cong (EM→ΩEM+1 (suc n +' suc m)) ((λ i → _⌣ₖ_ {n = suc n} {m = suc m} (ll n i) y)
                                           ∙ 0ₖ-⌣ₖ (suc n) (suc m) y)
         ∙ EM→ΩEM+1-0ₖ (suc (suc (n + m)))
{-
   cup∙' : ∀ n m → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cup∙' =
     ℕelim (cup∙ zero)
           (ℕelim (λ _ → cup∙ 1)
                  λ n _ ind m
                → Trunc.rec {!!}
                             λ { north → (λ _ → 0ₖ (suc (suc n) +' m)) , refl
                               ; south → (λ _ → 0ₖ (suc (suc n) +' m)) , refl
                               ; (merid a i) → (λ y → subst (λ x → 0ₖ x ≡ 0ₖ x) (+'-suc (suc n) m)
                                                         (EM→ΩEM+1 (suc n +' m) (ind m (EM-raw→EM _ (suc n) a) .fst y)) i)
                                , λ j → (cong (subst (λ x → 0ₖ x ≡ 0ₖ x) (+'-suc (suc n) m)) ((cong (EM→ΩEM+1 (suc n +' m))
                                     (ind m (EM-raw→EM G' (suc n) a) .snd)) ∙ EM→ΩEM+1-0ₖ (suc n +' m))
                                    ∙ substReflℕ 0ₖ (+'-suc (suc n) m)) j i})
     where
     substReflℕ : ∀ {ℓ'} {B : (n : ℕ) → Type ℓ'} (p : (x : ℕ) → B x) {n m : ℕ} (q : n ≡ m)
                → subst (λ x → p x ≡ p x) q refl ≡ refl
     substReflℕ p {n = n} = J (λ m q → subst (λ x → p x ≡ p x) q refl ≡ refl) (transportRefl refl)
   cup≡ : (n m : ℕ) (x : EM G' n) → cup∙ n m x ≡ cup∙' n m x
   cup≡ zero m x = refl
   cup≡ (suc zero) m x = refl
   cup≡ (suc (suc n)) zero =
     Trunc.elim {!!}
                λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                (funExt λ y → help (λ a → cup≡ (suc n) zero (EM-raw→EM G' (suc n) a)) y x)
     where
     help : (cup≡ : (a : _) → cup∙ (suc n) zero (EM-raw→EM G' (suc n) a)
                             ≡ cup∙' (suc n) zero (EM-raw→EM G' (suc n) a))
       (y : fst H') (x : EM-raw G' (suc (suc n))) → (cup∙ (suc (suc n)) zero ∣ x ∣ₕ .fst y) ≡ cup∙' (suc (suc n)) zero ∣ x ∣ .fst y
     help cup≡ y north = refl
     help cup≡ y south = refl
     help cup≡ y (merid a i) = flipSquare help2 i
       where
       help2 : cong (λ x → cup∙ (suc (suc n)) zero ∣ x ∣ₕ .fst y) (merid a) ≡ cong (λ x → cup∙' (suc (suc n)) zero ∣ x ∣ₕ .fst y) (merid a)
       help2 i = transportRefl (EM→ΩEM+1 (suc n) (fst (cup≡ a i) y)) (~ i)
   cup≡ (suc (suc n)) (suc m) =
     Trunc.elim {!!}
                λ a → →∙Homogeneous≡ (isHomogeneousEM _)
                  (funExt λ y → help m (λ x → cup≡ (suc n) (suc m) _) y a)
     where
     help : (m : ℕ) (cup≡ : (a : _) → cup∙ (suc n) (suc m) (EM-raw→EM G' (suc n) a)
                             ≡ cup∙' (suc n) (suc m) (EM-raw→EM G' (suc n) a))
       (y : EM H' (suc m)) (x : EM-raw G' (suc (suc n))) → (cup∙ (suc (suc n)) (suc m) ∣ x ∣ₕ .fst y) ≡ cup∙' (suc (suc n)) (suc m) ∣ x ∣ .fst y
     help m cup≡ y north = refl
     help m cup≡ y south = refl
     help m cup≡ y (merid a i) = flipSquare l i
       where
       l : cong (λ x → cup∙ (suc (suc n)) (suc m) ∣ x ∣ₕ .fst y) (merid a) ≡ cong (λ x → cup∙' (suc (suc n)) (suc m) ∣ x ∣ₕ .fst y) (merid a)
       l i = transportRefl (EM→ΩEM+1 (suc n +' (suc m)) (fst (cup≡ a i) y)) (~ i)
-}

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

EMEqFunct : (n : ℕ) {G H : AbGroup ℓ} (e : AbGroupEquiv G H) (x : EM G (suc n))
  →  (cong ((Iso.fun (Iso→EMIso e (suc (suc n))))))
    (EM→ΩEM+1 (suc n) x)
   ≡ EM→ΩEM+1 (suc n) (Iso.fun (Iso→EMIso e (suc n)) x)
EMEqFunct zero e x =
  cong ((cong ((Iso.fun (Iso→EMIso e 2))))) (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase)))
  ∙ cong-∙ (Iso.fun (Iso→EMIso e 2))
           (cong ∣_∣ₕ (merid x))
           (cong ∣_∣ₕ (sym (merid embase)))
  ∙ (λ i → cong ∣_∣ₕ (merid (Iso.fun (Iso→EMIso e 1) x)) ∙ cong ∣_∣ₕ (sym (merid embase)))
  ∙ sym (cong-∙ ∣_∣ₕ (merid (Iso.fun (Iso→EMIso e (suc zero)) x)) (sym (merid embase)))
EMEqFunct (suc n) e =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
    λ a → cong ((cong ((Iso.fun (Iso→EMIso e (3 + n)))))) (cong-∙ ∣_∣ₕ (merid a)
               (sym (merid north)))
        ∙∙ cong-∙ (Iso.fun (Iso→EMIso e (3 + n)))
             (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (sym (merid north)))
        ∙∙  ((λ i → cong ∣_∣ₕ (merid (inducedFun-EM-raw (fst e .fst , snd e) (suc (suc n)) a))
                  ∙ cong ∣_∣ₕ (sym (merid north)))
         ∙ sym (cong-∙ ∣_∣ₕ (merid ((inducedFun-EM-raw (fst e .fst , snd e) (suc (suc n))) a)) (sym (merid north))))

module _ {ℓ ℓ' ℓ'' ℓ''' : Level} {G' : AbGroup ℓ} {H' : AbGroup ℓ'} {L' : AbGroup ℓ''} {K' : AbGroup ℓ'''} where
   private
     G = fst G'
     H = fst H'
     L = fst L'

     strG = snd G'
     strH = snd H'
     strL = snd L'

     0G = 0g strG
     0H = 0g strH
     0L = 0g strL

     _+G_ = _+Gr_ strG
     _+H_ = _+Gr_ strH
     _+L_ = _+Gr_ strL

     -H_ = -Gr_ strH
     -G_ = -Gr_ strG
     -L_ = -Gr_ strL

     open import Cubical.Data.Sigma
   assocInd : (n m l : ℕ) (f g : (EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ K' ((n +' m) +' l) ∙) ∙)))
            → ((x : EM' G' n) (y : EM' H' m) (z : EM' L' l)
             → fst f (EM'→EM _ n x) .fst (EM'→EM _ m y) .fst (EM'→EM _ l z)
              ≡ fst g (EM'→EM _ n x) .fst (EM'→EM _ m y) .fst (EM'→EM _ l z))
            → f ≡ g
   assocInd zero zero l f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt (λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt (EM'-elim _ _ (λ x → isOfHLevelPath' (suc l) (hLevelEM _ l) _ _)
             λ z → ind x y z)))))
   assocInd zero (suc m) zero f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt λ y → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt (EM'-elim _ _
           (λ _ → isOfHLevelPath' (suc (suc m))
                    (isOfHLevelΣ (suc (suc (suc m)))
                    (isOfHLevelΠ (suc (suc (suc m)))
                      (λ _ → hLevelEM _ (suc m)))
                    λ _ → isOfHLevelPath (suc (suc (suc m)))
                    (hLevelEM _ (suc m)) _ _) _ _)
           λ z → →∙Homogeneous≡ (isHomogeneousEM _)
                    (funExt (ind y z)))))
   assocInd zero (suc m) (suc l) f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt (EM'-elim _ _
           (λ _ → isOfHLevelPath' (suc (suc m))
             (isOfHLevel↑∙ {G = L'} {H = K'} (suc m) l) _ _)
             λ y → →∙Homogeneous≡ (isHomogeneousEM _)
               (funExt λ z → funExt⁻ (cong fst (helpid x z)) y))))
     where
     help : (EM∙ G' zero →∙ (EM∙ H' (suc m) →∙ EM∙ L' (suc l)
         →∙ EM∙ K' ((zero +' suc m) +' suc l) ∙ ∙))
       → (x : fst G') → EM L' (suc l) → EM'∙ H' (suc m) →∙ EM∙ K' ((suc m) +' suc l)
     fst (help f x y) z = fst f x .fst (EM'→EM _ _ z) .fst y
     snd (help f x y) = (λ i → fst f x .fst (EM'→EM∙ _ _ i) .fst y) ∙ funExt⁻ (cong fst (fst f x .snd)) y

     helpid :  (x : fst G') → (y : EM L' (suc l)) → help f x y ≡ help g x y
     helpid x =
       EM'-elim _ _
         (λ x → isOfHLevelPath' (suc (suc l))
                 (subst (λ x → isOfHLevel (suc (suc (suc l))) (EM'∙ H' (suc m) →∙ EM∙ K' x))
                   (cong suc (+-suc l m) ∙ cong (2 +_) (+-comm l m))
                   (isOfHLevel↑-raw {G = H'} {H = K'} (suc l) (suc m))) _ _)
         λ y → →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ z → ind x z y)

   assocInd (suc n) zero zero f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ z → main y z x)))
     where
     main : (x : H) (y : L) (z : _) → f .fst z .fst x .fst y ≡ g .fst z .fst x .fst y
     main x y = EM'-elim _ _ (λ _ → hLevelEM _ (suc n) _ _) λ _ → ind _ _ _

   assocInd (suc n) zero (suc l) f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (cong fst (lem₁ y x))))
     where
     help : EM∙ G' (suc n) →∙ (EM∙ H' zero →∙ EM∙ L' (suc l) →∙ EM∙ K' (suc (suc (n + l))) ∙ ∙)
         → (y : H) (x : EM G' (suc n)) → EM∙ L' (suc l) →∙ EM∙ K' (suc (suc (n + l)))
     fst (help f y x) z = fst f x .fst y .fst z
     snd (help f y x) = fst f x .fst y .snd

     help2 : EM∙ G' (suc n) →∙ (EM∙ H' zero →∙ EM∙ L' (suc l) →∙ EM∙ K' (suc (suc (n + l))) ∙ ∙)
           → (y : H) (x : EM L' (suc l)) → EM'∙ G' (suc n) →∙ EM∙ K' (suc (suc (n + l)))
     fst (help2 f y x) z = fst f (EM'→EM _ _ z) .fst y .fst x
     snd (help2 f y x) = (λ i → fst f (EM'→EM∙ G' (suc n) i) .fst y .fst x)
                       ∙ λ i → snd f i .fst y .fst x

     lem₂ : (y : H) (x : EM L' (suc l)) → help2 f y x ≡ help2 g y x
     lem₂ y =
       EM'-elim _ _ (λ _ → isOfHLevelPath' (suc (suc l))
                    (subst (λ x → isOfHLevel (2 + suc l) (EM'∙ G' (suc n) →∙ EM∙ K' x))
                            (cong suc (+-comm l (suc n)))
                            (isOfHLevel↑-raw {G = G'} {H = K' } (suc l) (suc n)) ) _ _)
         λ _ → →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ _ → ind _ _ _)

     lem₁ : (y : H) (x : EM G' (suc n)) → help f y x ≡ help g y x
     lem₁ y =
       EM'-elim _ _ (λ _ → isOfHLevelPath' (suc (suc n))
                    (isOfHLevel↑∙ {G = L'} {H = K' } (suc n) l) _ _)
         λ x → →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ z → funExt⁻ (cong fst (lem₂ y z)) x) 
   assocInd (suc n) (suc m) zero f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt (λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt (λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt (λ z → funExt⁻ (cong fst (funExt⁻ (cong fst (lem z)) x)) y))))))
     where
     F : (EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ EM∙ L' zero →∙ EM∙ K' (suc (suc (n + m))) ∙ ∙))
       → L → (EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ EM∙ K' (suc (suc (n + m))) ∙))
     fst (fst (F f x) y) z = fst f y .fst z .fst x
     snd (fst (F f x) y) = λ i → fst f y .snd i .fst x
     snd (F f x) =
       →∙Homogeneous≡ (isHomogeneousEM _)
         (funExt λ z → λ i → snd f i .fst z .fst x)

     FF : (EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ EM∙ L' zero →∙ EM∙ K' (suc (suc (n + m))) ∙ ∙))
       → L → EM H' (suc m)
       → EM'∙ G' (suc n) →∙ EM∙ K' (suc (suc (n + m)))
     fst (FF f x y) z = fst f (EM'→EM _ _ z) .fst y .fst x
     snd (FF f x y) =
         (λ i → fst f (EM'→EM∙ G' (suc n) i) .fst y .fst x)
       ∙ λ i → snd f i .fst y .fst x

     FFid : (x : L) (y : _) → FF f x y ≡ FF g x y
     FFid x =
       EM'-elim _ _ (λ _ → isOfHLevelPath' (suc (suc m))
                      (subst (λ x → isOfHLevel (2 + suc m) (EM'∙ G' (suc n) →∙ EM∙ K' (suc x)))
                             (+-comm m (suc n))
                             (isOfHLevel↑-raw {G = G'} {H = K'} (suc m) (suc n))) _ _)
         λ z → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y → ind _ _ _)

     lem : (z : _ ) → F f z ≡ F g z
     lem z = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
             (funExt (EM'-elim _ _
               (λ _ → isOfHLevelPath' (suc (suc n))
                       (isOfHLevel↑∙ {G = H'} {H = K' } (suc n) m) _ _)
               λ x → →∙Homogeneous≡ (isHomogeneousEM _)
                 (funExt λ y → funExt⁻ (cong fst (FFid z y)) x)))

   assocInd (suc n) (suc m) (suc l) f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt (EM'-elim _ _ (λ _ → isOfHLevelPath' (2 + n) (isOfHLevel↑∙∙ m l (suc n)) _ _)
               λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ z → funExt⁻ (cong fst (funExt⁻ (cong fst (funExt⁻ (cong fst F₂id) y)) z)) _))))
     where
     F₂ : (f : (EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ (EM∙ L' (suc l)
            →∙ EM∙ K' (((suc n) +' (suc m)) +' (suc l)) ∙) ∙)))
       → EM∙ H' (suc m) →∙ (EM∙ L' (suc l) →∙ EM'∙ G' (suc n)
       →∙ EM∙ K' (suc (suc (suc (n + m + l)))) ∙ ∙)
     fst (fst (fst (F₂ f) x) y) z = fst f (EM'→EM _ _ z) .fst x .fst y
     snd (fst (fst (F₂ f) x) y) =
         (λ i → fst f (EM'→EM∙ G' (suc n) i) .fst x .fst y)
       ∙ funExt⁻ (cong fst (funExt⁻ (cong fst (snd f)) x)) y
     snd (fst (F₂ f) x) =
       →∙Homogeneous≡ (isHomogeneousEM _)
         (funExt λ y → fst f (EM'→EM G' (suc n) y) .fst x .snd)
     snd (F₂ f) = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
               (funExt λ z → →∙Homogeneous≡ (isHomogeneousEM _)
                 (funExt λ x → funExt⁻ (cong fst (fst f (EM'→EM G' (suc n) x) .snd)) z))

     F₃ : (f : (EM∙ G' (suc n) →∙ (EM∙ H' (suc m) →∙ (EM∙ L' (suc l)
            →∙ EM∙ K' (((suc n) +' (suc m)) +' (suc l)) ∙) ∙)))
        → EM L' (suc l) → EM'∙ H' (suc m) →∙ (EM'∙ G' (suc n)
        →∙ EM∙ K' (suc (suc (suc (n + m + l)))) ∙)
     fst (fst (F₃ f x) y) z = fst f (EM'→EM G' (suc n) z) .fst (EM'→EM H' (suc m) y) .fst x
     snd (fst (F₃ f x) y) = (λ i → fst f (EM'→EM∙ G' (suc n) i) .fst (EM'→EM H' (suc m) y) .fst x)
                          ∙ funExt⁻ (cong fst (funExt⁻ (cong fst (snd f)) _)) _
     snd (F₃ f x) =
         →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ z → (λ i → fst f (EM'→EM G' (suc n) z) .fst (EM'→EM∙ H' (suc m) i) .fst x)
                       ∙ funExt⁻ (cong fst (fst f (EM'→EM G' (suc n) z) .snd)) x)

     F₃id : F₃ f ≡ F₃ g
     F₃id = funExt
             (EM'-elim _ _ (λ _ → isOfHLevelPath' (suc (suc l))
                                  (subst2 (λ y x → isOfHLevel y
                                    ((EM'∙ H' (suc m) →∙ (EM'∙ G' (suc n) →∙ EM∙ K' x ∙))))
                                  refl
                                  (cong (λ x → suc (suc (suc x)))
                                      (cong (_+ n) (+-comm l m)
                                    ∙ sym (+-assoc m l n)
                                    ∙ cong (m +_) (+-comm l n)
                                    ∙ +-assoc m n l ∙
                                    cong (_+ l) (+-comm m n)))
                                  (isOfHLevel↑∙∙'' {G = H'} {H = G'} {L = K' } m n (suc l))) _ _)
               λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
                 (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
                   (funExt (λ z → ind z y x))))

     help : isOfHLevel (suc (2 + m)) (EM∙ L' (suc l) →∙ (EM'∙ G' (suc n) →∙ EM∙ K' (suc (suc (suc (n + m + l)))) ∙))
     help =
       subst2 (λ x y → isOfHLevel x (EM∙ L' (suc l) →∙ (EM'∙ G' (suc n) →∙ EM∙ K' y ∙)))
              refl
              (cong (λ x → suc (suc (suc x)))
                (+-comm (m + l) n ∙ +-assoc n m l))
              (isOfHLevel↑∙∙' {G = L'} {H = G'} {L = K' } l n (suc m))

     F₂id : F₂ f ≡ F₂ g
     F₂id = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
             (funExt (EM'-elim _ _ (λ _ → isOfHLevelPath' (2 + m)
                     help _ _)
                     λ y →
                       →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
                         (funExt λ z → →∙Homogeneous≡ (isHomogeneousEM _)
                           (cong fst (funExt⁻ (cong fst (funExt⁻ F₃id z)) y)))))

module Assoc {ℓ ℓ' ℓ'' : Level} {G' : AbGroup ℓ} {H' : AbGroup ℓ'} {L' : AbGroup ℓ''} where

   private
     G = fst G'
     H = fst H'
     L = fst L'

     strG = snd G'
     strH = snd H'
     strL = snd L'

     0G = 0g strG
     0H = 0g strH
     0L = 0g strL

     _+G_ = _+Gr_ strG
     _+H_ = _+Gr_ strH
     _+L_ = _+Gr_ strL

     -H_ = -Gr_ strH
     -G_ = -Gr_ strG
     -L_ = -Gr_ strL

     assL : (n m l : ℕ)
       → EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙) ∙)
     fst (fst (fst (assL n m l) x) y) z = (x ⌣ₖ y) ⌣ₖ z
     snd (fst (fst (assL n m l) x) y) = ⌣ₖ-0ₖ (n +' m) l (x ⌣ₖ y)
     snd (fst (assL n m l) x) =
       →∙Homogeneous≡ (isHomogeneousEM _)
         (funExt λ z → (λ i → (⌣ₖ-0ₖ n m x i) ⌣ₖ z) ∙ 0ₖ-⌣ₖ (n +' m) l z)
     snd (assL n m l) =
       →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt (λ z → ((λ i → (0ₖ-⌣ₖ n m y i) ⌣ₖ z)) ∙ 0ₖ-⌣ₖ (n +' m) l z)))

     substAssocLem : ∀ {ℓ} {G : AbGroup ℓ} {n m : ℕ} (p : n ≡ m) → subst (EM G) p (0ₖ n) ≡ 0ₖ m
     substAssocLem {G = G} {n = n} = J (λ m p → subst (EM G) p (0ₖ n) ≡ 0ₖ m) (transportRefl (0ₖ n))

     preSubstFun : {n m : ℕ} → n ≡ m → EM ((G' ⨂ H') ⨂ L') n → EM ((G' ⨂ H') ⨂ L') m
     preSubstFun {n = n} {m = m} p = subst (EM ((G' ⨂ H') ⨂ L')) p

     preSubstFunLoop : {n : ℕ} (p : n ≡ n) → (x : _) → preSubstFun p x ≡ x
     preSubstFunLoop p x = (λ i → preSubstFun (isSetℕ _ _ p refl i) x) ∙ transportRefl x

     substFun : (n m l : ℕ) → EM ((G' ⨂ H') ⨂ L') (n +' (m +' l)) → EM ((G' ⨂ H') ⨂ L') ((n +' m) +' l)
     substFun n m l = preSubstFun (+'-assoc n m l)

     swapFun : (n m l : ℕ) → EM (G' ⨂ (H' ⨂ L')) (n +' (m +' l)) → EM ((G' ⨂ H') ⨂ L') (n +' (m +' l))
     swapFun n m l = Iso.fun (Iso→EMIso ⨂assoc (n +' (m +' l)))

     assR : (n m l : ℕ)
       → EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙) ∙)
     fst (fst (fst (assR n m l) x) y) z =
       substFun n m l
         (swapFun n m l
           (x ⌣ₖ (y ⌣ₖ z)))
     snd (fst (fst (assR n m l) x) y) =
       cong (substFun n m l)
           (cong (swapFun n m l)
             (((λ i → x ⌣ₖ (⌣ₖ-0ₖ m l y i)) ∙ ⌣ₖ-0ₖ n (m +' l) x))
             ∙ Iso→EMIso∙ _ _)
         ∙ substAssocLem (+'-assoc n m l)
     snd (fst (assR n m l) x) =
       →∙Homogeneous≡ (isHomogeneousEM _)
         (funExt λ z → cong (substFun n m l) (cong (swapFun n m l)
                        ((λ i → x ⌣ₖ (0ₖ-⌣ₖ m l z i))
                      ∙ ⌣ₖ-0ₖ n (m +' l) x)
                      ∙ Iso→EMIso∙ _ _)
                      ∙ substAssocLem (+'-assoc n m l))
     snd (assR n m l) =
       →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
         (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt (λ z →
             cong (substFun n m l) (cong (swapFun n m l)
               (0ₖ-⌣ₖ n (m +' l) (y ⌣ₖ z))
           ∙ Iso→EMIso∙ _ _)
           ∙ substAssocLem (+'-assoc n m l))))

     EM→ΩEM+1-distr₀ₙ : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ)
                      → (x : fst G) (y : EM H (suc n))
                      → EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = G} {n = 0} {m = suc n} x y)
                       ≡ λ i → _⌣ₖ_ {G' = G} {n = 0} {m = suc (suc n)} x (EM→ΩEM+1 (suc n) y i)
     EM→ΩEM+1-distr₀ₙ = {!!}

     EM→ΩEM+1-distrₙ₀ : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ)
                      → (x : fst G) (y : EM H (suc n))
                      → EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = H} {H' = G} {n = suc n} {m = 0} y x)
                      ≡ λ i → _⌣ₖ_ {G' = H} {H' = G} {n = suc (suc n)} {m = 0} (EM→ΩEM+1 (suc n) y i) x
     EM→ΩEM+1-distrₙ₀ = {!!}

     assocConvert : {n m l : ℕ} → assL n m l ≡ assR n m l
       → (x : EM G' n) (y : EM H' m) (z : EM L' l)
       → cup∙ (n +' m) l (cup∙ n m x .fst y) .fst z
        ≡ substFun n m l (swapFun n m l (cup∙ n (m +' l) x .fst (cup∙ m l y .fst z)))
     assocConvert p x y z i = p i .fst x .fst y .fst z

     00-assoc : (l : ℕ) → assL zero zero l ≡ assR zero zero l
     00-assoc zero = assocInd zero zero zero _ _ λ x y z → sym (transportRefl (swapFun zero zero zero (x ⊗ (y ⊗ z))))
     00-assoc (suc zero) =
       assocInd zero zero 1 _ _ λ x y z → help x y z ∙ sym (transportRefl (swapFun zero zero 1 (x ⌣ₖ (y ⌣ₖ EM'→EM _ _ z))))
       where
       help : (x : G) (y : H) (z : EM' L' 1)
         → (cup∙ 0 1 (cup∙ 0 0 x .fst y) .fst (EM'→EM _ _ z)) ≡ swapFun zero zero 1  (x ⌣ₖ (y ⌣ₖ (EM'→EM _ _ z)))
       help x y embase-raw = refl
       help x y (emloop-raw g i) = refl
     00-assoc (suc (suc l)) =
       assocInd zero zero (suc (suc l)) _ _ λ x y z → help (00-assoc (suc l)) x y z ∙ sym (preSubstFunLoop _ (swapFun zero zero (2 + l) (x ⌣ₖ (y ⌣ₖ EM'→EM _ _ z))))
       where
       help : assL zero zero (suc l) ≡ assR zero zero (suc l)
         → (x : G) (y : H) (z : EM' L' (suc (suc l)))
         → (cup∙ 0 (suc (suc l)) (cup∙ 0 0 x .fst y) .fst ∣ z ∣ₕ)
          ≡ swapFun zero zero (suc (suc l)) (x ⌣ₖ (y ⌣ₖ ∣ z ∣))
       help p x y north = refl
       help p x y south = refl
       help p x y (merid a i) j = help2 j i
         where
         help2 : EM→ΩEM+1 (suc l) (_⌣ₖ_ {n = 0} (_⌣ₖ_ {n = 0} {m = 0} x y) (EM-raw→EM _ _ a))
               ≡ cong (swapFun zero zero (2 + l)) λ i → _⌣ₖ_ {n = 0} {m = suc (suc l)} x (_⌣ₖ_ {n = 0} {m = (suc (suc l))} y ∣ merid a i ∣ₕ)
         help2 = ((cong (EM→ΩEM+1 (suc l)) (assocConvert p x y (EM-raw→EM L' (suc l) a)
                                           ∙ preSubstFunLoop _ (swapFun zero zero (suc l) _))
                 ∙ sym (EMEqFunct l _ _))
                ∙ cong (cong (swapFun zero zero (2 + l)))
                       (EM→ΩEM+1-distr₀ₙ l x ((_⌣ₖ_ {n = 0} {m = (suc l)} y (EM-raw→EM _ _ a)))))

     01-assoc : (l : ℕ) → assL zero 1 l ≡ assR zero 1 l
     01-assoc zero = assocInd zero 1 zero _ _ λ { x embase-raw z → sym (transportRefl embase)
                                                ; x (emloop-raw g i) z → sym (transportRefl (EM→ΩEM+1 zero ((x ⊗ g) ⊗ z) i))}
     01-assoc (suc l) = assocInd zero 1 (suc l) _ _ λ x y z → help (01-assoc l) z y x
                                               ∙ sym (preSubstFunLoop _
                                                      (swapFun zero (suc zero) (suc l)
                                                        (_⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l} (EM'→EM _ _ y) (EM'→EM _ _ z)))))
       where
       help : assL zero 1 l ≡ assR zero 1 l → (z : EM' L' (suc l)) (y : EM₁-raw (AbGroup→Group H')) (x : fst G')
          → fst (assL zero 1 (suc l)) (EM'→EM (fst G' , snd G') zero x) .fst (EM'→EM H' 1 y) .fst (EM'→EM L' (suc l) z)
          ≡ swapFun zero (suc zero) (suc l)
                    (_⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l} (EM'→EM _ _ y) (EM'→EM _ _ z)))
       help ind z embase-raw x = refl
       help ind z (emloop-raw g i) x = flipSquare help2 i
         where
         help2 : cong (λ y → fst (assL zero 1 (suc l)) (EM'→EM (fst G' , snd G') zero x) .fst y .fst (EM'→EM L' (suc l) z)) (emloop g)
               ≡ cong (swapFun zero (suc zero) (suc l)) λ i → _⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l} (emloop g i) (EM'→EM _ _ z))
         help2 = cong (EM→ΩEM+1 (suc l)) (assocConvert (00-assoc (suc l)) x g (EM'→EM _ _ z)
                                        ∙ preSubstFunLoop _ ((swapFun zero zero (suc l)
                                                             (cup∙ zero (suc l) x .fst (cup∙ zero (suc l) g .fst (EM'→EM L' (suc l) z))))))
              ∙∙ sym (EMEqFunct l _ _)
              ∙∙ cong (cong (swapFun zero (suc zero) (suc l)))
                      (EM→ΩEM+1-distr₀ₙ l x (_⌣ₖ_ {n = zero} {m = suc l} g (EM'→EM _ _ z)))

     02-assoc : (n l : ℕ) → assL zero (suc n) l ≡ assR zero (suc n) l → assL zero (suc (suc n)) l ≡ assR zero (suc (suc n)) l
     02-assoc n zero ind =
       assocInd zero (suc (suc n)) zero _ _
         λ x y z → help x y z
                  ∙ sym (preSubstFunLoop (+'-assoc zero (suc (suc n)) zero)
                        (swapFun zero (suc (suc n)) zero _))
       where
       help : (x : G) (a : EM' H' (suc (suc n))) (z : L)
         → cup∙ _ 0 (cup∙ 0 (suc (suc n)) x .fst ∣ a ∣) .fst z
          ≡ swapFun zero (suc (suc n)) zero
              (_⌣ₖ_ {n = 0} {m = suc (suc n)} x
                (_⌣ₖ_ {n = suc (suc n)} {m = 0} (EM'→EM _ _ a) z))
       help x north z = refl
       help x south z = refl
       help x (merid a i) z = flipSquare help' i
         where
         help' : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = zero} (_⌣ₖ_ {n = zero} {m = suc (suc n)} x ∣ merid a i ∣) z)
            ≡ (cong (swapFun zero (suc (suc n)) zero)
                 (λ i → (_⌣ₖ_ {n = 0} {m = suc (suc n)} x (_⌣ₖ_ {n = suc (suc n)} {m = 0} ∣ merid a i ∣ₕ z))))
         help' =
              sym (EM→ΩEM+1-distrₙ₀ n z (_⌣ₖ_ {n = zero} {m = suc n} x (EM-raw→EM _ _ a)))
           ∙∙ cong (EM→ΩEM+1 (suc n)) (assocConvert ind x (EM-raw→EM H' (suc n) a) z
                 ∙ preSubstFunLoop _ (swapFun zero (suc n) zero
                   ((cup∙ zero (suc n) x .fst
                     (cup∙ (suc n) zero (EM-raw→EM H' (suc n) a) .fst z)))))
           ∙∙ (sym (EMEqFunct n _ _)
             ∙ cong (cong ((swapFun zero (suc (suc n)) zero)))
               (EM→ΩEM+1-distr₀ₙ n x (_⌣ₖ_ {n = suc n} {m = zero} (EM-raw→EM _ _ a) z)))
     02-assoc n (suc l) ind =
       assocInd zero (2 + n) (suc l) _ _
         λ x y z → {!!} ∙ {!!} -- sym (preSubstFunLoop _ (swapFun zero (suc (suc n)) (suc l) _))

     0-assoc : (m l : ℕ) → assL zero m l ≡ assR zero m l
     0-assoc zero = 00-assoc
     0-assoc (suc zero) = 01-assoc
     0-assoc (suc (suc n)) l = 02-assoc n l (0-assoc (suc n) l)

     ---
     n00-assoc : (l : ℕ) → assL 1 zero l ≡ assR 1 zero l
     n00-assoc =
       elim+2 (assocInd 1 zero zero _ _ λ x y z → l₁ x y z ∙ sym (transportRefl _))
              (assocInd 1 zero 1 _ _ (λ x y z → l₂ z y x ∙ sym (transportRefl _)))
              λ n ind → assocInd 1 zero (suc (suc n)) _ _ λ x y z → l₃ n ind x y z ∙ sym (funExt⁻ (lem n) _)
       where
       l₁ : (x : EM' G' 1) (y : H) (z : L)
         → fst (assL 1 zero 0) (EM'→EM G' 1 x) .fst (EM'→EM H' zero y) .fst (EM'→EM L' zero z)
         ≡ swapFun 1 zero 0 ((EM'→EM _ _ x ⌣ₖ (y ⌣ₖ z)))
       l₁ embase-raw y z = refl
       l₁ (emloop-raw g i) y z = refl

       l₂ : (z : EM' L' 1) (y : EM' H' zero) (x : EM' G' 1)
         → fst (assL 1 zero 1) (EM'→EM G' 1 x) .fst (EM'→EM H' zero y) .fst (EM'→EM L' 1 z)
         ≡ swapFun 1 zero 1 (EM'→EM _ _ x ⌣ₖ (y ⌣ₖ EM'→EM _ _ z))
       l₂ z y embase-raw = refl
       l₂ z y (emloop-raw g i) = sym (flipSquare help i)
         where
         help : cong (λ x → swapFun 1 zero 1 (x ⌣ₖ (y ⌣ₖ EM'→EM _ _ z))) (emloop g)
              ≡ cong (λ x → (_⌣ₖ_ {n = suc zero} {m = suc zero}
                     (_⌣ₖ_ {G' = G'} {H' = H'} {n = suc zero} {m = 0} x y) (EM'→EM _ _ z))) (emloop g)
         help = EMEqFunct 0 _ (cup∙ zero 1 g .fst (cup∙ zero 1 y .fst (EM'→EM _ _ z)))
              ∙ cong (EM→ΩEM+1 1) (sym (transportRefl _)
                                  ∙ sym (funExt⁻ (cong fst (funExt⁻
                                     (cong fst (funExt⁻ (cong fst (0-assoc zero 1)) g)) y)) (EM'→EM _ _ z)))

       lem : (n : ℕ) → substFun 1 zero (suc (suc n)) ≡ idfun _
       lem n = (λ i → subst (EM ((G' ⨂ H') ⨂ L')) (isSetℕ _ _ (+'-assoc 1 zero (2 + n)) refl i))
             ∙ funExt transportRefl

       l₃ : (n : ℕ) → assL 1 zero (suc n) ≡ assR 1 zero (suc n) →
         (x : EM' G' 1) (y : EM' H' zero) (z : EM' L' (suc (suc n))) →
         fst (assL 1 zero (suc (suc n))) (EM'→EM G' 1 x) .fst
         (EM'→EM H' zero y) .fst (EM'→EM L' (suc (suc n)) z)
         ≡
           (swapFun 1 zero (suc (suc n))
             (EM'→EM _ _ x ⌣ₖ (y ⌣ₖ ∣ z ∣)))
       l₃ n ind embase-raw y z = refl
       l₃ n ind (emloop-raw g i) y z = flipSquare help i
         where
         help : (λ i → (emloop (g ⊗ y) i ⌣ₖ ∣ z ∣)) ≡ cong (swapFun 1 zero (suc (suc n))) λ i → (emloop g i ⌣ₖ (y ⌣ₖ ∣ z ∣))
         help = cong (EM→ΩEM+1 (suc (suc n)))
                 (funExt⁻ (cong fst (funExt⁻ (cong fst (funExt⁻ (cong fst (0-assoc zero (suc (suc n)))) g)) y)) ∣ z ∣ₕ
                 ∙ preSubstFunLoop _ (swapFun zero zero (suc (suc n)) (g ⌣ₖ (y ⌣ₖ ∣ z ∣))))
              ∙ sym (EMEqFunct (suc n) _ (cup∙ zero (suc (suc n)) g .fst (cup∙ zero (suc (suc n)) y .fst ∣ z ∣)))

     n0-assoc : (n l : ℕ) → assL n zero l ≡ assR n zero l → assL (suc n) zero l ≡ assR (suc n) zero l
     n0-assoc zero l ind = n00-assoc l
     n0-assoc (suc n) l ind = {!!}

     --
     nm0-assoc : (n m : ℕ) → assL n (suc m) zero ≡ assR n (suc m) zero → assL (suc n) (suc m) zero ≡ assR (suc n) (suc m) zero
     nm0-assoc = {!!}

     mainassoc : (n m l : ℕ) → assL n (suc m) (suc l) ≡ assR n (suc m) (suc l) → assL (suc n) (suc m) (suc l) ≡ assR (suc n) (suc m) (suc l)
     mainassoc = {!!}

     mainAssoc : (n m l : ℕ) → assL n m l ≡ assR n m l
     mainAssoc zero m l = 0-assoc m l
     mainAssoc (suc n) zero l = n0-assoc n l (mainAssoc n zero l)
     mainAssoc (suc n) (suc m) zero = nm0-assoc n m (mainAssoc n (suc m) zero)
     mainAssoc (suc n) (suc m) (suc l) = mainassoc n m l (mainAssoc n (suc m) (suc l))


--      assoc1 : (n m l : ℕ)
--        → EM G' n → (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙))
--      fst (fst (assoc1 n m l x) y) z = (x ⌣ₖ y) ⌣ₖ z
--      snd (fst (assoc1 n m l x) y) = ⌣ₖ-0ₖ (n +' m) l _
--      snd (assoc1 n m l x) =
--        →∙Homogeneous≡ (isHomogeneousEM _)
--          (funExt λ z → (λ i → (⌣ₖ-0ₖ n m x i) ⌣ₖ z) ∙ 0ₖ-⌣ₖ (n +' m) l z)

--      assoc2 : (n m l : ℕ)
--        → EM G' n → (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ (G' ⨂ (H' ⨂ L')) (n +' (m +' l)) ∙))
--      fst (fst (assoc2 n m l x) y) z = x ⌣ₖ (y ⌣ₖ z)
--      snd (fst (assoc2 n m l x) y) =
--        (λ i → x ⌣ₖ (⌣ₖ-0ₖ m l y i)) ∙ ⌣ₖ-0ₖ n (m +' l) x
--      snd (assoc2 n m l x) =
--        →∙Homogeneous≡ (isHomogeneousEM _)
--          (funExt λ z → (λ i → x ⌣ₖ (0ₖ-⌣ₖ m l z i))
--                       ∙ ⌣ₖ-0ₖ n (m +' l) x)

--      open import Cubical.Algebra.Group.Morphisms

--      Iso→EM≃∙ : ∀ {ℓ ℓ'} {A : AbGroup ℓ} {B : AbGroup ℓ'} (e : AbGroupEquiv A B) (n : ℕ)
--        → EM∙ A n ≃∙ EM∙ B n
--      fst (Iso→EM≃∙ e n) = isoToEquiv (Iso→EMIso e n)
--      snd (Iso→EM≃∙ e zero) = IsGroupHom.pres1 (snd e)
--      snd (Iso→EM≃∙ e (suc zero)) = refl
--      snd (Iso→EM≃∙ e (suc (suc n))) = refl

--      EM→∙ : (n m l : ℕ)
--           → (EM ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ,
--        snd (EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l)))
--       →∙
--       (EM (G' ⨂ (H' ⨂ L')) ((n +' m) +' l) ,
--        snd (EM∙ (G' ⨂ (H' ⨂ L')) ((n +' m) +' l)))
--      fst (EM→∙ n m l) = Iso.fun (Iso→EMIso (invAbGroupEquiv ⨂assoc) _)
--      snd (EM→∙ n m l) = snd (Iso→EM≃∙ (invAbGroupEquiv ⨂assoc) ((n +' m) +' l))

--      coh∙ : (n m l : ℕ)
--        → (EM∙ L' l →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙)
--        →∙ ((EM∙ L' l →∙ EM∙ (G' ⨂ (H' ⨂ L')) ((n +' m) +' l) ∙))
--      coh∙ n m l = post∘∙ _ (EM→∙ n m l)

--      assoc₀₀ₙ : (l : ℕ) (g : fst G')
--        → post∘∙ (EM∙ L' l) (EM→∙ zero zero l) ∘∙ assoc1 zero zero l g
--         ≡ assoc2 zero zero l g
--      assoc₀₀ₙ =
--        elim+2
--          (λ g → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--          (funExt λ h → →∙Homogeneous≡ (isHomogeneousEM _)
--            (funExt λ l → refl)))
--          (λ g → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--          (funExt λ h → →∙Homogeneous≡ (isHomogeneousEM _)
--            (funExt (elimSet (AbGroup→Group L')
--              (λ l → hLevelEM _ 1 _ _)
--              refl
--              λ l → 
--                ((λ i j → inducedFun-EM-raw {G' = (G' ⨂ H') ⨂ L'}
--                            (fst (invAbGroupEquiv ⨂assoc) .fst , snd (invAbGroupEquiv ⨂assoc)) 1
--                             (emloop ((g ⊗ h) ⊗ l) i)))))))
--          λ l ind g → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--          (funExt λ h → →∙Homogeneous≡ (isHomogeneousEM _)
--            (funExt
--              (Trunc.elim
--                (λ _ → isOfHLevelPath (4 + l) (hLevelEM _ (2 + l)) _ _)
--                λ { north → refl
--                  ; south → refl
--                  ; (merid a i) j → h' l g ind h a (~ j) i})))
--        where
--        h' : (l : ℕ) (g : G) (as : (g₁ : fst G') →
--          (post∘∙ (EM∙ L' (suc l)) (EM→∙ zero zero (suc l)) ∘∙
--            assoc1 zero zero (suc l) g₁)
--          ≡ assoc2 zero zero (suc l) g₁) (h : fst H') (a : EM-raw L' (suc l)) →
--            (λ i → _⌣ₖ_ {n = 0} {m = (suc (suc l))} g (EM→ΩEM+1 (suc l) (_⌣ₖ_ {n = 0} {m = suc l} h (EM-raw→EM L' (suc l) a)) i))
--          ≡ cong (map
--              (inducedFun-EM-raw {G' = (G' ⨂ H') ⨂ L'} {H' = G' ⨂ (H' ⨂ L')}
--               (fst (invAbGroupEquiv ⨂assoc) .fst , snd (invAbGroupEquiv ⨂assoc))
--               (suc (suc l))))
--               (EM→ΩEM+1 (suc l) (_⌣ₖ_ {n = 0} {m = suc l} (_⌣ₖ_ {n = zero} {m = zero} g h) (EM-raw→EM L' (suc l) a)))
--        h' l g as h a = ((sym (EM→ΩEM-⌣ₗᵣ₀₂ l g (_⌣ₖ_ {n = 0} h (EM-raw→EM L' (suc l) a)))
--                 ∙ sym (cong (EM→ΩEM+1 (suc l))
--                   (Iso.rightInv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc l))
--                     (_⌣ₖ_ {n = zero} {m = suc l} g (_⌣ₖ_ {n = zero} h (EM-raw→EM L' (suc l) a))))))
--               ∙ sym (EMEqFunct l (invAbGroupEquiv ⨂assoc)
--                       ((Iso.inv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc l))
--                   (_⌣ₖ_ {n = zero} g (_⌣ₖ_ {n = zero} {m = suc l} h (EM-raw→EM L' (suc l) a)))))))
--               ∙ cong (cong ((Iso.fun (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc (suc l))))))
--                 (cong (EM→ΩEM+1 (suc l))
--                   (cong (Iso.inv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc l)))
--                     (sym (funExt⁻ (cong fst (funExt⁻ (cong fst (as g)) h))
--                       (EM-raw→EM L' (suc l) a)))
--             ∙ Iso.leftInv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc l))
--               ((_⌣ₖ_ {n = 0} {m = 0} g h) ⌣ₖ EM-raw→EM L' (suc l) a)))

--      assoc₀₂ₙ : (g : G) (m l : ℕ) → (ind : (post∘∙ (EM∙ L' l) (EM→∙ zero (suc m) l) ∘∙
--        assoc1 zero (suc m) l g)
--       ≡ assoc2 zero (suc m) l g) →
--        (post∘∙ (EM∙ L' l) (EM→∙ zero (suc (suc m)) l) ∘∙
--        assoc1 zero (suc (suc m)) l g)
--       ≡ assoc2 zero (suc (suc m)) l g
--      assoc₀₂ₙ g m =
--        ℕelim (λ ind → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--                 (funExt (Trunc.elim {!!}
--                   (λ a → →∙Homogeneous≡ (isHomogeneousEM _)
--                     (funExt (lem ind a))))))
--               λ n ind p → {!p!}
--        where
--        lem : (ind : (post∘∙ (EM∙ L' zero) (EM→∙ zero (suc m) zero) ∘∙
--                   assoc1 zero (suc m) zero g)
--                   ≡ assoc2 zero (suc m) zero g)
--             (a : Susp (EM-raw H' (suc m))) (l : L)
--          → ((post∘∙ (EM∙ L' zero) (EM→∙ zero (suc (suc m)) zero) ∘∙
--          assoc1 zero (suc (suc m)) zero g)
--         .fst ∣ a ∣ₕ .fst l)
--         ≡ (assoc2 zero (suc (suc m)) zero g .fst ∣ a ∣ₕ .fst l)
--        lem ind north l = refl
--        lem ind south l = refl
--        lem ind (merid a i) l j = help j i
--          where
--          lem2 : ∀ {ℓ} (m : ℕ) (H' : AbGroup ℓ) (a : EM H' (suc m))
--            → cong (cup∙ {G' = G'} {H' = H'} 0 (suc (suc m)) g .fst) (EM→ΩEM+1 (suc m) a)
--             ≡ EM→ΩEM+1 (suc m) (cup∙ 0 (suc m) g .fst a)
--          lem2 m H' a = {!!}

--          lem3 : ∀ {ℓ ℓ'} (m : ℕ) (H' : AbGroup ℓ) (L' : AbGroup ℓ') (a : EM H' (suc m)) (l : fst L')
--            → cong (λ x → cup∙ {G' = H'} {H' = L'} (suc (suc m)) 0 x .fst l) (EM→ΩEM+1 (suc m) a)
--             ≡ EM→ΩEM+1 (suc m) (cup∙ {G' = H'} {H' = L'} (suc m) 0 a .fst l) -- EM→ΩEM+1 (suc m) (cup∙ 0 (suc m) g .fst a)
--          lem3 m H' L' l a = {!!}

--          help : cong (fst (EM→∙ zero (suc (suc m)) zero))
--                  (λ i → cup∙ (2 + m) 0 (cup∙ 0 (2 + m) g .fst ∣ merid a i ∣ₕ) .fst l)
--               ≡ λ i → cup∙ 0 (2 + m) g .fst (cup∙ (2 + m) 0 ∣ merid a i ∣ₕ .fst l)
--          help = cong (cong (fst (EM→∙ zero (suc (suc m)) zero))) (lem3 m _ _ (cup∙ 0 (suc m) g .fst (EM-raw→EM _ _ a)) l )
--                ∙ EMEqFunct _ (invAbGroupEquiv ⨂assoc) (cup∙ (suc m) 0 (cup∙ 0 (suc m) g .fst (EM-raw→EM _ _ a)) .fst l)
--                ∙ cong (EM→ΩEM+1 (suc m)) (funExt⁻ (cong fst (funExt⁻ (cong fst ind) (EM-raw→EM _ _ a))) l)
--              ∙∙ sym (lem2 m _ (cup∙ (suc m) 0 (EM-raw→EM H' (suc m) a) .fst l))
--              ∙∙ cong (cong (cup∙ 0 (2 + m) g .fst))
--                      λ _ → EM→ΩEM+1 (suc m) (cup∙ (suc m) 0 (EM-raw→EM _ (suc m) a) .fst l)

--      assoc₀₁ₙ : (g : G) (l : ℕ)
--        → (post∘∙ (EM∙ L' l) (EM→∙ zero 1 l) ∘∙ assoc1 zero 1 l g)
--          ≡ assoc2 zero (suc zero) l g -- 
--      assoc₀₁ₙ g =
--        ℕelim (→∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--                 (funExt (EM₁→fun∙≡ _ (isHomogeneousEM _) {!!}
--                   (λ l → refl)
--                   λ h a _  → emloop (g ⊗ (h ⊗ a)))))
--               λ n ind → (→∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _)))
--                         (funExt (EM₁→fun∙≡ _ (isHomogeneousEM _) {!!}
--                           (λ l → refl)
--                           λ h a → cong (cong (fst (EM→∙ zero 1 (suc n))))
--                                    (cong (EM→ΩEM+1 (suc n))
--                                      ((sym (Iso.leftInv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc n)) _)
--                                             ∙ cong (Iso.inv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc n)))
--                                               (funExt⁻ (cong fst (funExt⁻ (cong fst (assoc₀₀ₙ (suc n) g)) h)) a))))
--                                 ∙∙ EMEqFunct n (invAbGroupEquiv ⨂assoc) _
--                                  ∙ cong (EM→ΩEM+1 (suc n)) (Iso.rightInv (Iso→EMIso (invAbGroupEquiv ⨂assoc) (suc n)) _)
--                                  ∙ lem n g _ (_⌣ₖ_ {n = zero} {m = suc n} h a)
--                                 ∙∙ λ i j → _⌣ₖ_ {n = zero} {m = suc (suc n)} g (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = zero} {m = suc n} h a) j)))
--        where
--        lem : {ℓ : Level} (n : ℕ) (g : fst G') (H : AbGroup ℓ) (x : EM H (suc n))
--          → EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = G'} {H' = H} {n = zero} {m = suc n} g x)
--          ≡ λ j → _⌣ₖ_ {G' = G'} {H' = H} {n = zero} {m = suc (suc n)} g (EM→ΩEM+1 (suc n) x j)
--        lem zero g H x = (rUnit _
--                       ∙ (cong (EM→ΩEM+1 (suc zero) (_⌣ₖ_ {G' = G'} {H' = H} {n = zero} {m = suc zero} g x) ∙_) (cong sym (sym (EM→ΩEM+1-0ₖ (suc zero))))))
--                       ∙ sym (cong-∙ (_⌣ₖ_ {n = zero} {m = suc (suc zero)} g) (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid embase))))
--                       ∙ λ i j → _⌣ₖ_ {n = zero} {m = suc (suc zero)} g (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase)) (~ i) j) --  {!!} ∣ₕ
--        lem (suc n) g H =
--          Trunc.elim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
--                     λ x → (rUnit _
--                       ∙ (cong (EM→ΩEM+1 (suc (suc n)) (_⌣ₖ_ {G' = G'} {H' = H} {n = zero} {m = suc (suc n)} g ∣ x ∣ₕ) ∙_) (cong sym (sym (EM→ΩEM+1-0ₖ (suc (suc n)))))))
--                       ∙ sym (cong-∙ (_⌣ₖ_ {n = zero} {m = suc (suc (suc n))} g) (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid north))))
--                       ∙ λ i j → _⌣ₖ_ {n = zero} {m = suc (suc (suc n))} g (cong-∙ ∣_∣ₕ (merid x) (sym (merid north)) (~ i) j)

--      assoc₁l : (n m : ℕ) (g : EM₁-raw (AbGroup→Group G')) → EM∙ H' m →∙ Ω (EM∙ (G' ⨂ H') (suc (1 +' m)))
--      fst (assoc₁l n m g) h = EM→ΩEM+1 (1 +' m) ((EM₁-raw→EM₁ _ g) ⌣ₖ h)
--      snd (assoc₁l n m g) = cong (EM→ΩEM+1 (1 +' m)) (⌣ₖ-0ₖ 1 m (EM₁-raw→EM₁ (AbGroup→Group G') g))
--                         ∙ EM→ΩEM+1-0ₖ (1 +' m)


--      0-assoc : (m l : ℕ) (g : fst G')
--        → post∘∙ (EM∙ L' l) (EM→∙ zero m l) ∘∙ assoc1 zero m l g
--        ≡ assoc2 zero m l g
--      0-assoc zero l g = assoc₀₀ₙ l g
--      0-assoc (suc zero) l g = assoc₀₁ₙ g l
--      0-assoc (suc (suc m)) l g = {!0-assoc (suc m) l g!} -- assoc₀₂ₙ g m l

--      main : (n m l : ℕ) (x : EM G' n)
--        → transport (λ i → EM∙ H' m
--                        →∙ (EM∙ L' l
--                        →∙ EM∙ (G' ⨂ (H' ⨂ L')) (+'-assoc n m l (~ i)) ∙))
--            (post∘∙ (EM∙ L' l) (EM→∙ n m l) ∘∙ assoc1 n m l x)
--          ≡ assoc2 n m l x
--      main zero m l x = help _ ∙ 0-assoc m l x
--        where
--        help : (y : _) → subst (λ x → EM∙ H' m →∙
--          (EM∙ L' l →∙ EM∙ (G' ⨂ (H' ⨂ L')) x ∙)) (sym (+'-assoc zero m l)) y ≡ y
--        help y = (λ i → subst  (λ x → EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ (G' ⨂ (H' ⨂ L')) x ∙))
--                        (isSetℕ _ _ (sym (+'-assoc zero m l)) refl i) y)
--               ∙ transportRefl y
--      main (suc zero) m l =
--        elimSet' _ {!!} λ b → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--          (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
--            (funExt λ z → cong (transport (λ i → fst (EM∙ (G' ⨂ (H' ⨂ L')) (+'-assoc 1 m l (~ i)))))
--                              (cong (fst ((EM→∙ 1 m l)))
--                              λ i → (EM₁-raw→EM₁ _ b ⌣ₖ transportRefl y i) ⌣ₖ (transportRefl z i)) ∙
--                              {!!}))
--      {-
--        EM₁→fun∙≡' _ (isHomogeneousEM _)
--          (λ _ → isOfHLevelPath' 2 {!isOfHLevel↑∙∙!} _ _)
--          (λ a b → (λ j → transport (λ i → fst (EM∙ (G' ⨂ (H' ⨂ L')) (+'-assoc 1 m l (~ i))))
--                     (EM→∙ 1 m l .fst
--                       {!!}))
--                  ∙ {!EM→∙ 1 m l .fst ?!}
--                  ∙ sym (0ₖ-⌣ₖ 1 (m +' l) (a ⌣ₖ b)))
--          {!ΣPathP!} -}
--      main (suc (suc n)) m l =
--        Trunc.elim {!!} λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
--          (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
--            (funExt λ z → cong (trFun m l ∘ EMF m l) (λ i → (_⌣ₖ_ {n = 2 + n} ∣ x ∣ₕ (transportRefl y i)) ⌣ₖ transportRefl z i)
--                         ∙ {!!}
--                         ∙ {!!}))
--        where
--        trFun : (m l : ℕ) → _
--        trFun m l = transport (λ i → fst (EM∙ (G' ⨂ (H' ⨂ L')) (+'-assoc (suc (suc n)) m l (~ i))))

--        EMF : (m l : ℕ) → _
--        EMF m l = EM→∙ (suc (suc n)) m l .fst

--        h : (m l : ℕ)
--           → (x : EM-raw G' (suc (suc n))) (y : EM H' m) (z : EM L' l)
--          → trFun m l (EMF m l ((∣ x ∣ ⌣ₖ y) ⌣ₖ z))
--           ≡ _⌣ₖ_ {n = 2 + n} ∣ x ∣ₕ (y ⌣ₖ z) 
--        h zero zero north y z = refl
--        h zero zero south y z = refl
--        h zero zero (merid a i) y z = {!!}
--          where
--          h2 : {!cong (trFun zero zero) ?!}
--          h2 = {!!}
--        h zero (suc l) north y z = refl
--        h zero (suc l) south y z = refl
--        h zero (suc l) (merid a i) y z = {!!}
--        h (suc m) zero north y z = refl
--        h (suc m) zero south y z = refl
--        h (suc m) zero (merid a i) y z = {!!}
--        h (suc m) (suc l) north y z = refl
--        h (suc m) (suc l) south y z = refl
--        h (suc m) (suc l) (merid a i) y z = {!!}



-- --      main : (n m l : ℕ) (x : EM G' n)
-- --        → transport (λ i → EM∙ H' m
-- --                        →∙ (EM∙ L' l
-- --                        →∙ EM∙ (G' ⨂ (H' ⨂ L')) (+'-assoc n m l (~ i)) ∙))
-- --            (post∘∙ (EM∙ L' l) (EM→∙ n m l) ∘∙ assoc1 n m l x)
-- --          ≡ assoc2 n m l x
-- --      main n m l =
-- --        EM-elim n {!!}
-- --          λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
-- --            (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
-- --              (funExt λ z → cong (subst (EM (G' ⨂ (H' ⨂ L'))) (sym (+'-assoc n m l)))
-- --                                  (cong (Iso.fun (Iso→EMIso (invAbGroupEquiv ⨂assoc) ((n +' m) +' l))) (λ i → ((EM-raw→EM G' n x ⌣ₖ transportRefl y i) ⌣ₖ
-- --        transportRefl z i)))
-- --                                  ∙ main2 n m l x y z))
-- --        where
-- --        main2 : (n m l : ℕ) (x : EM-raw G' n) (y : EM H' m) (z : EM L' l) →
-- --          subst (EM (G' ⨂ (H' ⨂ L'))) (sym (+'-assoc n m l))
-- --            (Iso.fun (Iso→EMIso (invAbGroupEquiv ⨂assoc) ((n +' m) +' l))
-- --              ((EM-raw→EM G' n x ⌣ₖ y) ⌣ₖ z))
-- --          ≡ ((EM-raw→EM G' n x ⌣ₖ (y ⌣ₖ z)))
-- --        main2 zero zero zero x y z = transportRefl _
-- --        main2 zero zero (suc zero) x y =
-- --          EM-elim 1 {!!}
-- --           (elimSet _
-- --             {!λ _ → is!}
-- --             refl
-- --             λ g → flipSquare {!!})
-- --        main2 zero zero (suc (suc l)) x y = {!!}
-- --        main2 zero (suc m) l x y z = {!!}
-- --        main2 (suc zero) m l x = {!!}
-- --        main2 (suc (suc n)) zero l x y z = {!!}
-- --        main2 (suc (suc n)) (suc m) zero x y z = {!!}
-- --        main2 (suc (suc n)) (suc m) (suc l) north y z = refl
-- --        main2 (suc (suc n)) (suc m) (suc l) south y z = refl
-- --        main2 (suc (suc n)) (suc m) (suc l) (merid a i) y z j =
-- --            ({!!}
-- --          ∙ cong (EM→ΩEM+1 (suc n +' (suc m +' suc l))) (main2 (suc n) (suc m) (suc l) a y z)) j i
-- --          where
-- --          F = subst (EM (G' ⨂ (H' ⨂ L'))) (sym (+'-assoc (suc (suc n)) (suc m) (suc l)))

-- --          F2 = map
-- --             (inducedFun-EM-raw
-- --              (fst (invAbGroupEquiv ⨂assoc) .fst , snd (invAbGroupEquiv ⨂assoc))
-- --              (suc (suc (suc (suc (n + m + l))))))

-- --          open import Cubical.Foundations.Function
-- --          F∘F2 = F ∘ F2

-- --          help : cong F∘F2 (λ i → (_⌣ₖ_ {n = suc (suc n) +' (suc m)} {m = (suc l)}
-- --                                   (_⌣ₖ_ {n = (suc (suc n))} {m = (suc m)} ∣ merid a i ∣ₕ y) z))
-- --               ≡ λ i → ∣ merid a i ∣ₕ ⌣ₖ (y ⌣ₖ z)
-- --          help = cong (cong F∘F2)
-- --                      (sym (funExt⁻ (cong fst (EM→ΩEM+1-⌣' (suc (n + m)) l (EM-raw→EM G' (suc n) a ⌣ₖ y))) z))
-- --                      {-
-- --                      (λ i → cong (λ x → _⌣ₖ_ {n = suc (suc n) +' (suc m)} {m = (suc l)} x z)
-- --                                   (fst (EM→ΩEM+1-⌣ n m a i) y)) -- (EM→ΩEM+1 (suc n +' suc m) (EM-raw→EM G' (suc n) a ⌣ₖ y)) -}
-- --               ∙ {!!}
-- --               ∙ cong (EM→ΩEM+1 (suc n +' (suc m +' suc l))) (main2 (suc n) (suc m) (suc l) a y z)
-- --               ∙ λ _ → EM→ΩEM+1 (suc n +' (suc m +' suc l)) (_⌣ₖ_ {n = suc n} (EM-raw→EM G' (suc n) a) (y ⌣ₖ z))

-- --      assoc≡' : (n m l : ℕ)
-- --        → {!!}
-- --      assoc≡' = {!!}

-- --      assoc≡ : (n m l : ℕ) (x : EM G' n)
-- --        → transport (λ i → EMPath2 n m l i) (assoc1 n m l x) ≡ (assoc2 n m l x)
-- --      assoc≡ n zero l x =
-- --          →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
-- --            (funExt (λ y → →∙Homogeneous≡ (isHomogeneousEM _)
-- --              (funExt λ z → {!!})))
-- --      assoc≡ n (suc m) zero x = {!!}
-- --      assoc≡ n (suc m) (suc l) =
-- --        {!!}
-- --      {-
-- --        EM-elim n (λ _ → isOfHLevelPathP (2 + n) {!isOfHLevel↑∙∙ l m n!} _ _)
-- --          {!!}
-- -- -}

-- -- module RightDistributivity {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
-- --    private
-- --      G = fst G'
-- --      H = fst H'

-- --      strG = snd G'
-- --      strH = snd H'

-- --      0G = 0g strG
-- --      0H = 0g strH

-- --      _+G_ = _+Gr_ strG
-- --      _+H_ = _+Gr_ strH

-- --      -H_ = -Gr_ strH
-- --      -G_ = -Gr_ strG


-- --      distrr1 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
-- --      fst (distrr1 n m x y) z = (x +ₖ y) ⌣ₖ z
-- --      snd (distrr1 n m x y) = ⌣ₖ-0ₖ n m _

-- --      distrr2 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
-- --      fst (distrr2 n m x y) z = (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
-- --      snd (distrr2 n m x y) = cong₂ _+ₖ_ (⌣ₖ-0ₖ n m x) (⌣ₖ-0ₖ n m y) ∙ rUnitₖ _ (0ₖ (n +' m))

-- --    mainDistrR : (n m : ℕ) (x y : EM G' (suc n))
-- --      → distrr1 (suc n) (suc m) x y ≡ distrr2 (suc n) (suc m) x y
-- --    mainDistrR zero m =
-- --      wedgeConEM.fun G' G' 0 0
-- --        (λ _ _ → isOfHLevel↑∙ 1 m _ _)
-- --        (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt (l x)))
-- --        (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt (r x)))
-- --        λ i → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt λ z → l≡r z i)
-- --      where
-- --      l : (x : _) (z : _) → _ ≡ _
-- --      l x z =
-- --           (λ i → (lUnitₖ 1 x i) ⌣ₖ z)
-- --        ∙∙ sym (lUnitₖ _ (x ⌣ₖ z))
-- --        ∙∙ λ i → 0ₖ-⌣ₖ _ _ z (~ i) +ₖ (x ⌣ₖ z)

-- --      r : (x : _) (z : _) → _ ≡ _
-- --      r x z =
-- --           ((λ i → (rUnitₖ 1 x i) ⌣ₖ z))
-- --        ∙∙ sym (rUnitₖ _ _)
-- --        ∙∙ λ i → (_⌣ₖ_ {n = 1} {m = suc m} x z) +ₖ 0ₖ-⌣ₖ (suc zero) (suc m) z (~ i)

-- --      l≡r : (z : _) → l embase z ≡ r embase z
-- --      l≡r z = pathTypeMake _ _ _

-- --    mainDistrR (suc n) m =
-- --      elim2 (λ _ _ → isOfHLevelPath (4 + n)
-- --                       (isOfHLevel↑∙ (2 + n) m) _ _)
-- --            (wedgeConEM.fun _ _ _ _
-- --              (λ x y → isOfHLevelPath ((2 + n) + (2 + n))
-- --                        (transport (λ i → isOfHLevel (((λ i → (+-comm n 2 (~ i) + (2 + n)))
-- --                                                          ∙ sym (+-assoc n 2 (2 + n))) (~ i))
-- --                                   (EM∙ H' (suc m) →∙ EM∙ ((fst (AbGroupPath (G' ⨂ H') (H' ⨂ G'))) ⨂-comm (~ i))
-- --                                   ((+'-comm (suc m) (suc (suc n))) i)))
-- --                                   (isOfHLevelPlus n
-- --                                     (LeftDistributivity.hLevLem m (suc (suc n))))) _ _)
-- --              (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt (l x)))
-- --              (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt (r x)))
-- --              λ i → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                         (funExt λ z → r≡l z i))
-- --      where
-- --      l : (x : _) (z : _) → _ ≡ _
-- --      l x z = (λ i → (lUnitₖ _ ∣ x ∣ i) ⌣ₖ z)
-- --         ∙∙ sym (lUnitₖ _ (∣ x ∣ ⌣ₖ z))
-- --         ∙∙ λ i → 0ₖ-⌣ₖ _ _ z (~ i) +ₖ (∣ x ∣ ⌣ₖ z)

-- --      r : (x : _) (z : _) → _ ≡ _
-- --      r x z = (λ i → (rUnitₖ _ ∣ x ∣ i) ⌣ₖ z)
-- --            ∙∙ sym (rUnitₖ _ (∣ x ∣ ⌣ₖ z))
-- --            ∙∙ λ i → (∣ x ∣ ⌣ₖ z) +ₖ 0ₖ-⌣ₖ _ _ z (~ i)

-- --      r≡l : (z : _) → l north z ≡ r north z
-- --      r≡l z = pathTypeMake _ _ _

-- -- -- TODO: Summarise distributivity proofs
-- -- -- TODO: Associativity and graded commutativity, following Cubical.ZCohomology.RingStructure
-- -- -- The following lemmas will be needed to make the types match up.
