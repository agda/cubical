{-# OPTIONS --safe --experimental-lossy-unification --no-forcing #-}

module Cubical.Algebra.Group.EilenbergMacLane.CupProduct where

open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity
open import Cubical.Algebra.Group.EilenbergMacLane.GroupStructure
open import Cubical.Algebra.Group.EilenbergMacLane.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1 renaming (rec to EMrec)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.HITs.Susp
open import Cubical.Functions.Morphism
open import Cubical.Foundations.Path

open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group

open import Cubical.Foundations.Pointed.Homogeneous


private
  variable
    ℓ ℓ' ℓ'' : Level

stupidInd : ∀ {ℓ} {A : ℕ → Type ℓ} → A 0 → A 1
          → ((n : ℕ) → (A (suc n) → A (suc (suc n))))
          → (n : ℕ) → A n
stupidInd a0 a1 ind zero = a0
stupidInd a0 a1 ind (suc zero) = a1
stupidInd {A = A} a0 a1 ind (suc (suc n)) =
  ind n (stupidInd {A = A} a0 a1 ind (suc n))

stupidInd' : ∀ {ℓ} {A : ℕ → Type ℓ} → A 0
          → ((n : ℕ) → (A n → A (suc n)))
          → (n : ℕ) → A n
stupidInd' a0 ind zero = a0
stupidInd' a0 ind (suc n) = ind n (stupidInd' a0 ind n)

_+'_ : ℕ → ℕ → ℕ
zero +' m = m
suc n +' zero = suc n
suc n +' suc m = suc (suc (n + m))

+'-comm : (n m : ℕ) → n +' m ≡ m +' n
+'-comm zero zero = refl
+'-comm zero (suc m) = refl
+'-comm (suc n) zero = refl
+'-comm (suc n) (suc m) = cong (2 +_) (+-comm n m)

+'≡+ : (n m : ℕ) → n +' m ≡ n + m
+'≡+ zero zero = refl
+'≡+ zero (suc m) = refl
+'≡+ (suc n) zero = cong suc (+-comm zero n)
+'≡+ (suc n) (suc m) = cong suc (sym (+-suc n m))

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)

inducedFun-EM-raw : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
                     → AbGroupHom G' H'
                     → ∀ n
                     →  EM-raw G' n → EM-raw H' n
inducedFun-EM-raw f =
  stupidInd (fst f)
    (EMrec _ emsquash embase
     (λ g → emloop (fst f g))
      λ g h → compPathR→PathP (sym
                (sym (lUnit _)
              ∙∙ cong (_∙ (sym (emloop (fst f h)))) (cong emloop (IsGroupHom.pres· (snd f) g h)
                                                   ∙ emloop-comp _ (fst f g) (fst f h))
              ∙∙ sym (∙assoc _ _ _)
              ∙∙ cong (emloop (fst f g) ∙_) (rCancel _)
              ∙∙ sym (rUnit _))))
    (λ n ind → λ { north → north
                  ; south → south
                  ; (merid a i) → merid (ind a) i} )

inducedFun-EM-rawIso : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
                     → AbGroupEquiv G' H'
                     → ∀ n → Iso (EM-raw G' n) (EM-raw H' n)
Iso.fun (inducedFun-EM-rawIso e n) = inducedFun-EM-raw (_ , (snd e)) n
Iso.inv (inducedFun-EM-rawIso e n) = inducedFun-EM-raw (_ , isGroupHomInv e) n
Iso.rightInv (inducedFun-EM-rawIso e n) = h n
  where
  h : (n : ℕ) → section (inducedFun-EM-raw (fst e .fst , snd e) n)
      (inducedFun-EM-raw (invEq (fst e) , isGroupHomInv e) n)
  h = stupidInd
    (secEq (fst e))
    (elimSet _ (λ _ → emsquash _ _) refl
                       (λ g → compPathR→PathP
                          ((sym (cong₂ _∙_ (cong emloop (secEq (fst e) g)) (sym (lUnit _))
                               ∙ rCancel _)))))
    λ n p → λ { north → refl
               ; south → refl
               ; (merid a i) k → merid (p a k) i}
Iso.leftInv (inducedFun-EM-rawIso e n) = h n
  where
  h : (n : ℕ) → retract (Iso.fun (inducedFun-EM-rawIso e n))
                          (Iso.inv (inducedFun-EM-rawIso e n))
  h = stupidInd
    (retEq (fst e))
    (elimSet _ (λ _ → emsquash _ _) refl
                       (λ g → compPathR→PathP
                          ((sym (cong₂ _∙_ (cong emloop (retEq (fst e) g)) (sym (lUnit _))
                               ∙ rCancel _)))))
    λ n p → λ { north → refl
               ; south → refl
               ; (merid a i) k → merid (p a k) i}

Iso→EMIso : {G : AbGroup ℓ} {H : AbGroup ℓ'}
  → AbGroupEquiv G H → ∀ n → Iso (EM G n) (EM H n) 
Iso→EMIso is zero = inducedFun-EM-rawIso is zero
Iso→EMIso is (suc zero) = inducedFun-EM-rawIso is 1
Iso→EMIso is (suc (suc n)) = mapCompIso (inducedFun-EM-rawIso is (suc (suc n)))

EM⊗-commFun : {G : AbGroup ℓ} {H : AbGroup ℓ'}
  → ∀ n →  Iso (EM (G ⨂ H) n) (EM (H ⨂ G) n)
EM⊗-commFun {G = G} {H = H} = Iso→EMIso (GroupIso→GroupEquiv ⨂-commIso)

EM⊗-assocIso : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
  → ∀ n → Iso (EM (G ⨂ (H ⨂ L)) n) (EM ((G ⨂ H) ⨂ L) n)
EM⊗-assocIso = Iso→EMIso (GroupIso→GroupEquiv (GroupEquiv→GroupIso ⨂assoc))

pathType : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → Type ℓ
pathType n x p = sym (rUnitₖ (2 + n) x) ∙ (λ i → x +ₖ p i) ≡ sym (lUnitₖ (2 + n) x) ∙ λ i → p i +ₖ x

lem : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x)
    → pathType n x p
lem n x = J (λ x p → pathType n x p) refl

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
     stupidInd
       (_⊗ h)
       (elimGroupoid _ (λ _ → emsquash)
         embase
         (λ g → emloop (g ⊗ h))
         λ g l →
           compPathR→PathP
             (sym (∙assoc _ _ _
                ∙∙ cong₂ _∙_ (sym (emloop-comp _ _ _) ∙ cong emloop (sym (linl g l h))) refl
                ∙∙ rCancel _)))
       λ n f → trRec (isOfHLevelTrunc (4 + n))
                        λ { north → 0ₖ (suc (suc n))
                          ; south → 0ₖ (suc (suc n))
                          ; (merid a i) → EM→ΩEM+1 (suc n) (f (EM-raw→EM _ _ a)) i}

   ·₀ : G → (m : ℕ) → EM H' m → EM (G' ⨂ H') m
   ·₀ g =
     stupidInd (λ h → g ⊗ h)
               (elimGroupoid _ (λ _ → emsquash)
                 embase
                 (λ h → emloop (g ⊗ h))
                 λ h l → compPathR→PathP
                   (sym (∙assoc _ _ _
                      ∙∙ cong₂ _∙_ (sym (emloop-comp _ _ _) ∙ cong emloop (sym (linr g h l))) refl
                      ∙∙ rCancel _)))
               λ n f
               → trRec (isOfHLevelTrunc (4 + n))
                        λ { north → 0ₖ (suc (suc n))
                          ; south → 0ₖ (suc (suc n))
                          ; (merid a i) → EM→ΩEM+1 (suc n) (f (EM-raw→EM _ _ a)) i}

   ·₀-distr : (g h : G) → (m : ℕ)  (x : EM H' m) → ·₀ (g +G h) m x ≡ ·₀ g m x +ₖ ·₀ h m x
   ·₀-distr g h =
     stupidInd
       (linl g h)
       (elimSet _ (λ _ → emsquash _ _)
         refl
         (λ w → compPathR→PathP (sym ((λ i → emloop (linl g h w i)
                               ∙ (lUnit (sym (cong₂+₁ (emloop (g ⊗ w)) (emloop (h ⊗ w)) i)) (~ i)))
              ∙∙ cong₂ _∙_ (emloop-comp _ (g ⊗ w) (h ⊗ w)) refl
              ∙∙ rCancel _))))
       λ m ind →
         trElim (λ _ → isOfHLevelTruncPath)
                λ { north → refl
                  ; south → refl
                  ; (merid a i) k → z m ind a k i}

      where
      z : (m : ℕ) → ((x : EM H' (suc m)) → ·₀ (g +G h) (suc m) x ≡ ·₀ g (suc m) x +ₖ ·₀ h (suc m) x) → (a : EM-raw H' (suc m))
        → cong (·₀ (g +G h) (suc (suc m))) (cong ∣_∣ₕ (merid a)) ≡
          cong₂ _+ₖ_
            (cong (·₀ g (suc (suc m))) (cong ∣_∣ₕ (merid a)))
            (cong (·₀ h (suc (suc m))) (cong ∣_∣ₕ (merid a)))
      z m ind a = (λ i → EM→ΩEM+1 _ (ind (EM-raw→EM _ _ a) i))
               ∙∙ EM→ΩEM+1-hom _ (·₀ g (suc m) (EM-raw→EM H' (suc m) a)) (·₀ h (suc m) (EM-raw→EM H' (suc m) a))
               ∙∙ sym (cong₂+₂ m (cong (·₀ g (suc (suc m))) (cong ∣_∣ₕ (merid a)))
                                 (cong (·₀ h (suc (suc m))) (cong ∣_∣ₕ (merid a))))

   ·₀0 : (m : ℕ) → (g : G) → ·₀ g m (0ₖ m) ≡ 0ₖ m
   ·₀0 zero = rCancelPrim
   ·₀0 (suc zero) g = refl
   ·₀0 (suc (suc m)) g = refl

   ·₀'0 : (m : ℕ) (h : H) → ·₀' h m (0ₖ m) ≡ 0ₖ m
   ·₀'0 zero = lCancelPrim
   ·₀'0 (suc zero) g = refl
   ·₀'0 (suc (suc m)) g = refl

   0·₀ : (m : ℕ) → (x : _) → ·₀ 0G m x ≡ 0ₖ m
   0·₀ =
     stupidInd lCancelPrim
       (elimSet _ (λ _ → emsquash _ _)
         refl
         λ g → compPathR→PathP ((sym (emloop-1g _)
                                ∙ cong emloop (sym (lCancelPrim g)))
                                ∙∙ (λ i → rUnit (rUnit (cong (·₀ 0G 1) (emloop g)) i) i)
                                ∙∙ sym (∙assoc _ _ _)))
       λ n f → trElim (λ _ → isOfHLevelTruncPath)
                       λ { north → refl
                         ; south → refl
                         ; (merid a i) j → (cong (EM→ΩEM+1 (suc n)) (f (EM-raw→EM _ _ a))
                                           ∙ EM→ΩEM+1-0ₖ _) j i}

   0·₀' : (m : ℕ) (g : _) → ·₀' 0H m g ≡ 0ₖ m
   0·₀' =
     stupidInd
       rCancelPrim
       (elimSet _ (λ _ → emsquash _ _)
         refl
         λ g → compPathR→PathP (sym (∙assoc _ _ _
                              ∙∙ sym (rUnit _) ∙ sym (rUnit _)
                              ∙∙ (cong emloop (rCancelPrim g)
                                ∙ emloop-1g _))))
       λ n f → trElim (λ _ → isOfHLevelTruncPath)
                       λ { north → refl
                         ; south → refl
                         ; (merid a i) j → (cong (EM→ΩEM+1 (suc n)) (f (EM-raw→EM _ _ a))
                                           ∙ EM→ΩEM+1-0ₖ _) j i} 

   cup∙ : ∀ n m → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
   cup∙ =
     stupidInd'
       (λ m g → (·₀ g m) , ·₀0 m g)
         λ n f →
           stupidInd'
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
           ; (merid a i) → (λ x → EM→ΩEM+1 _ (ind _ (EM-raw→EM _ _ a) .fst x) i)
                          , λ j → (cong (EM→ΩEM+1 (suc (suc (n + m)))) (ind (suc m) (EM-raw→EM G' (suc n) a) .snd)
                                 ∙ EM→ΩEM+1-0ₖ _) j i}

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

   private
     distrl1 : (n m : ℕ) → EM H' m → EM H' m → EM∙ G' n →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrl1 n m x y) z = z ⌣ₖ (x +ₖ y)
     snd (distrl1 n m x y) = 0ₖ-⌣ₖ n m _

     distrl2 : (n m : ℕ) → EM H' m → EM H' m → EM∙ G' n →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrl2 n m x y) z = (z ⌣ₖ x) +ₖ (z ⌣ₖ y)
     snd (distrl2 n m x y) = cong₂ _+ₖ_ (0ₖ-⌣ₖ n m x) (0ₖ-⌣ₖ n m y) ∙ rUnitₖ _ (0ₖ (n +' m))

     hLevLem : (n m : ℕ) → isOfHLevel (suc (suc m)) (EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H') ((suc n) +' m))
     hLevLem n m = subst (isOfHLevel (suc (suc m))) (λ i → EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H')
                         ((cong suc (+-comm m n) ∙ sym (+'≡+ (suc n) m)) i)) (isOfHLevel↑∙ m n)




   mainDistrL : (n m : ℕ) (x y : EM H' (suc m)) → distrl1 (suc n) (suc m) x y ≡ distrl2 (suc n) (suc m) x y
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
     l : (x : EM H' 1) (z : _) → (distrl1 (suc n) 1 embase x .fst z) ≡ (distrl2 (suc n) 1 embase x .fst z)
     l x z = cong (z ⌣ₖ_) (lUnitₖ _ x)
            ∙∙ sym (lUnitₖ _ (z ⌣ₖ x))
            ∙∙ λ i → (⌣ₖ-0ₖ (suc n) (suc zero) z (~ i)) +ₖ (z ⌣ₖ x)

     r : (z : EM H' 1) (x : EM G' (suc n)) → (distrl1 (suc n) 1 z embase .fst x) ≡ (distrl2 (suc n) 1 z embase .fst x)
     r y z = cong (z ⌣ₖ_) (rUnitₖ _ y)
            ∙∙ sym (rUnitₖ _ (z ⌣ₖ y))
            ∙∙ λ i → (z ⌣ₖ y) +ₖ (⌣ₖ-0ₖ (suc n) (suc zero) z (~ i))

     l≡r : (z : EM G' (suc n)) → l embase z ≡ r embase z
     l≡r z = sym (lem _ _ (sym (⌣ₖ-0ₖ (suc n) (suc zero) z)))

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
     → (distrl1 (suc n) (suc (suc m)) (0ₖ _) ∣ x ∣ₕ .fst z) ≡ (distrl2 (suc n) (suc (suc m)) (0ₖ _) ∣ x ∣ₕ .fst z)
    l x z = cong (z ⌣ₖ_) (lUnitₖ (suc (suc m)) ∣ x ∣)
         ∙∙ sym (lUnitₖ _ (z ⌣ₖ ∣ x ∣))
         ∙∙ λ i → (⌣ₖ-0ₖ (suc n) (suc (suc m)) z (~ i)) +ₖ (z ⌣ₖ ∣ x ∣)

    r : (x : EM-raw H' (suc (suc m))) (z : EM G' (suc n))
      → (distrl1 (suc n) (suc (suc m)) ∣ x ∣ₕ (0ₖ _) .fst z) ≡ (distrl2 (suc n) (suc (suc m)) ∣ x ∣ₕ (0ₖ _) .fst z)
    r x z = cong (z ⌣ₖ_) (rUnitₖ (suc (suc m)) ∣ x ∣)
         ∙∙ sym (rUnitₖ _ (z ⌣ₖ ∣ x ∣))
         ∙∙ λ i → (z ⌣ₖ ∣ x ∣) +ₖ (⌣ₖ-0ₖ (suc n) (suc (suc m)) z (~ i))

    l≡r : (z : EM G' (suc n)) → l north z ≡ r north z
    l≡r z = sym (lem _ _ (sym (⌣ₖ-0ₖ (suc n) (suc (suc m)) z)))

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


     distrr1 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrr1 n m x y) z = (x +ₖ y) ⌣ₖ z
     snd (distrr1 n m x y) = ⌣ₖ-0ₖ n m _

     distrr2 : (n m : ℕ) → EM G' n → EM G' n → EM∙ H' m →∙ EM∙ (G' ⨂ H') (n +' m)
     fst (distrr2 n m x y) z = (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
     snd (distrr2 n m x y) = cong₂ _+ₖ_ (⌣ₖ-0ₖ n m x) (⌣ₖ-0ₖ n m y) ∙ rUnitₖ _ (0ₖ (n +' m))

     hLevLem2 : (n m : ℕ) → isOfHLevel (suc (suc m)) (EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H') ((suc n) +' m))
     hLevLem2 n m = subst (isOfHLevel (suc (suc m))) (λ i → EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H')
                         ((cong suc (+-comm m n) ∙ sym (+'≡+ (suc n) m)) i)) (isOfHLevel↑∙ m n)

   mainDistrR : (n m : ℕ) (x y : EM G' (suc n)) → distrr1 (suc n) (suc m) x y ≡ distrr2 (suc n) (suc m) x y
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
     l≡r z = lem _ _ _

   mainDistrR (suc n) m =
     elim2 (λ _ _ → isOfHLevelPath (4 + n)
                      (isOfHLevel↑∙ (2 + n) m) _ _)
           (wedgeConEM.fun _ _ _ _
             (λ x y → isOfHLevelPath ((2 + n) + (2 + n))
                        {!subst !} _ _)
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
     r≡l z = lem _ _ _
