{-# OPTIONS --lossy-unification #-}

{-
This file contains:
1. Construction of the cup product ⌣ₖ : K(G,n) × K(H,m) → K(G ⊗ H , n + m) together with
  proofs that 0ₖ ⌣ₖ x = x ⌣ₖ 0ₖ = 0ₖ
2. Proof that, for rings G and H, we have 1ᵣ ⌣ x = x and x ⌣ 1ₕ = x
   (in module Neutral)
3. Proofs of left and right distributivity
    (LeftDistributivity.main and RightDistributivity.main)
4. Proofs of associativity (Assoc.main)
5. Proof that the cup product repects homomorphisms G -ϕ→ G' , H -ψ→ H', i.e.
                              ⌣ₖ
           K(G,n) × K(H,m) -----→ K(G ⊗ H, n + m)
                  ∣                     ∣
 K(ϕ,n) × K(ψ,m)  ∣                     ∣ K(ϕ ⊗ ψ, n+m)
                  ̌            ⌣ₖ      ̌
           K(G',n) × K(H',m) ----> K(G' ⊗ H' , m)

-}

module Cubical.Homotopy.EilenbergMacLane.CupProductTensor where

open import Cubical.Homotopy.EilenbergMacLane.Base
  renaming (elim to EM-elim ; elim2 to EM-elim2)
open import Cubical.Homotopy.EilenbergMacLane.WedgeConnectivity
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Ring

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Data.Nat hiding (_·_) renaming (elim to ℕelim)
open import Cubical.Data.Sigma

open import Cubical.Functions.Morphism

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Truncation as Trunc
  renaming (rec to trRec; elim to trElim ; rec2 to trRec2)
open import Cubical.HITs.EilenbergMacLane1
  renaming (rec to EMrec ; elim to EM₁elim)
open import Cubical.HITs.Susp

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)

open PlusBis

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Lemma for distributativity of cup product (used later)
private
  pathType : {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → Type ℓ
  pathType n x p = sym (rUnitₖ (2 + n) x) ∙ (λ i → x +ₖ p i)
                 ≡ sym (lUnitₖ (2 + n) x) ∙ λ i → p i +ₖ x

  pathTypeMake : {G : AbGroup ℓ} (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x)
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
           ; (merid a i) →
             (λ x → EM→ΩEM+1 (2 + (n + m)) (ind (suc m) (EM-raw→EM _ _ a) .fst x) i)
                  , λ j → pp a j i}
        where
        pp : (a : _)
          → EM→ΩEM+1 (suc (suc (n + m)))
              (ind (suc m) (EM-raw→EM G' (suc n) a) .fst (snd (EM∙ H' (suc m))))
          ≡ refl
        pp a = cong (EM→ΩEM+1 (suc (suc (n + m)))) (ind (suc m) (EM-raw→EM G' (suc n) a) .snd)
             ∙ EM→ΩEM+1-0ₖ _

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

module Neutral {G'' : Ring ℓ} {H'' : Ring ℓ'} where
  private
    open RingStr renaming (_+_ to _+R_)
    G' = Ring→AbGroup G''
    H' = Ring→AbGroup H''
    G = fst G''
    H = fst H''

    1G = 1r (snd G'')
    1H = 1r (snd H'')

  1ₖ-⌣ₖ : (m : ℕ) (x : EM H' m)
    → (_⌣ₖ_ {G' = G'} {n = zero} {m = m} 1G x) ≡ inducedFun-EM (rIncl⨂ 1G) m x
  1ₖ-⌣ₖ zero x = refl
  1ₖ-⌣ₖ (suc zero) = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) → refl}
  1ₖ-⌣ₖ (suc (suc m)) =
    Trunc.elim (λ _ → isOfHLevelPath (4 + m) (hLevelEM _ (2 + m)) _ _)
      (help m (1ₖ-⌣ₖ (suc m)))
    where
    help : (m : ℕ)
      → ((a : EM H' (suc m))
      → (_⌣ₖ_ {n = zero} {m = suc m} (1r (snd G'')) a)
      ≡ inducedFun-EM (rIncl⨂ 1G) (suc m) a)
      → (a : EM-raw H' (suc (suc m)))
      → (_⌣ₖ_ {n = zero} {m = 2 + m} (1r (snd G'')) ∣ a ∣ₕ)
      ≡ inducedFun-EM (rIncl⨂ 1G) (suc (suc m)) ∣ a ∣ₕ
    help m ind north = refl
    help m ind south i = ∣ merid ptEM-raw i ∣ₕ
    help m ind (merid a i) j = lem j i
      where
      lem : PathP (λ i → 0ₖ {G = G' ⨂ H'} (suc (suc m)) ≡ ∣ merid ptEM-raw i ∣)
        (EM→ΩEM+1 (suc m) (_⌣ₖ_ {G' = G'} {n = zero} {m = suc m} (1r (snd G'')) (EM-raw→EM H' _ a)))
        (cong (inducedFun-EM (rIncl⨂ 1G) (suc (suc m))) (cong ∣_∣ₕ (merid a)))
      lem = (cong (EM→ΩEM+1 (suc m)) (ind (EM-raw→EM H' (suc m) a)
                                    ∙ sym (EM-raw→EM-funct _ (rIncl⨂ 1G) a))
          ∙ EM→ΩEM+1∘EM-raw→EM m (inducedFun-EM-raw (rIncl⨂ 1G) (suc m) a))
          ◁ (λ i j → ∣ compPath-filler (merid (inducedFun-EM-raw (rIncl⨂ 1G) (suc m) a)) (sym (merid ptEM-raw)) (~ i) j ∣ₕ)

  private
    pre-⌣ₖ-1ₖ : (n : ℕ) (x : EM G' (suc n))
      → _⌣ₖ_ {H' = H'} {n = (suc n)} {m = zero} x 1H
       ≡ inducedFun-EM (lIncl⨂ 1H) (suc n) x
    pre-⌣ₖ-1ₖ zero = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
      λ { embase-raw → refl ; (emloop-raw g i) → refl}
    pre-⌣ₖ-1ₖ (suc n) =
      Trunc.elim (λ _ → isOfHLevelPath (4 + n) (hLevelEM _ (2 + n)) _ _)
        (help (pre-⌣ₖ-1ₖ n))
      where
      help : ((x : EM G' (suc n))
               → _⌣ₖ_ {H' = H'} {n = (suc n)} {m = zero} x 1H
                 ≡ inducedFun-EM (lIncl⨂ 1H) (suc n) x)
           → (a : Susp (EM-raw G' (suc n)))
           → (_⌣ₖ_ {H' = H'} {n = (suc (suc n))} {m = zero} ∣ a ∣ 1H)
            ≡ map (inducedFun-EM-raw (lIncl⨂ 1H) (suc (suc n))) ∣ a ∣
      help ind north = refl
      help ind south i = ∣ merid ptEM-raw i ∣ₕ
      help ind (merid a i) = flipSquare lem i
        where
        lem : PathP (λ i → 0ₖ {G = G' ⨂ H'} (suc (suc n)) ≡ ∣ merid ptEM-raw i ∣)
               (EM→ΩEM+1 (suc n) (_⌣ₖ_ {H' = H'} {m = zero} (EM-raw→EM _ _ a) 1H))
               (cong (inducedFun-EM (lIncl⨂ 1H) (suc (suc n))) (cong ∣_∣ₕ (merid a)))
        lem = (cong (EM→ΩEM+1 (suc n)) (ind (EM-raw→EM G' (suc n) a)
                                      ∙ sym (EM-raw→EM-funct _ _ a))
            ∙ EM→ΩEM+1∘EM-raw→EM n (inducedFun-EM-raw (lIncl⨂ 1H) (suc n) a))
            ◁ λ i j → ∣ compPath-filler (merid (inducedFun-EM-raw (lIncl⨂ 1H) (suc n) a)) (sym (merid ptEM-raw)) (~ i) j ∣ₕ

  ⌣ₖ-1ₖ : (n : ℕ) (x : EM G' n)
      → _⌣ₖ_ {H' = H'} {n = n} {m = zero} x 1H
       ≡ subst (EM (G' ⨂ H')) (+'-comm zero n) (inducedFun-EM (lIncl⨂ 1H) n x)
  ⌣ₖ-1ₖ zero x = sym (transportRefl _)
  ⌣ₖ-1ₖ (suc n) x = pre-⌣ₖ-1ₖ n x
                  ∙ sym (transportRefl _)
                  ∙ λ i → subst (EM (G' ⨂ H'))
                            (isSetℕ _ _ refl (+'-comm zero (suc n)) i)
                            (inducedFun-EM (lIncl⨂ 1H) (suc n) x)

module LeftDistributivity {G' : AbGroup ℓ} {H' : AbGroup ℓ'} where
  hLevLem : (n m : ℕ) → isOfHLevel (suc (suc m)) (EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H') ((suc n) +' m))
  hLevLem n m =
    subst (isOfHLevel (suc (suc m)))
          (λ i → EM∙ G' (suc n) →∙ EM∙ (G' ⨂ H')
          ((cong suc (+-comm m n) ∙ sym (+'≡+ (suc n) m)) i)) (isOfHLevel↑∙ m n)

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

  main : (n m : ℕ) (x : EM G' n) (y z : EM H' m)
    → (x ⌣ₖ (y +ₖ z)) ≡ (x ⌣ₖ y) +ₖ (x ⌣ₖ z)
  main zero zero = ⊗DistR+⊗
  main zero (suc m) x =
    EM-elim2 _ (λ _ _ → isOfHLevelPath (3 + m) (hLevelEM _ (suc m)) _ _)
             (help m)
    where
    c : (m : ℕ) → _
    c m = _⌣ₖ_ {G' = G'} {H' = H'} {n = zero} {m = suc m}

    help : (m : ℕ) (y z : EM-raw H' (suc m))
      → (c m x (EM-raw→EM H' (suc m) y +ₖ EM-raw→EM H' (suc m) z))
        ≡ (c m x (EM-raw→EM H' (suc m) y)) +ₖ (c m x (EM-raw→EM H' (suc m) z))
    help zero =
      wedgeConEM.fun _ _ _ _
        (λ _ _ → isOfHLevelPath' 2 (hLevelEM _ 1) _ _)
        (λ z → cong (c zero x) (lUnitₖ _ (EM-raw→EM H' 1 z)))
        (λ y → cong (c zero x) (rUnitₖ _ (EM-raw→EM H' 1 y)) ∙ sym (rUnitₖ _ (c zero x (EM-raw→EM H' 1 y))))
        (rUnit _)
    help (suc m) =
      wedgeConEM.fun _ _ _ _
        (λ _ _ → isOfHLevelPath (suc (suc m) + (suc (suc m)))
          (subst (λ x → isOfHLevel x (EM (G' ⨂ H') (suc (suc m))))
            (cong (suc ∘ suc) (sym (+-suc m (suc m) ∙ cong suc (+-suc m m))))
            (isOfHLevelPlus' {n = m} (4 + m) (hLevelEM _ (suc (suc m))))) _ _)
        (λ z → cong (c (suc m) x) (lUnitₖ _ (EM-raw→EM H' (2 + m) z))
              ∙ sym (lUnitₖ _ (c (suc m) x (EM-raw→EM H' (2 + m) z))))
        (λ y → cong (c (suc m) x) (rUnitₖ _ (EM-raw→EM H' (2 + m) y))
             ∙ sym (rUnitₖ _ (c (suc m) x (EM-raw→EM H' (2 + m) y))))
        refl
  main (suc n) zero =
    EM-raw'-elim G' (suc n) (λ _ → isOfHLevelΠ2 (suc (suc n)) λ _ _ → hLevelEM _ (suc n) _ _)
      (lem n (main n zero))
    where
    cup : (n : ℕ) → _
    cup n = _⌣ₖ_ {G' = G'} {H' = H'} {n = n} {m = zero}

    lem : (n : ℕ) (ind : (x : EM G' n) (y z : fst H')
            → cup n x (y +ₖ z) ≡ cup n x y +ₖ cup n x z)
          (x : EM-raw' G' (suc n)) (y z : fst H')
        → cup (suc n) (EM-raw'→EM G' (suc n) x) (y +ₖ z)
        ≡ cup (suc n) (EM-raw'→EM G' (suc n) x) y +ₖ cup (suc n) (EM-raw'→EM G' (suc n) x) z
    lem zero ind embase-raw y z = refl
    lem zero ind (emloop-raw g i) y z = flipSquare help i
      where
      help : cong (λ g → cup (suc zero) g (y +ₖ z)) (emloop g)
           ≡ cong₂ (_+ₖ_ {n = suc zero})
              (cong (λ g → cup (suc zero) g y) (emloop g)) (cong (λ g → cup (suc zero) g z) (emloop g))
      help = cong (EM→ΩEM+1 zero) (⊗DistR+⊗ g y z)
          ∙∙ EM→ΩEM+1-hom zero (g ⊗ y) (g ⊗ z)
          ∙∙ sym (cong₂+₁ _ _)
    lem (suc n) ind north y z = refl
    lem (suc n) ind south y z = refl
    lem (suc n) ind (merid a i) y z = flipSquare help i
      where
      help : cong (λ g → cup (suc (suc n)) ∣ g ∣ (y +ₖ z)) (merid a)
           ≡ cong₂ (_+ₖ_ {n = suc (suc n)})
              (cong (λ g → cup (suc (suc n)) ∣ g ∣ y) (merid a)) (cong (λ g → cup (suc (suc n)) ∣ g ∣ₕ z) (merid a))
      help = cong (EM→ΩEM+1 (suc n)) (ind (EM-raw→EM _ _ a) y z)
          ∙∙ EM→ΩEM+1-hom (suc n)
              (cup (suc n) (EM-raw→EM _ _ a) y) (cup (suc n) (EM-raw→EM _ _ a) z)
          ∙∙ sym (cong₂+₂ _ _ _)
  main (suc n) (suc m) x y z i = fst (mainDistrL n m y z i) x

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

  main : (n m : ℕ) (x y : EM G' n) (z : EM H' m)
    → ((x +ₖ y) ⌣ₖ z) ≡ (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
  main zero zero = ⊗DistL+⊗
  main zero (suc m) x y =
    EM-raw'-elim _ _ (λ _ → hLevelEM _ (suc m) _ _)
      (lem m (main zero m) x y)
    where
    cup : (m : ℕ) (x : G) → _
    cup m g = cup∙ {G' = G'} {H' = H'} zero m g .fst

    lem : (m : ℕ)
      → ((x y : G) (z : EM H' m) → cup m (x +G y) z ≡ cup m x z +ₖ cup m y z)
      → ((x y : G) (z : EM-raw' H' (suc m))
      → cup (suc m) (x +G y) (EM-raw'→EM _ _ z)
       ≡ cup (suc m) x (EM-raw'→EM _ _ z) +ₖ cup (suc m) y (EM-raw'→EM _ _ z))
    lem zero ind x y embase-raw = refl
    lem zero ind x y (emloop-raw g i) = flipSquare help i
      where
      help : cong (cup 1 (x +G y)) (emloop g)
           ≡ cong₂ _+ₖ_ (cong (cup 1 x) (emloop g))
                        (cong (cup 1 y) (emloop g))
      help = cong emloop (⊗DistL+⊗ x y g)
          ∙∙ emloop-comp _ (x ⊗ g) (y ⊗ g)
          ∙∙ sym (cong₂+₁ _ _)
    lem (suc m) ind x y north = refl
    lem (suc m) ind x y south = refl
    lem (suc m) ind x y (merid a i) = flipSquare help i
      where
      help : cong (cup (suc (suc m)) (x +G y)) (cong ∣_∣ₕ (merid a))
           ≡ cong₂ (_+ₖ_ {n = suc (suc m)})
              (cong (cup (suc (suc m)) x) (cong ∣_∣ₕ (merid a)))
              (cong (cup (suc (suc m)) y) (cong ∣_∣ₕ (merid a)))
      help = cong (EM→ΩEM+1 (suc m)) (ind x y (EM-raw→EM _ _ a))
          ∙∙ EM→ΩEM+1-hom (suc m) (cup (suc m) x (EM-raw→EM _ _ a))
                                   (cup (suc m) y (EM-raw→EM _ _ a))
          ∙∙ sym (cong₂+₂ _ _ _)

  main (suc n) zero =
    EM-elim2 _ (λ _ _ → isOfHLevelΠ (3 + n)
      λ _ → isOfHLevelPath (3 + n) (hLevelEM _ (suc n)) _ _)
      λ x y z → lem n z x y
    where
    cup : (n : ℕ) (x : EM G' n) → _
    cup n x = cup∙ {G' = G'} {H' = H'} n zero x .fst

    lem : (n : ℕ) (z : H) (x y : EM-raw G' (suc n))
      → cup (suc n) (EM-raw→EM _ _ x +ₖ EM-raw→EM _ _ y) z
       ≡ cup (suc n) (EM-raw→EM _ _ x) z +ₖ cup (suc n) (EM-raw→EM _ _ y) z
    lem zero z =
      wedgeConEM.fun _ _ _ _
        (λ _ _ → hLevelEM _ 1 _ _)
        (λ x → cong (λ x → cup 1 x z) (lUnitₖ _ (EM-raw→EM G' 1 x)))
        (λ y → cong (λ x → cup 1 x z) (rUnitₖ _ (EM-raw→EM G' 1 y))
              ∙ sym (rUnitₖ _ (cup 1 (EM-raw→EM G' 1 y) z)))
        (rUnit _)
    lem (suc n) z =
      wedgeConEM.fun _ _ _ _
        (λ _ _ → isOfHLevelPath (2 + n + (2 + n))
                   (subst (λ m → isOfHLevel (suc (suc m))
                                  (EM (G' ⨂ H') (suc (suc n))))
                          (+-comm (suc (suc n)) n)
                          (isOfHLevelPlus' {n = n} (4 + n)
                            (hLevelEM _ (suc (suc n))))) _ _)
        (λ x → cong (λ x → cup (suc (suc n)) x z)
                     (lUnitₖ _ (EM-raw→EM G' _ x))
              ∙ sym (lUnitₖ (suc (suc n)) (cup (suc (suc n))
                    (EM-raw→EM G' (suc (suc n)) x) z)))
        (λ y → cong (λ x → cup (suc (suc n)) x z)
                     (rUnitₖ _ (EM-raw→EM G' _ y))
              ∙ sym (rUnitₖ (suc (suc n)) (cup (suc (suc n))
                     (EM-raw→EM G' (suc (suc n)) y) z)))
        refl
  main (suc n) (suc m) x y z i = fst (mainDistrR n m x y i) z

-- Before proving associativity we state an elimination principle for the associator functions
module _ {ℓ ℓ' ℓ'' ℓ''' : Level} {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
         {L' : AbGroup ℓ''} {K' : AbGroup ℓ'''} where
   private
     G = fst G'
     H = fst H'
     L = fst L'

   assocInd : (n m l : ℕ)
        (f g : (EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ K' ((n +' m) +' l) ∙) ∙)))
     → ((x : EM-raw' G' n) (y : EM-raw' H' m) (z : EM-raw' L' l)
     → fst f (EM-raw'→EM _ n x) .fst (EM-raw'→EM _ m y) .fst (EM-raw'→EM _ l z)
      ≡ fst g (EM-raw'→EM _ n x) .fst (EM-raw'→EM _ m y) .fst (EM-raw'→EM _ l z))
     → f ≡ g
   assocInd n m l f g ind =
     →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)))
       (funExt (EM-raw'-elim _ _
                (λ _ → isOfHLevelPath' (suc n) (isOfHLevel↑∙∙1 n m l) _ _)
         λ x → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
           (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ z → funExt⁻ (cong fst (funExt⁻ (cong fst (flip₁Id y)) z)) x))))
     where
     substFun : ∀ {ℓ} (m l : ℕ) {n r : ℕ} {G : AbGroup ℓ} → n ≡ r → _
     substFun m l {G = G} =
       subst (λ x → isOfHLevel (suc (suc m)) (EM∙ G l →∙ EM∙ K' x))

     substFun' : ∀ {ℓ} (m l : ℕ) {n r : ℕ} {G : AbGroup ℓ} → n ≡ r → _
     substFun' m l {G = G} =
       subst (λ x → isOfHLevel (suc (suc m)) (EM-raw'∙ G l →∙ EM∙ K' x))

     isOfHLevel↑∙∙1 : (n m l : ℕ)
       → isOfHLevel (suc (suc n)) (EM∙ H' m →∙ (EM∙ L' l →∙ EM∙ K' ((n +' m) +' l) ∙))
     isOfHLevel↑∙∙1 n zero zero =
       isOfHLevel→∙ (suc (suc n))
         (isOfHLevel→∙ (2 + n) (subst (λ x → isOfHLevel (2 + n) (EM K' x))
           (+'-comm zero n ∙ +'-comm zero (n +' zero)) (hLevelEM _ n)))
     isOfHLevel↑∙∙1 n zero (suc l) =
       isOfHLevel→∙ (suc (suc n)) (substFun n (suc l)
         ((sym (+-suc n l) ∙ sym (+'≡+ n (suc l)))
         ∙ (λ i → +'-comm zero n i +' suc l))
         (isOfHLevel↑∙ n l))
     isOfHLevel↑∙∙1 n (suc m) zero =
       subst (isOfHLevel (suc (suc n))) (isoToPath flip→∙∙Iso)
         (isOfHLevel→∙ (suc (suc n)) (substFun n (suc m)
               (sym (+-suc n m)
             ∙∙ sym (+'≡+ n (suc m))
             ∙∙ +'-comm zero (n +' suc m))
               (isOfHLevel↑∙ n m)))
     isOfHLevel↑∙∙1 n (suc m) (suc l) =
       subst (λ z → isOfHLevel (suc (suc n))
                     (EM∙ H' (suc m) →∙ (EM∙ L' (suc l) →∙ EM∙ K' z ∙)))
         (cong suc (λ i → +-suc n m (~ i) + l)
                ∙∙ sym (+-suc (n + suc m) l)
                ∙∙ (λ i → +'≡+ (+'≡+ n (suc m) (~ i)) (suc l) (~ i)))
         (isOfHLevel↑∙∙ m l n)

     isOfHLevel↑∙∙2 : (n m l : ℕ)
       → isOfHLevel (suc (suc m))
           (EM∙ L' l →∙ (EM-raw'∙ G' n →∙ EM∙ K' ((n +' m) +' l) ∙))
     isOfHLevel↑∙∙2 zero m zero =
       isOfHLevel→∙ (suc (suc m)) (isOfHLevel→∙ (suc (suc m))
         (subst (λ x → isOfHLevel (suc (suc m)) (EM K' x))
                (+'-comm zero m) (hLevelEM _ m)))
     isOfHLevel↑∙∙2 zero m (suc l) =
       subst (isOfHLevel (suc (suc m))) (isoToPath flip→∙∙Iso)
        (isOfHLevel→∙ (suc (suc m))
         (substFun m (suc l) (sym (+-suc m l) ∙ sym (+'≡+ m (suc l)))
           (isOfHLevel↑∙ m l)))
     isOfHLevel↑∙∙2 (suc n) m zero =
       isOfHLevel→∙ (suc (suc m))
         (substFun' m (suc n)
           (+-comm m (suc n) ∙∙ sym (+'≡+ (suc n) m) ∙∙ +'-comm zero _)
          (isOfHLevel↑∙' m (suc n)))
     isOfHLevel↑∙∙2 (suc n) m (suc l) =
       subst (λ x → isOfHLevel (suc (suc m))
             (EM∙ L' (suc l) →∙ (EM-raw'∙ G' (suc n) →∙ EM∙ K' x ∙)))
             (cong (2 +_) (sym (+-assoc m l n)
                       ∙∙ cong (m +_) (+-comm l n)
                       ∙∙ (+-assoc m n l
                         ∙ cong (_+ l) (+-comm m n)))
           ∙∙ cong suc (sym (+-suc (n + m) l))
           ∙∙ (λ i → +'≡+ (+'≡+ (suc n) m (~ i)) (suc l) (~ i)))
             (isOfHLevel↑∙∙' l n m)

     isOfHLevel↑∙∙3 : (n m l : ℕ)
       → isOfHLevel (suc (suc l))
           (EM-raw'∙ H' m →∙ (EM-raw'∙ G' n →∙ EM∙ K' ((n +' m) +' l) ∙))
     isOfHLevel↑∙∙3 zero zero l =
       isOfHLevel→∙ (suc (suc l)) (isOfHLevel→∙ (suc (suc l)) (hLevelEM _ l))
     isOfHLevel↑∙∙3 zero (suc m) l =
       subst (isOfHLevel (suc (suc l))) (isoToPath flip→∙∙Iso)
         (isOfHLevel→∙ (suc (suc l))
           (substFun' l (suc m) {G = H'} (sym (+'≡+ l (suc m)) ∙ +'-comm l (suc m))
           (isOfHLevel↑∙' l (suc m))))
     isOfHLevel↑∙∙3 (suc n) zero l = isOfHLevel→∙ (suc (suc l))
       (substFun' l (suc n) {G = G'} (+-comm l (suc n) ∙ sym (+'≡+ (suc n) l))
        (isOfHLevel↑∙' l (suc n)))
     isOfHLevel↑∙∙3 (suc n) (suc m) l =
       subst (λ x → isOfHLevel (suc (suc l))
             (EM-raw'∙ H' (suc m) →∙ (EM-raw'∙ G' (suc n) →∙ EM∙ K' x ∙)))
          (cong (λ x → suc (suc x))
            ((sym (+-assoc l m n) ∙ cong (l +_) (+-comm m n)) ∙ +-comm l (n + m))
          ∙ sym (+'≡+ (suc (suc (n + m))) l))
          (isOfHLevel↑∙∙'' m n l)

     flip₁ : (f : (EM∙ G' n →∙ (EM∙ H' m
                            →∙ (EM∙ L' l →∙ EM∙ K' ((n +' m) +' l) ∙) ∙)))
          → EM H' m → (EM∙ L' l
                    →∙ (EM-raw'∙ G' n →∙ EM∙ K' ((n +' m) +' l) ∙))
     fst (fst (flip₁ f y) z) x = fst f (EM-raw'→EM _ _ x) .fst y .fst z
     snd (fst (flip₁ f y) z) =
        (λ i → fst f (EM-raw'→EM∙ G' n i) .fst y .fst z)
       ∙ λ i → snd f i .fst y .fst z
     snd (flip₁ f y) =
       →∙Homogeneous≡ (isHomogeneousEM _)
         (funExt λ z → fst f (EM-raw'→EM G' n z) .fst y .snd)

     flip₂ : (f : (EM∙ G' n →∙ (EM∙ H' m
                            →∙ (EM∙ L' l →∙ EM∙ K' ((n +' m) +' l) ∙) ∙)))
          → EM L' l → EM-raw'∙ H' m
                    →∙ (EM-raw'∙ G' n →∙ EM∙ K' ((n +' m) +' l) ∙)
     fst (fst (flip₂ f z) y) x =
       fst f (EM-raw'→EM _ _ x) .fst (EM-raw'→EM _ _ y) .fst z
     snd (fst (flip₂ f z) y) =
         (λ i → fst f (EM-raw'→EM∙ G' n i) .fst (EM-raw'→EM H' m y) .fst z)
       ∙ λ i → snd f i .fst (EM-raw'→EM H' m y) .fst z
     snd (flip₂ f z) =
       →∙Homogeneous≡ (isHomogeneousEM _)
          ((λ i x → fst f (EM-raw'→EM G' n x) .fst (EM-raw'→EM∙ H' m i) .fst z)
         ∙ λ i x → fst f (EM-raw'→EM G' n x) .snd i .fst z)

     flip₂Id : (x : EM L' l) → flip₂ f x ≡ flip₂ g x
     flip₂Id =
       EM-raw'-elim _ _ (λ _ → isOfHLevelPath' (suc l) (isOfHLevel↑∙∙3 n m l) _ _)
         λ z → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
                 (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
                   (funExt λ x → ind x y z))

     flip₁Id : (x : EM H' m) → flip₁ f x ≡ flip₁ g x
     flip₁Id =
       EM-raw'-elim _ _ (λ _ → isOfHLevelPath' (suc m) (isOfHLevel↑∙∙2 n m l) _ _)
         λ y → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
                 (funExt λ z → →∙Homogeneous≡ (isHomogeneousEM _)
                   (cong fst (funExt⁻ (cong fst (flip₂Id z)) y)))

-- The following three lemmas give associativity as an immediate (but technical) corollary
EM→ΩEM+1-distr₀ₙ : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ)
  → (x : fst G) (y : EM H (suc n))
  → EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = G} {n = 0} {m = suc n} x y)
   ≡ λ i → _⌣ₖ_ {G' = G} {n = 0} {m = suc (suc n)} x (EM→ΩEM+1 (suc n) y i)
EM→ΩEM+1-distr₀ₙ {G = G} {H = H} zero x y =
    rUnit _
    ∙ (λ i → EM→ΩEM+1 1 (_⌣ₖ_ {G' = G} {H' = H} {n = 0} {m = suc zero} x y)
    ∙ sym (EM→ΩEM+1-0ₖ 1 (~ i)))
  ∙ (sym (cong-∙ (_⌣ₖ_ {n = 0} {m = suc (suc zero)} x)
         (cong ∣_∣ₕ (merid y)) (sym (cong ∣_∣ₕ (merid embase)))))
  ∙ cong (cong (_⌣ₖ_ {n = 0} {m = suc (suc zero)} x))
         (sym (cong-∙ ∣_∣ₕ (merid y) (sym (merid embase))))
EM→ΩEM+1-distr₀ₙ {G = G} {H = H} (suc n) x =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n)
                      (isOfHLevelTrunc (5 + n) _ _) _ _)
    λ a → (rUnit _
          ∙ (λ i → EM→ΩEM+1 (suc (suc n))
                     (_⌣ₖ_ {G' = G} {H' = H} {n = 0} {m = suc (suc n)} x ∣ a ∣ₕ)
                   ∙ sym (EM→ΩEM+1-0ₖ (suc (suc n)) (~ i))))
        ∙∙ sym (cong-∙ (_⌣ₖ_ {n = 0} {m = suc (suc (suc n))} x)
               (cong ∣_∣ₕ (merid a)) (sym (cong ∣_∣ₕ (merid north))))
        ∙∙ cong (cong (_⌣ₖ_ {n = 0} {m = suc (suc (suc n))} x))
               (sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid north))))

EM→ΩEM+1-distrₙsuc : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n m : ℕ)
  → (x : EM G (suc n)) (y : EM H (suc m))
  → EM→ΩEM+1 (suc n +' suc m) (_⌣ₖ_ {G' = G} {n = (suc n)} {m = suc m} x y)
   ≡ λ i → _⌣ₖ_ {G' = G} {n = suc (suc n)} {m = suc m} (EM→ΩEM+1 (suc n) x i) y
EM→ΩEM+1-distrₙsuc {G = G} {H = H} n m x = funExt⁻ (cong fst (help n m x))
  where
  fl : (n m : ℕ) (x : EM G (suc n))
    → EM∙ H (suc m) →∙ Ω (EM∙ (G ⨂ H) (suc (suc (suc (n + m)))))
  fst (fl n m x) y =
    EM→ΩEM+1 (suc n +' suc m) (_⌣ₖ_ {G' = G} {n = (suc n)} {m = suc m} x y)
  snd (fl n m x) =
      cong (EM→ΩEM+1 (suc n +' suc m)) (⌣ₖ-0ₖ (suc n) (suc m) x)
    ∙ EM→ΩEM+1-0ₖ (suc n +' suc m)

  fr : (n m : ℕ) (x : EM G (suc n))
    → EM∙ H (suc m) →∙ Ω (EM∙ (G ⨂ H) (suc (suc (suc (n + m)))))
  fst (fr n m x) y i =
    _⌣ₖ_ {G' = G} {n = suc (suc n)} {m = suc m} (EM→ΩEM+1 (suc n) x i) y
  snd (fr n m x) j i =
    ⌣ₖ-0ₖ {G' = G} (suc (suc n)) (suc m) (EM→ΩEM+1 (suc n) x i) j

  hLev : (n m : ℕ)
    → isOfHLevel (3 + n)
        (EM∙ H (suc m) →∙ Ω (EM∙ (G ⨂ H) (suc (suc (suc (n + m))))))
  hLev n m =
    subst (λ x → isOfHLevel (3 + n) (EM∙ H (suc m) →∙ x))
          (EM≃ΩEM+1∙ (suc n +' suc m))
          (isOfHLevel↑∙ (suc n) m)

  help : (n m : ℕ) (x : EM G (suc n)) → fl n m x ≡ fr n m x
  help n m =
    EM-elim (suc n) (λ _ → isOfHLevelPath (3 + n) (hLev n m) _ _)
      λ x → →∙Homogeneous≡ (isHomogeneousPath _ _)
        (funExt (main n x))
   where
   main : (n : ℕ) (x : EM-raw G (suc n)) (y : EM H (suc m))
     → fl n m (EM-raw→EM _ _ x) .fst y ≡ fr n m (EM-raw→EM _ _ x) .fst y
   main zero x y =
         rUnit _
       ∙ (λ i → EM→ΩEM+1 (suc (suc m)) (_⌣ₖ_ {n = suc zero} {m = suc m} x y)
               ∙ sym (EM→ΩEM+1-0ₖ (suc (suc m)) (~ i)))
     ∙∙ sym (cong-∙ (λ x → _⌣ₖ_ {n = (suc (suc zero))} {m = suc m} x y)
            (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid embase))))
     ∙∙ λ j i → _⌣ₖ_ {n = (suc (suc zero))} {m = suc m}
           (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase)) (~ j) i) y
   main (suc n) x y =
       (rUnit _
       ∙ (λ i → EM→ΩEM+1 (suc (suc n) +' suc m)
                 (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ x ∣ₕ y)
              ∙ sym (EM→ΩEM+1-0ₖ _ (~ i))))
     ∙∙ sym (cong-∙ (λ x → _⌣ₖ_ {n = (suc (suc (suc n)))} {m = suc m} x y)
                    (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid north))))
     ∙∙ λ j i → _⌣ₖ_ {n = (suc (suc (suc n)))} {m = suc m}
          (cong-∙ ∣_∣ₕ (merid x) (sym (merid north)) (~ j) i) y

EM→ΩEM+1-distrₙ₀ : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ)
  → (x : fst G) (y : EM H (suc n))
  → EM→ΩEM+1 (suc n) (_⌣ₖ_ {G' = H} {H' = G} {n = suc n} {m = 0} y x)
  ≡ λ i → _⌣ₖ_ {G' = H} {H' = G} {n = suc (suc n)} {m = 0}
                (EM→ΩEM+1 (suc n) y i) x
EM→ΩEM+1-distrₙ₀ {G = G} {H = H} zero x y =
     (rUnit _
   ∙ λ i → EM→ΩEM+1 (suc zero) (_⌣ₖ_ {n = suc zero} {m = zero} y x)
          ∙ sym (EM→ΩEM+1-0ₖ (suc zero) (~ i)))
  ∙∙ sym (cong-∙ (λ y → _⌣ₖ_ {n = (suc (suc zero))} {m = zero} y x)
                 (cong ∣_∣ₕ (merid y)) (cong ∣_∣ₕ (sym (merid embase))))
  ∙∙ λ j i → _⌣ₖ_ {n = suc (suc zero)} {m = 0}
         (cong-∙ ∣_∣ₕ (merid y) (sym (merid embase)) (~ j) i) x
EM→ΩEM+1-distrₙ₀ {G = G} {H = H} (suc n) x =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n)
                      (isOfHLevelTrunc (5 + n) _ _) _ _)
    λ a → (rUnit _
          ∙ λ i → EM→ΩEM+1 (suc (suc n))
                    (_⌣ₖ_ {n = suc (suc n)} {m = zero} ∣ a ∣ₕ x)
                 ∙ sym (EM→ΩEM+1-0ₖ (suc (suc n)) (~ i)))
        ∙∙ sym (cong-∙ (λ y → _⌣ₖ_ {n = (suc (suc (suc n)))} {m = zero} y x)
                       (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (sym (merid north))))
        ∙∙ λ j i → _⌣ₖ_ {n = suc (suc (suc n))} {m = 0}
               (cong-∙ ∣_∣ₕ (merid a) (sym (merid north)) (~ j) i) x

module Assoc {ℓ ℓ' ℓ'' : Level} {G' : AbGroup ℓ}
             {H' : AbGroup ℓ'} {L' : AbGroup ℓ''} where
  private
    G = fst G'
    H = fst H'
    L = fst L'

    -- left associator
    assL : (n m l : ℕ)
      → EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l
                  →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙) ∙)
    fst (fst (fst (assL n m l) x) y) z = (x ⌣ₖ y) ⌣ₖ z
    snd (fst (fst (assL n m l) x) y) = ⌣ₖ-0ₖ (n +' m) l (x ⌣ₖ y)
    snd (fst (assL n m l) x) =
      →∙Homogeneous≡ (isHomogeneousEM _)
        (funExt λ z → (λ i → (⌣ₖ-0ₖ n m x i) ⌣ₖ z) ∙ 0ₖ-⌣ₖ (n +' m) l z)
    snd (assL n m l) =
      →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
        (funExt λ y → →∙Homogeneous≡ (isHomogeneousEM _)
          (funExt (λ z → ((λ i → (0ₖ-⌣ₖ n m y i) ⌣ₖ z)) ∙ 0ₖ-⌣ₖ (n +' m) l z)))

    substAssocLem : ∀ {ℓ} {G : AbGroup ℓ} {n m : ℕ} (p : n ≡ m)
      → subst (EM G) p (0ₖ n) ≡ 0ₖ m
    substAssocLem {G = G} {n = n} =
      J (λ m p → subst (EM G) p (0ₖ n) ≡ 0ₖ m) (transportRefl (0ₖ n))

    preSubstFun : {n m : ℕ} → n ≡ m
      → EM ((G' ⨂ H') ⨂ L') n
      → EM ((G' ⨂ H') ⨂ L') m
    preSubstFun {n = n} {m = m} p = subst (EM ((G' ⨂ H') ⨂ L')) p

    preSubstFunLoop : {n : ℕ} (p : n ≡ n) → (x : _) → preSubstFun p x ≡ x
    preSubstFunLoop p x =
      (λ i → preSubstFun (isSetℕ _ _ p refl i) x) ∙ transportRefl x

    substFun : (n m l : ℕ)
      → EM ((G' ⨂ H') ⨂ L') (n +' (m +' l))
      → EM ((G' ⨂ H') ⨂ L') ((n +' m) +' l)
    substFun n m l = preSubstFun (+'-assoc n m l)

    swapFun : (n m l : ℕ)
      → EM (G' ⨂ (H' ⨂ L')) (n +' (m +' l))
      → EM ((G' ⨂ H') ⨂ L') (n +' (m +' l))
    swapFun n m l = Iso.fun (Iso→EMIso ⨂assoc (n +' (m +' l)))

    -- right associator
    assR : (n m l : ℕ)
      → EM∙ G' n →∙ (EM∙ H' m →∙ (EM∙ L' l
                  →∙ EM∙ ((G' ⨂ H') ⨂ L') ((n +' m) +' l) ∙) ∙)
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

    assocConvert : {n m l : ℕ} → assL n m l ≡ assR n m l
      → (x : EM G' n) (y : EM H' m) (z : EM L' l)
      → cup∙ (n +' m) l (cup∙ n m x .fst y) .fst z
       ≡ substFun n m l (swapFun n m l (cup∙ n (m +' l) x .fst (cup∙ m l y .fst z)))
    assocConvert p x y z i = p i .fst x .fst y .fst z

    -- all the different cases...
    assoc₀₀ₗ : (l : ℕ) → assL zero zero l ≡ assR zero zero l
    assoc₀₀ₗ zero =
      assocInd zero zero zero _ _
        λ x y z → sym (transportRefl (swapFun zero zero zero (x ⊗ (y ⊗ z))))
    assoc₀₀ₗ (suc zero) =
      assocInd zero zero 1 _ _
        λ x y z →
          help x y z
        ∙ sym (transportRefl (swapFun zero zero 1 (x ⌣ₖ (y ⌣ₖ EM-raw'→EM _ _ z))))
      where
      help : (x : G) (y : H) (z : EM-raw' L' 1)
        → (cup∙ 0 1 (cup∙ 0 0 x .fst y) .fst (EM-raw'→EM _ _ z))
         ≡ swapFun zero zero 1  (x ⌣ₖ (y ⌣ₖ (EM-raw'→EM _ _ z)))
      help x y embase-raw = refl
      help x y (emloop-raw g i) = refl
    assoc₀₀ₗ (suc (suc l)) =
      assocInd zero zero (suc (suc l)) _ _
        λ x y z → help (assoc₀₀ₗ (suc l)) x y z
                 ∙ sym (preSubstFunLoop (+'-assoc zero zero (suc (suc l)))
                          ((swapFun zero zero (2 + l)
                            (x ⌣ₖ (y ⌣ₖ EM-raw'→EM _ _ z)))))
      where
      help : assL zero zero (suc l) ≡ assR zero zero (suc l)
        → (x : G) (y : H) (z : EM-raw' L' (suc (suc l)))
        → (cup∙ 0 (suc (suc l)) (cup∙ 0 0 x .fst y) .fst ∣ z ∣ₕ)
         ≡ swapFun zero zero (suc (suc l)) (x ⌣ₖ (y ⌣ₖ ∣ z ∣))
      help p x y north = refl
      help p x y south = refl
      help p x y (merid a i) j = help2 j i
        where
        help2 : EM→ΩEM+1 (suc l)
                 (_⌣ₖ_ {n = 0} (_⌣ₖ_ {n = 0} {m = 0} x y) (EM-raw→EM _ _ a))
              ≡ cong (swapFun zero zero (2 + l))
                 λ i → _⌣ₖ_ {n = 0} {m = suc (suc l)} x
                   (_⌣ₖ_ {n = 0} {m = (suc (suc l))} y ∣ merid a i ∣ₕ)
        help2 = (cong (EM→ΩEM+1 (suc l))
                      (assocConvert p x y (EM-raw→EM L' (suc l) a)
                     ∙ preSubstFunLoop _ (swapFun zero zero (suc l) _))
                ∙ EMFun-EM→ΩEM+1 (suc l) _)
               ∙ cong (cong (swapFun zero zero (2 + l)))
                      (EM→ΩEM+1-distr₀ₙ l x ((_⌣ₖ_ {n = 0} {m = (suc l)} y
                        (EM-raw→EM _ _ a))))

    assoc₀₁ₗ : (l : ℕ) → assL zero 1 l ≡ assR zero 1 l
    assoc₀₁ₗ zero = assocInd zero 1 zero _ _
      λ { x embase-raw z → sym (transportRefl embase)
        ; x (emloop-raw g i) z
          → sym (transportRefl (EM→ΩEM+1 zero ((x ⊗ g) ⊗ z) i))}
    assoc₀₁ₗ (suc l) =
      assocInd zero 1 (suc l) _ _
        λ x y z → help (assoc₀₁ₗ l) z y x
                 ∙ sym (preSubstFunLoop {n = suc (suc l)} (+'-assoc zero 1 (suc l))
                        (swapFun zero (suc zero) (suc l)
                         (_⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l}
                         (EM-raw'→EM _ _ y) (EM-raw'→EM _ _ z)))))
      where
      help : assL zero 1 l ≡ assR zero 1 l
        → (z : EM-raw' L' (suc l)) (y : EM₁-raw (AbGroup→Group H')) (x : fst G')
         → fst (assL zero 1 (suc l))
             (EM-raw'→EM (fst G' , snd G') zero x) .fst
               (EM-raw'→EM H' 1 y) .fst (EM-raw'→EM L' (suc l) z)
         ≡ swapFun zero (suc zero) (suc l)
                   (_⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l}
                    (EM-raw'→EM _ _ y) (EM-raw'→EM _ _ z)))
      help ind z embase-raw x = refl
      help ind z (emloop-raw g i) x = flipSquare help2 i
        where
        help2 : cong (λ y → fst (assL zero 1 (suc l))
                     (EM-raw'→EM (fst G' , snd G') zero x) .fst y .fst
                       (EM-raw'→EM L' (suc l) z)) (emloop g)
              ≡ cong (swapFun zero (suc zero) (suc l))
                λ i → _⌣ₖ_ {n = zero} x (_⌣ₖ_ {n = (suc zero)} {m = suc l}
                  (emloop g i) (EM-raw'→EM _ _ z))
        help2 = cong (EM→ΩEM+1 (suc l))
                     (assocConvert (assoc₀₀ₗ (suc l)) x g (EM-raw'→EM _ _ z)
                    ∙ preSubstFunLoop _
                       (swapFun zero zero (suc l)
                        (cup∙ zero (suc l) x .fst
                         (cup∙ zero (suc l) g .fst (EM-raw'→EM L' (suc l) z)))))
             ∙∙ EMFun-EM→ΩEM+1 (suc l) _
             ∙∙ cong (cong (swapFun zero (suc zero) (suc l)))
                     (EM→ΩEM+1-distr₀ₙ l x
                      (_⌣ₖ_ {n = zero} {m = suc l} g (EM-raw'→EM _ _ z)))

    assoc₀ₘₗ : (n l : ℕ)
      → assL zero (suc n) l ≡ assR zero (suc n) l
      → assL zero (suc (suc n)) l ≡ assR zero (suc (suc n)) l
    assoc₀ₘₗ n zero ind =
      assocInd zero (suc (suc n)) zero _ _
        λ x y z → help x y z
                 ∙ sym (preSubstFunLoop (+'-assoc zero (suc (suc n)) zero)
                       (swapFun zero (suc (suc n)) zero _))
      where
      help : (x : G) (a : EM-raw' H' (suc (suc n))) (z : L)
        → cup∙ _ 0 (cup∙ 0 (suc (suc n)) x .fst ∣ a ∣) .fst z
         ≡ swapFun zero (suc (suc n)) zero
             (_⌣ₖ_ {n = 0} {m = suc (suc n)} x
               (_⌣ₖ_ {n = suc (suc n)} {m = 0} (EM-raw'→EM _ _ a) z))
      help x north z = refl
      help x south z = refl
      help x (merid a i) z = flipSquare main i
        where
        main : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = zero}
                (_⌣ₖ_ {n = zero} {m = suc (suc n)} x ∣ merid a i ∣) z)
           ≡ (cong (swapFun zero (suc (suc n)) zero)
                (λ i → (_⌣ₖ_ {n = 0} {m = suc (suc n)} x
                 (_⌣ₖ_ {n = suc (suc n)} {m = 0} ∣ merid a i ∣ₕ z))))
        main =
             sym (EM→ΩEM+1-distrₙ₀ n z (_⌣ₖ_ {n = zero} {m = suc n}
                   x (EM-raw→EM _ _ a)))
          ∙∙ cong (EM→ΩEM+1 (suc n))
                  (assocConvert ind x (EM-raw→EM H' (suc n) a) z
                ∙ preSubstFunLoop _ (swapFun zero (suc n) zero
                  ((cup∙ zero (suc n) x .fst
                    (cup∙ (suc n) zero (EM-raw→EM H' (suc n) a) .fst z)))))
          ∙∙ (EMFun-EM→ΩEM+1 (suc n) _
            ∙ cong (cong ((swapFun zero (suc (suc n)) zero)))
              (EM→ΩEM+1-distr₀ₙ n x
               (_⌣ₖ_ {n = suc n} {m = zero} (EM-raw→EM _ _ a) z)))
    assoc₀ₘₗ n (suc l) ind =
      assocInd zero (2 + n) (suc l) _ _
        λ x y z → lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc zero (suc (suc n)) (suc l))
                           (swapFun zero (suc (suc n)) (suc l)
                             (x ⌣ₖ (∣ y ∣ ⌣ₖ EM-raw'→EM L' (suc l) z))))
      where
      lem : (x : G) (y : EM-raw' H' (suc (suc n))) (z : EM-raw' L' (suc l))
         → _⌣ₖ_ {n = suc (suc n)} {m = suc l}
            (_⌣ₖ_ {n = zero} {m = suc (suc n)} x ∣ y ∣)
              (EM-raw'→EM L' (suc l) z)
          ≡ swapFun zero (suc (suc n)) (suc l)
             (x ⌣ₖ (∣ y ∣ ⌣ₖ EM-raw'→EM L' (suc l) z))
      lem x north z = refl
      lem x south z = refl
      lem x (merid a i) z = flipSquare main i
        where
        main : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = suc l}
                 (_⌣ₖ_ {n = zero} {m = suc (suc n)} x ∣ merid a i ∣)
                  (EM-raw'→EM _ _ z))
           ≡ (cong (swapFun zero (suc (suc n)) (suc l))
                (λ i → (_⌣ₖ_ {n = 0} {m = suc (suc n) +' suc l} x
                  (_⌣ₖ_ {n = suc (suc n)} {m = suc l} ∣ merid a i ∣ₕ
                   (EM-raw'→EM _ _ z)))))
        main = (λ _ i → EM→ΩEM+1 _
                  (cup∙ 0 (suc n) x .fst ((EM-raw→EM _ _ a))) i
                   ⌣ₖ (EM-raw'→EM _ _ z))
             ∙∙ (sym (EM→ΩEM+1-distrₙsuc n l (cup∙ 0 (suc n) x .fst
                     (EM-raw→EM _ _ a)) (EM-raw'→EM _ _ z))
              ∙ cong (EM→ΩEM+1 (suc (suc (n + l))))
                     (assocConvert ind x (EM-raw→EM _ _ a) (EM-raw'→EM _ _ z)
                    ∙ preSubstFunLoop _
                       (Iso.fun (Iso→EMIso ⨂assoc (suc (suc (n + l)))) _)))
              ∙ (EMFun-EM→ΩEM+1 _ (_⌣ₖ_ {n = zero} {m = suc n +' suc l}
                     x (EM-raw→EM H' (suc n) a ⌣ₖ EM-raw'→EM L' (suc l) z)))
             ∙∙ cong (cong ((swapFun zero (suc (suc n)) (suc l))))
                 (EM→ΩEM+1-distr₀ₙ _ x (_⌣ₖ_ {n = suc n} {m = suc l}
                  (EM-raw→EM _ _ a) (EM-raw'→EM _ _ z)))


    mainAssoc₀ₘₗ : (m l : ℕ) → assL zero m l ≡ assR zero m l
    mainAssoc₀ₘₗ zero = assoc₀₀ₗ
    mainAssoc₀ₘₗ (suc zero) = assoc₀₁ₗ
    mainAssoc₀ₘₗ (suc (suc n)) l = assoc₀ₘₗ n l (mainAssoc₀ₘₗ (suc n) l)

    assoc₁₀ₗ : (l : ℕ) → assL 1 zero l ≡ assR 1 zero l
    assoc₁₀ₗ =
      elim+2 (assocInd 1 zero zero _ _
              λ x y z → l₁ x y z ∙ sym (transportRefl _))
             (assocInd 1 zero 1 _ _
              (λ x y z → l₂ z y x ∙ sym (transportRefl _)))
             λ n ind → assocInd 1 zero (suc (suc n)) _ _
              λ x y z → l₃ n ind x y z ∙ sym (funExt⁻ (lem n) _)
      where
      l₁ : (x : EM-raw' G' 1) (y : H) (z : L)
        → fst (assL 1 zero 0) (EM-raw'→EM G' 1 x)
          .fst (EM-raw'→EM H' zero y)
          .fst (EM-raw'→EM L' zero z)
        ≡ swapFun 1 zero 0 (EM-raw'→EM _ _ x ⌣ₖ (y ⌣ₖ z))
      l₁ embase-raw y z = refl
      l₁ (emloop-raw g i) y z = refl

      l₂ : (z : EM-raw' L' 1) (y : EM-raw' H' zero) (x : EM-raw' G' 1)
        → fst (assL 1 zero 1) (EM-raw'→EM G' 1 x)
          .fst (EM-raw'→EM H' zero y)
          .fst (EM-raw'→EM L' 1 z)
        ≡ swapFun 1 zero 1 (EM-raw'→EM _ _ x ⌣ₖ (y ⌣ₖ EM-raw'→EM _ _ z))
      l₂ z y embase-raw = refl
      l₂ z y (emloop-raw g i) = sym (flipSquare help i)
        where
        help : cong (λ x → swapFun 1 zero 1 (x ⌣ₖ (y ⌣ₖ EM-raw'→EM _ _ z)))
                    (emloop g)
             ≡ cong (λ x → (_⌣ₖ_ {n = suc zero} {m = suc zero}
                    (_⌣ₖ_ {G' = G'} {H' = H'} {n = suc zero} {m = 0} x y)
                     (EM-raw'→EM _ _ z))) (emloop g)
        help = (sym (EMFun-EM→ΩEM+1 (suc zero)
          (cup∙ zero 1 g .fst (cup∙ zero 1 y .fst (EM-raw'→EM _ _ z)))))
             ∙ cong (EM→ΩEM+1 1)
                  (sym (transportRefl _)
                 ∙ sym (funExt⁻ (cong fst (funExt⁻
                    (cong fst (funExt⁻ (cong fst (mainAssoc₀ₘₗ zero 1)) g)) y))
                     (EM-raw'→EM _ _ z)))

      lem : (n : ℕ) → substFun 1 zero (suc (suc n)) ≡ idfun _
      lem n = (λ i → subst (EM ((G' ⨂ H') ⨂ L'))
                       (isSetℕ _ _ (+'-assoc 1 zero (2 + n)) refl i))
            ∙ funExt transportRefl

      l₃ : (n : ℕ) → assL 1 zero (suc n) ≡ assR 1 zero (suc n)
        → (x : EM-raw' G' 1) (y : EM-raw' H' zero)
           (z : EM-raw' L' (suc (suc n)))
        → fst (assL 1 zero (suc (suc n))) (EM-raw'→EM G' 1 x) .fst
            (EM-raw'→EM H' zero y) .fst (EM-raw'→EM L' (suc (suc n)) z)
        ≡ (swapFun 1 zero (suc (suc n))
            (EM-raw'→EM _ _ x ⌣ₖ (y ⌣ₖ ∣ z ∣)))
      l₃ n ind embase-raw y z = refl
      l₃ n ind (emloop-raw g i) y z = flipSquare help i
        where
        help : (λ i → (emloop (g ⊗ y) i ⌣ₖ ∣ z ∣))
             ≡ cong (swapFun 1 zero (suc (suc n)))
               λ i → (emloop g i ⌣ₖ (y ⌣ₖ ∣ z ∣))
        help = cong (EM→ΩEM+1 (suc (suc n)))
                (assocConvert (mainAssoc₀ₘₗ zero (suc (suc n))) g y ∣ z ∣ₕ
                ∙ preSubstFunLoop (+'-assoc zero zero (suc (suc n)))
                   (swapFun zero zero (suc (suc n))
                   (g ⌣ₖ (y ⌣ₖ ∣ z ∣))))
             ∙ (EMFun-EM→ΩEM+1 (suc (suc n))
                   (cup∙ zero (suc (suc n)) g .fst
                    (cup∙ zero (suc (suc n)) y .fst ∣ z ∣)))

    assocₙ₀ₗ : (n l : ℕ)
      → assL n zero l ≡ assR n zero l
      → assL (suc n) zero l ≡ assR (suc n) zero l
    assocₙ₀ₗ zero l ind = assoc₁₀ₗ l
    assocₙ₀ₗ (suc n) zero ind =
      assocInd (suc (suc n)) zero zero _ _
        λ x y z → lem x y z
         ∙ sym (preSubstFunLoop
            (+'-assoc (suc (suc n)) zero zero)
            (swapFun (suc (suc n)) zero zero _))
      where
      lem : (x : EM-raw' G' (suc (suc n))) (y : H) (z : L)
        → fst (assL (suc (suc n)) zero zero)
            (EM-raw'→EM G' (suc (suc n)) x) .fst (EM-raw'→EM H' zero y)
            .fst (EM-raw'→EM L' zero z)
         ≡ _
      lem north y z = refl
      lem south y z = refl
      lem (merid a i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = 0}
                  (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = suc n} {m = zero}
                    (EM-raw→EM _ _ a) y) i) z)
             ≡ cong (swapFun (suc (suc n)) zero zero)
                (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = suc n} {m = zero}
                 (EM-raw→EM _ _ a) (y ⊗ z)))
        help = sym (EM→ΩEM+1-distrₙ₀ _ z
                 (_⌣ₖ_ {n = suc n} {m = zero} (EM-raw→EM _ _ a) y))
             ∙ cong (EM→ΩEM+1 (suc n))
                (assocConvert ind (EM-raw→EM G' (suc n) a) y z
               ∙ preSubstFunLoop _ ((swapFun (suc n) zero zero
                  (_⌣ₖ_ {n = suc n} {m = zero}
                   (EM-raw→EM _ _ a) (y ⊗ z)))))
             ∙ EMFun-EM→ΩEM+1 _ _
    assocₙ₀ₗ (suc n) (suc zero) ind =
      assocInd (suc (suc n)) zero (suc zero) _ _
       λ x y z →
           lem x y z
         ∙ sym (preSubstFunLoop
                (+'-assoc (suc (suc n)) zero (suc zero))
                (swapFun (suc (suc n)) zero (suc zero) _))
      where
      lem : (x : EM-raw' G' (suc (suc n))) (y : H)
            (z : EM-raw' L' (suc zero))
        → fst (assL (suc (suc n)) zero (suc zero))
            (EM-raw'→EM G' (suc (suc n)) x)
             .fst (EM-raw'→EM H' zero y)
              .fst (EM-raw'→EM L' (suc zero) z)
         ≡ _
      lem north y z = refl
      lem south y z = refl
      lem (merid a i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = suc zero}
                 (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = suc n} {m = zero}
                  (EM-raw→EM _ _ a) y) i) (EM-raw'→EM _ _ z))
             ≡ cong (swapFun (suc (suc n)) zero (suc zero))
                (EM→ΩEM+1 (suc n +' suc zero)
                  (cup∙ (suc n) _ (EM-raw→EM _ _ a)
                   .fst (cup∙ zero (suc zero) y
                    .fst (EM-raw'→EM L' (suc zero) z))))
        help = sym (EM→ΩEM+1-distrₙsuc _ _ _
                     (EM-raw'→EM L' (suc zero) z))
            ∙∙ cong (EM→ΩEM+1 (suc n +' suc zero))
                    (assocConvert ind
                     (EM-raw→EM G' (suc n) a) y (EM-raw'→EM L' (suc zero) z)
                  ∙ preSubstFunLoop _ (swapFun (suc n) zero (suc zero) _))
            ∙∙ EMFun-EM→ΩEM+1 _ _
    assocₙ₀ₗ (suc n) (suc (suc l)) ind =
      assocInd (suc (suc n)) zero (suc (suc l)) _ _
        λ x y z →
            lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc (suc (suc n)) zero (suc (suc l))) (swapFun (suc (suc n)) zero (suc (suc l)) _))
      where
      lem : (x : EM-raw' G' (suc (suc n))) (y : H)
            (z : EM-raw' L' (suc (suc l)))
        → fst (assL (suc (suc n)) zero (suc (suc l)))
            (EM-raw'→EM G' (suc (suc n)) x) .fst
             (EM-raw'→EM H' zero y) .fst
              (EM-raw'→EM L' (suc (suc l)) z)
         ≡ _
      lem north y z = refl
      lem south y z = refl
      lem (merid a i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc n)} {m = suc (suc l)}
                 (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = suc n} {m = zero}
                  (EM-raw→EM _ _ a) y) i) (EM-raw'→EM _ _ z))
             ≡ cong (swapFun (suc (suc n)) zero (suc (suc l)))
                (EM→ΩEM+1 (suc n +' suc (suc l))
                  (cup∙ (suc n) _ (EM-raw→EM _ _ a) .fst
                   (cup∙ zero (suc (suc l)) y .fst
                    (EM-raw'→EM L' (suc (suc l)) z))))
        help = sym (EM→ΩEM+1-distrₙsuc _ _ _
                    (EM-raw'→EM L' (suc (suc l)) z))
            ∙∙ cong (EM→ΩEM+1 (suc n +' suc (suc l)))
                    (assocConvert ind
                     (EM-raw→EM G' (suc n) a) y (EM-raw'→EM L' (suc (suc l)) z)
                  ∙ preSubstFunLoop _ (swapFun (suc n) zero (suc (suc l)) _))
            ∙∙ EMFun-EM→ΩEM+1 _ _

    assocₙₘ₀ : (n m : ℕ)
      → assL n (suc m) zero ≡ assR n (suc m) zero
      → assL (suc n) (suc m) zero ≡ assR (suc n) (suc m) zero
    assocₙₘ₀ zero zero ind = assocInd (suc zero) (suc zero) zero _ _
        λ x y z →
            lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc (suc zero) (suc zero) zero) (swapFun (suc zero) (suc zero) zero _))
      where
      lem : (x : EM-raw' G' (suc zero)) (y : EM-raw' H' (suc zero)) (z : L)
        → _ ≡ _
      lem embase-raw y z = refl
      lem (emloop-raw g i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc zero)} {m = zero}
                 (EM→ΩEM+1 (suc zero)
                  (_⌣ₖ_ {n = zero} {m = suc zero} g (EM-raw'→EM _ _ y)) i) z)
             ≡ cong (swapFun 1 1 zero)
                (EM→ΩEM+1 1 (·₀ g 1
                 (_⌣ₖ_ {n = suc zero} {m = zero} (EM-raw'→EM _ _ y) z)))
        help = sym (EM→ΩEM+1-distrₙ₀ zero z
                    (_⌣ₖ_ {n = zero} {m = suc zero} g (EM-raw'→EM _ _ y)))
             ∙ cong (EM→ΩEM+1 1)
                 (assocConvert ind g (EM-raw'→EM _ _ y) z
                ∙ preSubstFunLoop (+'-assoc zero (suc zero) zero)
                  (swapFun zero (suc zero) zero
                  (·₀ g 1 (_⌣ₖ_ {n = suc zero} {m = zero}
                   (EM-raw'→EM _ _ y) z))))
             ∙ EMFun-EM→ΩEM+1 _
                (·₀ g 1 (_⌣ₖ_ {n = suc zero} {m = zero}
                 (EM-raw'→EM _ _ y) z))
    assocₙₘ₀ zero (suc m) ind =
      assocInd (suc zero) (suc (suc m)) zero _ _
        λ x y z →
            lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc (suc zero) (suc (suc m)) zero)
                                 (swapFun (suc zero) (suc (suc m)) zero _))
      where
      lem : (x : EM-raw' G' (suc zero)) (y : EM-raw' H' (suc (suc m))) (z : L)
        → _ ≡ _
      lem embase-raw y z = refl
      lem (emloop-raw g i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc (suc m))} {m = zero}
                (EM→ΩEM+1 _ (_⌣ₖ_ {n = zero} {m = suc (suc m)} g ∣ y ∣ₕ) i) z)
             ≡ cong (swapFun 1 (suc (suc m)) zero)
                (EM→ΩEM+1 (suc (suc m)) (·₀ g (suc (suc m))
                 (_⌣ₖ_ {n = suc (suc m)} {m = zero} ∣ y ∣ₕ z)))
        help = sym (EM→ΩEM+1-distrₙ₀ (suc m) z
                     (_⌣ₖ_ {n = zero} {m = suc (suc m)} g (EM-raw'→EM _ _ y)))
             ∙ cong (EM→ΩEM+1 (suc (suc m)))
                   (assocConvert ind g (EM-raw'→EM _ _ y) z
                  ∙ preSubstFunLoop (+'-assoc zero (suc (suc m)) zero)
                    (swapFun zero (suc (suc m)) zero
                    (·₀ g (suc (suc m)) (_⌣ₖ_ {n = suc (suc m)} {m = zero}
                      ∣ y ∣ₕ z))))
             ∙ EMFun-EM→ΩEM+1 _
                    (·₀ g (suc (suc m)) (_⌣ₖ_ {n = suc (suc m)} {m = zero}
                     ∣ y ∣ₕ z))
    assocₙₘ₀ (suc n) zero ind =
      assocInd (suc (suc n)) (suc zero) zero _ _
        λ x y z →
            lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc (suc (suc n)) (suc zero) zero)
                (swapFun (suc (suc n)) (suc zero) zero _))
      where
      lem : (x : EM-raw' G' (suc (suc n))) (y : EM-raw' H' (suc zero)) (z : L)
       → _ ≡ _
      lem north y z = refl
      lem south y z = refl
      lem (merid a i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc n +' suc zero)} {m = zero}
                 (EM→ΩEM+1 _ (_⌣ₖ_ {n = suc n} {m = suc zero}
                  (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y)) i) z)
             ≡ cong (swapFun (suc (suc n)) (suc zero) zero)
                    (EM→ΩEM+1 (suc (suc (n + 0)))
                      (_⌣ₖ_ {n = suc n} {m = suc zero}
                       (EM-raw→EM _ _ a)
                        (_⌣ₖ_ {n = suc zero} {m = zero} (EM-raw'→EM _ _ y) z)))
        help = sym (EM→ΩEM+1-distrₙ₀ _ z (_⌣ₖ_ {n = suc n} {m = suc zero}
                   (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y)))
            ∙∙ cong (EM→ΩEM+1 (suc (suc (n + 0))))
                    (assocConvert ind (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y) z
                  ∙ preSubstFunLoop _ _)
            ∙∙ EMFun-EM→ΩEM+1 _ _
    assocₙₘ₀ (suc n) (suc m) ind =
      assocInd (suc (suc n)) (suc (suc m)) zero _ _
        λ x y z →
           lem x y z
         ∙ sym (preSubstFunLoop (+'-assoc (suc (suc n)) (suc (suc m)) zero)
               (swapFun (suc (suc n)) (suc (suc m)) zero _))
      where
      lem : (x : EM-raw' G' (suc (suc n))) (y : EM-raw' H' (suc (suc m))) (z : L)
        → _ ≡ _
      lem north y z = refl
      lem south y z = refl
      lem (merid a i) y z = flipSquare help i
        where
        help : (λ i → _⌣ₖ_ {n = suc (suc n +' suc (suc m))} {m = zero}
                 (EM→ΩEM+1 _ (_⌣ₖ_ {n = suc n} {m = suc (suc m)}
                  (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y)) i) z)
             ≡ cong (swapFun (suc (suc n)) (suc (suc m)) zero)
                    (EM→ΩEM+1 (suc n +' (suc (suc m)))
                      (_⌣ₖ_ {n = suc n} {m = suc (suc m)}
                       (EM-raw→EM _ _ a) (_⌣ₖ_ {n = suc (suc m)} {m = zero}
                        (EM-raw'→EM _ _ y) z)))
        help = sym (EM→ΩEM+1-distrₙ₀ _ z (_⌣ₖ_ {n = suc n} {m = suc (suc m)}
                   (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y)))
            ∙∙ cong (EM→ΩEM+1 _)
                    (assocConvert ind (EM-raw→EM _ _ a) (EM-raw'→EM _ _ y) z
                  ∙ preSubstFunLoop _ _)
            ∙∙ EMFun-EM→ΩEM+1 _ _

    assocₙₘₗ₊ : (n m l : ℕ)
      → assL n (suc m) (suc l) ≡ assR n (suc m) (suc l)
      → assL (suc n) (suc m) (suc l) ≡ assR (suc n) (suc m) (suc l)
    assocₙₘₗ₊ zero m l ind =
      assocInd (suc zero) (suc m) (suc l) _ _
        λ x y z →
            lem x y z
          ∙ sym (preSubstFunLoop (+'-assoc (suc zero) (suc m) (suc l))
                                 (swapFun (suc zero) (suc m) (suc l) _))
      where
      lem : (x : EM-raw' G' (suc zero))
            (y : EM-raw' H' (suc m))
            (z : EM-raw' L' (suc l)) → _ ≡ _
      lem embase-raw y z = refl
      lem (emloop-raw g i) y z = flipSquare help i
        where
        help : (λ i → ((_⌣ₖ_ {n = 1} {m = suc m} (emloop g i)
                 (EM-raw'→EM H' (suc m) y)) ⌣ₖ EM-raw'→EM L' (suc l) z))
          ≡ cong (swapFun 1 (suc m) (suc l))
             (EM→ΩEM+1 (suc (suc (m + l)))
              (·₀ g (suc (suc (m + l)))
               (EM-raw'→EM H' (suc m) y ⌣ₖ EM-raw'→EM L' (suc l) z)))
        help = sym (EM→ΩEM+1-distrₙsuc m l
                    (·₀ g (suc m) (EM-raw'→EM H' (suc m) y))
                                  (EM-raw'→EM L' (suc l) z))
            ∙∙ cong (EM→ΩEM+1 (suc (suc (m + l))))
                    (assocConvert ind g
                     (EM-raw'→EM H' (suc m) y) (EM-raw'→EM L' (suc l) z)
                  ∙ preSubstFunLoop _ (swapFun zero (suc m) (suc l)
                      (·₀ g (suc (suc (m + l)))
                       (EM-raw'→EM H' (suc m) y ⌣ₖ EM-raw'→EM L' (suc l) z))))
            ∙∙ EMFun-EM→ΩEM+1 _ _
    assocₙₘₗ₊ (suc n) m l ind =
      assocInd (suc (suc n)) (suc m) (suc l) _ _
        λ { north y z → refl ; south y z → refl
         ; (merid a i) y z → flipSquare (help a y z) i}
      where
      transplem : ∀ {ℓ} {G : AbGroup ℓ} (n m : ℕ) (p : n ≡ m) (x : EM G' (suc n))
        → EM→ΩEM+1 (suc m) (subst (λ x → EM G' (suc x)) p x)
        ≡ cong (subst (λ x → EM G' (suc (suc x))) p) (EM→ΩEM+1 (suc n) x)
      transplem n = J> λ x → cong (EM→ΩEM+1 (suc n)) (transportRefl x)
                 ∙ λ i j → transportRefl (EM→ΩEM+1 (suc n) x j) (~ i)

      help : (a : EM-raw G' (suc n)) (y : EM-raw' H' (suc m))
             (z : EM-raw' L' (suc l))
        → (λ i → _⌣ₖ_ {n = suc (suc n +' suc m)} {m = suc l}
                   (EM→ΩEM+1 _ (cup∙ (suc n) (suc m) (EM-raw→EM _ _ a) .fst
                     (EM-raw'→EM H' (suc m) y)) i)
                   (EM-raw'→EM L' (suc l) z))
         ≡ cong (substFun (suc (suc n)) (suc m) (suc l))
            (cong (swapFun (suc (suc n)) (suc m) (suc l))
              (EM→ΩEM+1 (suc n +' (suc m +' suc l))
                (cup∙ (suc n) (suc m +' suc l) (EM-raw→EM _ _ a) .fst
                 (cup∙ (suc m) (suc l) (EM-raw'→EM H' (suc m) y) .fst
                   (EM-raw'→EM L' (suc l) z)))))
      help a y z =
           sym (EM→ΩEM+1-distrₙsuc _ l
                 (cup∙ (suc n) (suc m) (EM-raw→EM _ _ a) .fst
                   (EM-raw'→EM H' (suc m) y)) (EM-raw'→EM L' (suc l) z))
        ∙∙ cong (EM→ΩEM+1 (suc (suc (suc (n + m + l)))))
            (assocConvert ind (EM-raw→EM _ _ a)
              (EM-raw'→EM H' (suc m) y) (EM-raw'→EM L' (suc l) z))
        ∙∙ (λ i j → transp
              (λ j → EM ((G' ⨂ H') ⨂ L')
                       (suc (+'-assoc (suc n) (suc m) (suc l) (~ i ∨ j)))) (~ i)
                      (EM→ΩEM+1 (+'-assoc (suc n) (suc m) (suc l) (~ i))
                       (transp (λ j → EM ((G' ⨂ H') ⨂ L')
                          (+'-assoc (suc n) (suc m) (suc l) (~ i ∧ j))) i
                         ((swapFun (suc n) (suc m) (suc l)
                          (cup∙ (suc n) (suc (suc (m + l)))
                           (EM-raw→EM G' (suc n) a) .fst
                            (cup∙ (suc m) (suc l)
                             (EM-raw'→EM H' (suc m) y) .fst
                              (EM-raw'→EM L' (suc l) z))))) ) j))
          ∙ cong (cong (substFun (suc (suc n)) (suc m) (suc l)))
                 (EMFun-EM→ΩEM+1 _ _)

    mainAssoc : (n m l : ℕ) → assL n m l ≡ assR n m l
    mainAssoc zero m l = mainAssoc₀ₘₗ m l
    mainAssoc (suc n) zero l = assocₙ₀ₗ n l (mainAssoc n zero l)
    mainAssoc (suc n) (suc m) zero = assocₙₘ₀ n m (mainAssoc n (suc m) zero)
    mainAssoc (suc n) (suc m) (suc l) =
      assocₙₘₗ₊ n m l (mainAssoc n (suc m) (suc l))

  main : (n m l : ℕ) (x : EM G' n) (y : EM H' m) (z : EM L' l)
       → ((x ⌣ₖ y) ⌣ₖ z)
        ≡ subst (EM ((G' ⨂ H') ⨂ L')) (+'-assoc n m l)
          (Iso.fun (Iso→EMIso ⨂assoc (n +' (m +' l)))
            (x ⌣ₖ (y ⌣ₖ z)))
  main n m l = assocConvert (mainAssoc n m l)

-- Miscellaneous lemmas
⌣ₖ-AbGroupHom-Distr : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {G : AbGroup ℓ} {H : AbGroup ℓ'} {G' : AbGroup ℓ''} {H' : AbGroup ℓ'''}
      (ϕ : AbGroupHom G G') (ψ : AbGroupHom H H')
   → (n m : ℕ)
   → (x : EM G n) (y : EM H m)
   → (inducedFun-EM ϕ n x) ⌣ₖ (inducedFun-EM ψ m y)
    ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m) (x ⌣ₖ y)
⌣ₖ-AbGroupHom-Distr ϕ ψ zero zero x y = refl
⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ zero (suc m) x =
  help m (⌣ₖ-AbGroupHom-Distr ϕ ψ zero m x)
  where
  help : (m : ℕ)
    → ((y : EM H m)
       → _⌣ₖ_ {n = zero} (inducedFun-EM ϕ zero x) (inducedFun-EM ψ m y)
        ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) m (_⌣ₖ_ {n = zero} x y))
    → (y : EM H (suc m))
    → (_⌣ₖ_ {n = zero} {m = suc m}
        (inducedFun-EM-raw ϕ zero x) (inducedFun-EM ψ (suc m) y))
     ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc m) (_⌣ₖ_ {n = zero} x y)
  help zero ind = EM-raw'-elim _ _ (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) → refl}
  help (suc m) ind =
    Trunc.elim
      (λ _ → isOfHLevelPath (4 + m) (isOfHLevelTrunc (4 + m)) _ _)
      λ { north → refl
        ; south → refl
        ; (merid a i) → flipSquare (lem a) i}
    where
    lem : (a : EM-raw H (suc m))
      → cong (_⌣ₖ_ {G' = G'} {n = zero} {m = suc (suc m)} (inducedFun-EM ϕ zero x))
              (cong (inducedFun-EM ψ (suc (suc m))) (cong ∣_∣ₕ (merid a)))
        ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc m)))
               (EM→ΩEM+1 (suc m) (_⌣ₖ_ {n = zero} x (EM-raw→EM _ _ a)))
    lem a =
        cong (EM→ΩEM+1 (suc m))
          (cong (_⌣ₖ_ {G' = G'} {n = zero} {m = suc m} (inducedFun-EM ϕ zero x))
            (EM-raw→EM-funct (suc m) ψ a)
        ∙ ind (EM-raw→EM H (suc m) a))
      ∙ EMFun-EM→ΩEM+1 (suc m) (_⌣ₖ_ {n = zero} x (EM-raw→EM _ _ a))
⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ (suc n) zero x y =
  help n (λ x → ⌣ₖ-AbGroupHom-Distr ϕ ψ n zero x y) x
  where
  help : (n : ℕ)
    → ((x : EM G n)
       → _⌣ₖ_ {m = zero} (inducedFun-EM ϕ n x) (inducedFun-EM ψ zero y)
        ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' zero) ((_⌣ₖ_ {n = n} x y)))
    → ((x : EM G (suc n))
       → _⌣ₖ_ {m = zero} (inducedFun-EM ϕ (suc n) x) (inducedFun-EM ψ zero y)
        ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc n) ((_⌣ₖ_ {n = suc n} {m = zero} x y)))
  help zero ind = EM-raw'-elim _ _ (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) → refl}
  help (suc n) ind = Trunc.elim
      (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
      λ { north → refl
        ; south → refl
        ; (merid a i) → flipSquare (lem a) i}
    where
    lem : (a : EM-raw G (suc n)) →
          (λ i → _⌣ₖ_ {n = suc (suc n)} {m = zero}
            (inducedFun-EM ϕ (suc (suc n)) ∣ merid a i ∣ₕ)
            (inducedFun-EM ψ zero y))
        ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc n)))
               (EM→ΩEM+1 (suc n) (_⌣ₖ_ {n = suc n} {m = zero} (EM-raw→EM _ _ a) y))
    lem a = cong (EM→ΩEM+1 (suc n)) ((λ j → (_⌣ₖ_ {n = suc n} {m = zero}
                     (EM-raw→EM-funct (suc n) ϕ a j)
                     (inducedFun-EM ψ zero y)))
                   ∙ ind (EM-raw→EM _ _ a))
         ∙ EMFun-EM→ΩEM+1 (suc n) _
⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ (suc n) (suc m) x =
  funExt⁻ (cong fst (main n m (⌣ₖ-AbGroupHom-Distr ϕ ψ n (suc m)) x))
  where
  fₗ : (n m : ℕ) → EM G n → EM∙ H m →∙ EM∙ (G' ⨂ H') (n +' m)
  fst (fₗ n m x) y = (inducedFun-EM ϕ n x ⌣ₖ inducedFun-EM ψ m y)
  snd (fₗ n m x) =
      (λ i → (inducedFun-EM ϕ n x ⌣ₖ (inducedFun-EM0ₖ {ϕ = ψ} m i)))
    ∙ ⌣ₖ-0ₖ n m (inducedFun-EM ϕ n x)

  fᵣ : (n m : ℕ) → EM G n → EM∙ H m →∙ EM∙ (G' ⨂ H') (n +' m)
  fst (fᵣ n m x) y = inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m) (x ⌣ₖ y)
  snd (fᵣ n m x) = cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m)) (⌣ₖ-0ₖ n m x)
                 ∙ inducedFun-EM0ₖ _

  main : (n m : ℕ)
    → ((x : EM G n) (y : EM H (suc m))
      → fst (fₗ n (suc m) x) y ≡ fst (fᵣ n (suc m) x) y)
    → (x : EM G (suc n)) → fₗ (suc n) (suc m) x ≡ fᵣ (suc n) (suc m) x
  main n m ind =
    EM-raw'-elim _ _ (λ _ → isOfHLevelPath' (2 + n) (isOfHLevel↑∙ (suc n) m) _ _)
      λ x → →∙Homogeneous≡ (isHomogeneousEM _) (funExt (main' n m ind x))
    where
    main' : (n m : ℕ) → ((x : EM G n) (y : EM H (suc m))
       → fst (fₗ n (suc m) x) y ≡ fst (fᵣ n (suc m) x) y)
      →  (x : EM-raw' G (suc n)) (y : EM H (suc m))
      → (inducedFun-EM ϕ (suc n) (EM-raw'→EM _ _ x) ⌣ₖ inducedFun-EM ψ (suc m) y)
       ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc n +' suc m) (EM-raw'→EM _ _ x ⌣ₖ y)
    main' zero m ind embase-raw y = refl
    main' zero m ind (emloop-raw g i) y = flipSquare l i
      where
      l : (λ i → _⌣ₖ_ {n = suc zero} {m = suc m}
                 (inducedFun-EM-raw ϕ 1 (emloop g i))
                 (inducedFun-EM ψ (suc m) y))
        ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc m)))
               (EM→ΩEM+1 (suc m) (_⌣ₖ_ {n = zero} g y))
      l = cong (EM→ΩEM+1 (suc m)) (ind g y)
        ∙ EMFun-EM→ΩEM+1 (suc m) _
    main' (suc n) m ind north y = refl
    main' (suc n) m ind south y = refl
    main' (suc n) m ind (merid a i) y = flipSquare l i
      where
      l : (λ i → (inducedFun-EM ϕ (suc (suc n))
                   (EM-raw'→EM G (suc (suc n)) (merid a i))
                 ⌣ₖ inducedFun-EM ψ (suc m) y))
        ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc n) +' suc m))
               (EM→ΩEM+1 (suc n +' suc m) (EM-raw→EM _ _ a ⌣ₖ y))
      l = cong (EM→ΩEM+1 (suc n +' suc m))
                 (cong (_⌣ₖ inducedFun-EM ψ (suc m) y) (EM-raw→EM-funct (suc n) ϕ a)
               ∙ ind (EM-raw→EM _ _ a) y)
        ∙ EMFun-EM→ΩEM+1 _ _

-- TODO: Graded commutativity, following Cubical.ZCohomology.RingStructure
