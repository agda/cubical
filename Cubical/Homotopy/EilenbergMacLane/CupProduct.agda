{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.CupProduct where

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  renaming (⌣ₖ-comm to ⌣ₖ⊗-comm)

open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Monoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Nat hiding (_·_) renaming (elim to ℕelim ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open RingStr

open PlusBis

private
  variable
    ℓ ℓ' : Level

module _ {G'' : Ring ℓ} where
  private
    G' = Ring→AbGroup G''
    G = fst G'
    _+G_ = _+Gr_ (snd G')

  TensorMult3Homₗ : AbGroupHom ((G' ⨂ G') ⨂ G') G'
  TensorMult3Homₗ =
    compGroupHom (inducedHom⨂ TensorMultHom
                 (idGroupHom {G = (AbGroup→Group G')}))
                 TensorMultHom

  EMTensorMult : (n : ℕ) → EM (G' ⨂ G') n → EM G' n
  EMTensorMult n = inducedFun-EM TensorMultHom n

  EMTensorMult3ₗ : (n : ℕ) → EM ((G' ⨂ G') ⨂ G') n → EM G' n
  EMTensorMult3ₗ n = inducedFun-EM TensorMult3Homₗ n

  EMTensorMultDistrLem : (n m : ℕ) (x : EM (G' ⨂ G') n) (y : EM G' m)
    → EMTensorMult _ (EMTensorMult n x ⌣ₖ⊗ y) ≡ EMTensorMult3ₗ _ (x ⌣ₖ⊗ y)
  EMTensorMultDistrLem n m x y =
      cong (EMTensorMult (n +' m))
        ((λ i → EMTensorMult n x ⌣ₖ⊗ inducedFun-EM-id m y (~ i))
        ∙ ⌣ₖ-AbGroupHom-Distr TensorMultHom idGroupHom n m x y)
    ∙ sym (inducedFun-EM-comp _ _ (n +' m) (x ⌣ₖ⊗ y))

  _⌣ₖ_ : {n m : ℕ} → EM G' n → EM G' m → EM G' (n +' m)
  x ⌣ₖ y = EMTensorMult _ (x ⌣ₖ⊗ y)

  1ₖ : EM G' zero
  1ₖ = 1r (snd G'')

  ⌣ₖ-0ₖ : (n m : ℕ) (x : EM G' n) → (x ⌣ₖ 0ₖ m) ≡ 0ₖ (n +' m)
  ⌣ₖ-0ₖ n m x = cong (EMTensorMult (n +' m)) (⌣ₖ-0ₖ⊗ n m x) ∙ inducedFun-EM0ₖ _

  0ₖ-⌣ₖ : (n m : ℕ) (x : EM G' m) → (0ₖ n ⌣ₖ x) ≡ 0ₖ (n +' m)
  0ₖ-⌣ₖ n m x = cong (EMTensorMult (n +' m)) (0ₖ-⌣ₖ⊗ n m x) ∙ inducedFun-EM0ₖ _

  ⌣ₖ-1ₖ : (n : ℕ) (x : EM G' n) → (x ⌣ₖ 1ₖ) ≡ subst (EM G') (+'-comm zero n) x
  ⌣ₖ-1ₖ n x = cong (EMTensorMult (n +' zero)) (Neutral.⌣ₖ-1ₖ n x)
           ∙∙ sym (substCommSlice (EM (G' ⨂ G')) (EM G')
                   EMTensorMult (+'-comm zero n)
                   (inducedFun-EM (lIncl⨂ 1ₖ) n x))
           ∙∙ cong (subst (EM G') (+'-comm zero n))
                   (sym (inducedFun-EM-comp (lIncl⨂ 1ₖ) TensorMultHom n x)
                 ∙∙ (λ i → inducedFun-EM (G→G⨂G→Gₗ i) n x)
                 ∙∙ inducedFun-EM-id n x)

  1ₖ-⌣ₖ : (m : ℕ) (x : EM G' m) → (_⌣ₖ_ {n = zero} 1ₖ x) ≡ x
  1ₖ-⌣ₖ m x = cong (EMTensorMult m) (Neutral.1ₖ-⌣ₖ m x)
           ∙∙ sym (inducedFun-EM-comp (rIncl⨂ 1ₖ) TensorMultHom m x)
           ∙∙ (λ i → inducedFun-EM (G→G⨂G→Gᵣ i) m x)
            ∙ inducedFun-EM-id m x

  distrR⌣ₖ : (n m : ℕ) (x y : EM G' n) (z : EM G' m)
    → ((x +ₖ y) ⌣ₖ z) ≡ (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
  distrR⌣ₖ n m x y z =
    cong (EMTensorMult (n +' m))
         (RightDistributivity.main n m x y z)
        ∙ inducedFun-EM-pres+ₖ _ (n +' m) _ _

  distrL⌣ₖ : (n m : ℕ) (x : EM G' n) (y z : EM G' m)
    → (x ⌣ₖ (y +ₖ z)) ≡ (x ⌣ₖ y) +ₖ (x ⌣ₖ z)
  distrL⌣ₖ n m x y z =
    cong (EMTensorMult (n +' m))
         (LeftDistributivity.main n m x y z)
        ∙ inducedFun-EM-pres+ₖ _ (n +' m) _ _

  assoc⌣ₖ : (n m l : ℕ) (x : EM G' n) (y : EM G' m) (z : EM G' l)
         → ((x ⌣ₖ y) ⌣ₖ z) ≡ subst (EM G') (+'-assoc n m l) (x ⌣ₖ (y ⌣ₖ z))
  assoc⌣ₖ n m l x y z =
      EMTensorMultDistrLem _ _ (x ⌣ₖ⊗ y) z
    ∙ cong (EMTensorMult3ₗ ((n +' m) +' l)) (Assoc.main n m l x y z)
    ∙ sym (substCommSlice (EM ((G' ⨂ G') ⨂ G')) _
          (EMTensorMult3ₗ)
          (+'-assoc n m l)
          (inducedFun-EM (GroupEquiv→GroupHom ⨂assoc)
            (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z))))
    ∙ cong (subst (EM G') (+'-assoc n m l))
           ((sym (inducedFun-EM-comp _ _ (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z)))
            ∙ λ i → inducedFun-EM (lem i) (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z)))
            ∙ inducedFun-EM-comp
               (inducedHom⨂ idGroupHom TensorMultHom)
               TensorMultHom (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z))
           ∙ cong (inducedFun-EM TensorMultHom (n +' (m +' l)))
               (sym (⌣ₖ-AbGroupHom-Distr idGroupHom TensorMultHom
                       n (m +' l) x (y ⌣ₖ⊗ z))
             ∙ (λ i → inducedFun-EM-id _ x i
                ⌣ₖ⊗ inducedFun-EM TensorMultHom (m +' l) (y ⌣ₖ⊗ z))))
    where
    lem : compGroupHom (GroupEquiv→GroupHom ⨂assoc) TensorMult3Homₗ
         ≡ compGroupHom (inducedHom⨂ idGroupHom TensorMultHom) TensorMultHom
    lem = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
            (funExt (⊗elimProp (λ _ → is-set (snd G') _ _)
              (λ a → ⊗elimProp (λ _ → is-set (snd G') _ _)
                       (λ b c → sym (·Assoc (snd G'') a b c))
                       λ b c ind ind2
                       → cong₂ _+G_ ind ind2
                        ∙ sym (·DistR+ (snd G'') a
                              (fst TensorMultHom b) (fst TensorMultHom c)))
              λ x y ind ind2 → cong₂ _+G_ ind ind2))

-- graded commutativity
module _ {G'' : CommRing ℓ} where
  private
    G' = CommRing→AbGroup G''
    G = fst G'
    _+G_ = _+Gr_ (snd G')

  ⌣ₖ-comm : (n m : ℕ) (x : EM G' n) (y : EM G' m)
           → x ⌣ₖ y ≡ subst (EM G') (+'-comm m n) (-ₖ^[ n · m ] (y ⌣ₖ x))
  ⌣ₖ-comm n m x y =
      cong (EMTensorMult (n +' m)) (⌣ₖ⊗-comm n m x y)
    ∙ sym (substCommSlice (EM (G' ⨂ G')) (EM G')
            EMTensorMult (+'-comm m n)
            (-ₖ^[ n · m ] (comm⨂-EM (m +' n) (y ⌣ₖ⊗ x))))
    ∙ cong (subst (EM G') (+'-comm m n))
        (-ₖ^< n · m >-Induced (m +' n) (evenOrOdd n) (evenOrOdd m) _ _
      ∙ cong (-ₖ^[ n · m ])
        (sym (inducedFun-EM-comp
         (GroupEquiv→GroupHom ⨂-comm) TensorMultHom (m +' n) _)
      ∙ λ i → inducedFun-EM (isTrivComm i) (m +' n) (y ⌣ₖ⊗ x)))

    where
    isTrivComm : compGroupHom (GroupEquiv→GroupHom ⨂-comm)
                  (TensorMultHom {G' = CommRing→Ring G''})
               ≡ TensorMultHom
    isTrivComm =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (⊗elimProp (λ _ → CommRingStr.is-set (snd G'') _ _)
          (λ a b → CommRingStr.·Comm (snd G'') b a)
          λ p q r s → cong₂ _+G_ r s))

⌣[]ₖ-syntax : ∀ {ℓ} {n m : ℕ} (R : Ring ℓ)
  → EM (Ring→AbGroup R) n
  → EM (Ring→AbGroup R) m
  → EM (Ring→AbGroup R) (n +' m)
⌣[]ₖ-syntax R x y = x ⌣ₖ y

⌣[]Cₖ-syntax : ∀ {ℓ} {n m : ℕ} (R : CommRing ℓ)
  → EM (Ring→AbGroup (CommRing→Ring R)) n
  → EM (Ring→AbGroup (CommRing→Ring R)) m
  → EM (Ring→AbGroup (CommRing→Ring R)) (n +' m)
⌣[]Cₖ-syntax R x y = x ⌣ₖ y

⌣[,,]ₖ-syntax : ∀ {ℓ} (n m : ℕ) (R : Ring ℓ)
  → EM (Ring→AbGroup R) n
  → EM (Ring→AbGroup R) m
  → EM (Ring→AbGroup R) (n +' m)
⌣[,,]ₖ-syntax n m R x y = x ⌣ₖ y

⌣[,,]Cₖ-syntax : ∀ {ℓ} (n m : ℕ) (R : CommRing ℓ)
  → EM (Ring→AbGroup (CommRing→Ring R)) n
  → EM (Ring→AbGroup (CommRing→Ring R)) m
  → EM (Ring→AbGroup (CommRing→Ring R)) (n +' m)
⌣[,,]Cₖ-syntax n m R x y = x ⌣ₖ y

syntax ⌣[]ₖ-syntax R x y = x ⌣[ R ]ₖ y
syntax ⌣[]Cₖ-syntax R x y = x ⌣[ R ]Cₖ y
syntax ⌣[,,]ₖ-syntax n m R x y = x ⌣[ R , n , m ]ₖ y
syntax ⌣[,,]Cₖ-syntax n m R x y = x ⌣[ R , n , m ]Cₖ y
