{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.CupProduct where

open import Cubical.Algebra.Group.EilenbergMacLane.Base
  renaming (elim to EM-elim ; elim2 to EM-elim2)
open import Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity
open import Cubical.Algebra.Group.EilenbergMacLane.GroupStructure
open import Cubical.Algebra.Group.EilenbergMacLane.Properties
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.EilenbergMacLane.CupProductTensor renaming
  (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)

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
open import Cubical.Data.Nat hiding (_·_) renaming (elim to ℕelim ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp

open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid.Base

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open CommRingStr
open RingStr
open IsMonoid

open PlusBis

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {G'' : CommRing ℓ} where
  private
    G' : AbGroup ℓ
    G' = Ring→AbGroup (CommRing→Ring G'')

    G = fst G'

    strG = snd G'

    ringStrG = snd (CommRing→Ring G'')

    0G = 0g strG

    _+G_ = _+Gr_ strG

    -G_ = -Gr_ strG

    _·G_ = RingStr._·_ ringStrG

    E = EM G'

  TensorMult : fst (G' ⨂ G') → G
  TensorMult =
    ⨂→AbGroup-elim G'
      (λ x → fst x ·G snd x)
       (RingTheory.0LeftAnnihilates (CommRing→Ring G'') 0G)
       (IsRing.·DistR+ (RingStr.isRing (snd (CommRing→Ring G''))))
       (IsRing.·DistL+ (RingStr.isRing (snd (CommRing→Ring G''))))

  TensorMultHom : AbGroupHom (G' ⨂ G') G'
  fst TensorMultHom = TensorMult
  snd TensorMultHom =
    makeIsGroupHom λ x y → refl

  TensorMult3Homₗ : AbGroupHom ((G' ⨂ G') ⨂ G') G'
  TensorMult3Homₗ =
    compGroupHom (inducedHom⨂ TensorMultHom
                 (idGroupHom {G = (AbGroup→Group G')}))
                 TensorMultHom

  EMTensorMult : (n : ℕ) → EM (G' ⨂ G') n → EM G' n
  EMTensorMult n = inducedFun-EM TensorMultHom n


  EMTensorMult0ₖ : (n : ℕ) → EMTensorMult n (0ₖ n) ≡ 0ₖ n
  EMTensorMult0ₖ zero = RingTheory.0LeftAnnihilates (CommRing→Ring G'') 0G
  EMTensorMult0ₖ (suc zero) = refl
  EMTensorMult0ₖ (suc (suc n)) = refl


  EMTensorMultPres+ : (n : ℕ) (x y : EM (G' ⨂ G') n)
    → EMTensorMult n (x +ₖ y) ≡ EMTensorMult n x +ₖ EMTensorMult n y
  EMTensorMultPres+ zero x y = refl
  EMTensorMultPres+ (suc zero) =
    EM-elim2 _ (λ _ _ → isOfHLevelPath 3 (hLevelEM _ 1) _ _)
      (wedgeConEM.fun (G' ⨂ G') (G' ⨂ G') 0 0
        (λ _ _ → emsquash _ _)
        (λ y → cong (EMTensorMult 1) (lUnitₖ _ (EM-raw→EM (G' ⨂ G') 1 y)))
        (λ x → cong (EMTensorMult 1) (rUnitₖ _ (EM-raw→EM (G' ⨂ G') 1 x))
             ∙ sym (rUnitₖ _ (EMTensorMult 1 (EM-raw→EM (G' ⨂ G') 1 x))))
        (rUnit _))
  EMTensorMultPres+ (suc (suc n)) =
    EM-elim2 _ (λ _ _ → isOfHLevelPath (4 +ℕ n) (hLevelEM _ (suc (suc n))) _ _)
      (wedgeConEM.fun (G' ⨂ G') (G' ⨂ G') _ _
        (λ _ _ → isOfHLevelPath ((suc (suc n)) +ℕ (suc (suc n)))
                  (subst (λ m → isOfHLevel m (EM G' (suc (suc n))))
                    (cong (suc ∘ suc) (+-comm (suc (suc n)) n))
                    (isOfHLevelPlus' {n = n} (4 +ℕ n)
                     (hLevelEM _ (suc (suc n))))) _ _)
        (λ x → cong (EMTensorMult (suc (suc n)))
                     (lUnitₖ _ (EM-raw→EM (G' ⨂ G') (suc (suc n)) x))
             ∙ sym (lUnitₖ _ (EMTensorMult (suc (suc n))
                   (EM-raw→EM (G' ⨂ G') (suc (suc n)) x))))
        (λ x → cong (EMTensorMult (suc (suc n)))
                     (rUnitₖ _ (EM-raw→EM (G' ⨂ G') (suc (suc n)) x))
             ∙ sym (rUnitₖ _ (EMTensorMult (suc (suc n))
                   (EM-raw→EM (G' ⨂ G') (suc (suc n)) x))))
        refl)

  EMTensorMult3ₗ : (n : ℕ) → EM ((G' ⨂ G') ⨂ G') n → EM G' n
  EMTensorMult3ₗ n = inducedFun-EM TensorMult3Homₗ n

  EMTensorMult3ₗ0ₖ : (n : ℕ) → EMTensorMult3ₗ n (0ₖ n) ≡ 0ₖ n
  EMTensorMult3ₗ0ₖ zero = RingTheory.0RightAnnihilates (CommRing→Ring G'') (0G ·G 0G)
  EMTensorMult3ₗ0ₖ (suc zero) = refl
  EMTensorMult3ₗ0ₖ (suc (suc n)) = refl

  EMFun-EM→ΩEM+1 : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} {ϕ : AbGroupHom G H} (n : ℕ) (x : EM G n)
    → PathP (λ i → inducedFun-EM0ₖ {ϕ = ϕ} (suc n) (~ i)
                   ≡ inducedFun-EM0ₖ {ϕ = ϕ} (suc n) (~ i))
             (EM→ΩEM+1 n (inducedFun-EM ϕ n x))
             (cong (inducedFun-EM ϕ (suc n)) (EM→ΩEM+1 n x))
  EMFun-EM→ΩEM+1 {ϕ = ϕ} zero x = refl
  EMFun-EM→ΩEM+1 {ϕ = ϕ} (suc zero) x =
    cong-∙ ∣_∣ₕ (merid (inducedFun-EM ϕ (suc zero) x)) (sym (merid embase))
    ∙∙ sym (cong-∙ (inducedFun-EM ϕ (suc (suc zero))) (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid embase))))
    ∙∙ cong (cong (inducedFun-EM ϕ (suc (suc zero)))) (sym (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase)))) --
  EMFun-EM→ΩEM+1 {ϕ = ϕ} (suc (suc n)) =
    Trunc.elim (λ _ → isOfHLevelPath (4 +ℕ n) (isOfHLevelTrunc (5 +ℕ n) _ _) _ _)
      λ a → cong-∙ ∣_∣ₕ (merid (inducedFun-EM-raw ϕ (2 +ℕ n) a)) (sym (merid north))
          ∙∙ sym (cong-∙ (inducedFun-EM ϕ (suc (suc (suc n)))) (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (sym (merid north))))
          ∙∙ cong (cong (inducedFun-EM ϕ (suc (suc (suc n))))) (sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid north))))

  EM-raw→EM-funct : ∀ {ℓ ℓ'} {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ) (ψ : AbGroupHom G H)
    → (y : EM-raw G n)
    → EM-raw→EM _ _ (inducedFun-EM-raw ψ n y) ≡ inducedFun-EM ψ n (EM-raw→EM _ _ y)
  EM-raw→EM-funct zero ψ y = refl
  EM-raw→EM-funct (suc zero) ψ y = refl
  EM-raw→EM-funct (suc (suc n)) ψ y = refl

  ⌣ₖ-AbGroupHom-Distr : ∀ {ℓ ℓ' ℓ'' ℓ'''} {G : AbGroup ℓ} {H : AbGroup ℓ'} {G' : AbGroup ℓ''} {H' : AbGroup ℓ'''}
            (ϕ : AbGroupHom G G') (ψ : AbGroupHom H H')
         → (n m : ℕ)
         → (x : EM G n) (y : EM H m)
         → (inducedFun-EM ϕ n x) ⌣ₖ⊗ (inducedFun-EM ψ m y)
          ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m) (x ⌣ₖ⊗ y)
  ⌣ₖ-AbGroupHom-Distr ϕ ψ zero zero x y = refl
  ⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ zero (suc m) x =
    help m (⌣ₖ-AbGroupHom-Distr ϕ ψ zero m x)
    where
    help : (m : ℕ)
      → ((y : EM H m)
         → _⌣ₖ⊗_ {n = zero} (inducedFun-EM ϕ zero x) (inducedFun-EM ψ m y)
          ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) m (_⌣ₖ⊗_ {n = zero} x y))
      → (y : EM H (suc m))
      → (_⌣ₖ⊗_ {n = zero} {m = suc m} (inducedFun-EM-raw ϕ zero x) (inducedFun-EM ψ (suc m) y))
       ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc m) (_⌣ₖ⊗_ {n = zero} x y)
    help zero ind = EM-rawer-elim _ _ (λ _ → hLevelEM _ 1 _ _)
      λ { embase-raw → refl ; (emloop-raw g i) → refl}
    help (suc m) ind =
      Trunc.elim
        (λ _ → isOfHLevelPath (4 +ℕ m) (isOfHLevelTrunc (4 +ℕ m)) _ _)
        λ { north → refl
          ; south → refl
          ; (merid a i) → flipSquare (lem a) i}
      where
      lem : (a : EM-raw H (suc m))
        → cong (_⌣ₖ⊗_ {G' = G'} {n = zero} {m = suc (suc m)} (inducedFun-EM ϕ zero x))
                (cong (inducedFun-EM ψ (suc (suc m))) (cong ∣_∣ₕ (merid a)))
          ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc m)))
                 (EM→ΩEM+1 (suc m) (_⌣ₖ⊗_ {n = zero} x (EM-raw→EM _ _ a)))
      lem a =
          cong (EM→ΩEM+1 (suc m))
            (cong (_⌣ₖ⊗_ {G' = G'} {n = zero} {m = suc m} (inducedFun-EM ϕ zero x))
              (EM-raw→EM-funct (suc m) ψ a)
          ∙ ind (EM-raw→EM H (suc m) a))
        ∙ EMFun-EM→ΩEM+1 (suc m) (_⌣ₖ⊗_ {n = zero} x (EM-raw→EM _ _ a))
  ⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ (suc n) zero x y =
    help n (λ x → ⌣ₖ-AbGroupHom-Distr ϕ ψ n zero x y) x
    where
    help : (n : ℕ)
      → ((x : EM G n)
         → _⌣ₖ⊗_ {m = zero} (inducedFun-EM ϕ n x) (inducedFun-EM ψ zero y)
          ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' zero) ((_⌣ₖ⊗_ {n = n} x y)))
      → ((x : EM G (suc n))
         → _⌣ₖ⊗_ {m = zero} (inducedFun-EM ϕ (suc n) x) (inducedFun-EM ψ zero y)
          ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc n) ((_⌣ₖ⊗_ {n = suc n} {m = zero} x y)))
    help zero ind = EM-rawer-elim _ _ (λ _ → hLevelEM _ 1 _ _)
      λ { embase-raw → refl ; (emloop-raw g i) → refl}
    help (suc n) ind = Trunc.elim
        (λ _ → isOfHLevelPath (4 +ℕ n) (isOfHLevelTrunc (4 +ℕ n)) _ _)
        λ { north → refl
          ; south → refl
          ; (merid a i) → flipSquare (lem a) i}
      where
      lem : (a : EM-raw G (suc n)) →
            (λ i → _⌣ₖ⊗_ {n = suc (suc n)} {m = zero}
              (inducedFun-EM ϕ (suc (suc n)) ∣ merid a i ∣ₕ)
              (inducedFun-EM ψ zero y))
          ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc n)))
                 (EM→ΩEM+1 (suc n) (_⌣ₖ⊗_ {n = suc n} {m = zero} (EM-raw→EM _ _ a) y))
      lem a = cong (EM→ΩEM+1 (suc n)) ((λ j → (_⌣ₖ⊗_ {n = suc n} {m = zero}
                       (EM-raw→EM-funct (suc n) ϕ a j)
                       (inducedFun-EM ψ zero y)))
                     ∙ ind (EM-raw→EM _ _ a))
           ∙ EMFun-EM→ΩEM+1 (suc n) _
  ⌣ₖ-AbGroupHom-Distr {G = G} {H = H} {G' = G'} {H' = H'} ϕ ψ (suc n) (suc m) x =
    funExt⁻ (cong fst (main n m (⌣ₖ-AbGroupHom-Distr ϕ ψ n (suc m)) x))
    where
    fₗ : (n m : ℕ) → EM G n → EM∙ H m →∙ EM∙ (G' ⨂ H') (n +' m)
    fst (fₗ n m x) y = (inducedFun-EM ϕ n x ⌣ₖ⊗ inducedFun-EM ψ m y)
    snd (fₗ n m x) =
        (λ i → (inducedFun-EM ϕ n x ⌣ₖ⊗ (inducedFun-EM0ₖ {ϕ = ψ} m i)))
      ∙ ⌣ₖ-0ₖ⊗ n m (inducedFun-EM ϕ n x)

    fᵣ : (n m : ℕ) → EM G n → EM∙ H m →∙ EM∙ (G' ⨂ H') (n +' m)
    fst (fᵣ n m x) y = inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m) (x ⌣ₖ⊗ y)
    snd (fᵣ n m x) = cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (n +' m)) (⌣ₖ-0ₖ⊗ n m x)
                   ∙ inducedFun-EM0ₖ _

    main : (n m : ℕ)
      → ((x : EM G n) (y : EM H (suc m)) → fst (fₗ n (suc m) x) y ≡ fst (fᵣ n (suc m) x) y)
      → (x : EM G (suc n)) → fₗ (suc n) (suc m) x ≡ fᵣ (suc n) (suc m) x
    main n m ind =
      EM-rawer-elim _ _ (λ _ → isOfHLevelPath' (2 +ℕ n) (isOfHLevel↑∙ (suc n) m) _ _)
        λ x → →∙Homogeneous≡ (isHomogeneousEM _) (funExt (main' n m ind x))
      where
      main' : (n m : ℕ) → ((x : EM G n) (y : EM H (suc m)) → fst (fₗ n (suc m) x) y ≡ fst (fᵣ n (suc m) x) y)
        →  (x : EM-rawer G (suc n)) (y : EM H (suc m))
          → (inducedFun-EM ϕ (suc n) (EM-rawer→EM _ _ x) ⌣ₖ⊗ inducedFun-EM ψ (suc m) y)
           ≡ inducedFun-EM (inducedHom⨂ ϕ ψ) (suc n +' suc m) (EM-rawer→EM _ _ x ⌣ₖ⊗ y)
      main' zero m ind embase-raw y = refl
      main' zero m ind (emloop-raw g i) y = flipSquare l i
        where
        l : (λ i → _⌣ₖ⊗_ {n = suc zero} {m = suc m} (inducedFun-EM-raw ϕ 1 (emloop g i)) (inducedFun-EM ψ (suc m) y))
          ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc m))) (EM→ΩEM+1 (suc m) (_⌣ₖ⊗_ {n = zero} g y))
        l = cong (EM→ΩEM+1 (suc m)) (ind g y)
          ∙ EMFun-EM→ΩEM+1 (suc m) _
      main' (suc n) m ind north y = refl
      main' (suc n) m ind south y = refl
      main' (suc n) m ind (merid a i) y = flipSquare l i
        where
        l : (λ i → (inducedFun-EM ϕ (suc (suc n))
                     (EM-rawer→EM G (suc (suc n)) (merid a i)) ⌣ₖ⊗ inducedFun-EM ψ (suc m) y))
          ≡ cong (inducedFun-EM (inducedHom⨂ ϕ ψ) (suc (suc n) +' suc m))
                 (EM→ΩEM+1 (suc n +' suc m) (EM-raw→EM _ _ a ⌣ₖ⊗ y))
        l = cong (EM→ΩEM+1 (suc n +' suc m))
                   (cong (_⌣ₖ⊗ inducedFun-EM ψ (suc m) y) (EM-raw→EM-funct (suc n) ϕ a)
                 ∙ ind (EM-raw→EM _ _ a) y)
          ∙ EMFun-EM→ΩEM+1 _ _

  lem : (n m : ℕ) (x : EM (G' ⨂ G') n) (y : E m)
    → EMTensorMult _ ((EMTensorMult n x ⌣ₖ⊗ y)) ≡ EMTensorMult3ₗ _ (x ⌣ₖ⊗ y)
  lem n m x y =
      cong (EMTensorMult (n +' m))
        ((λ i → EMTensorMult n x ⌣ₖ⊗ inducedFun-EM-id m y (~ i))
        ∙ ⌣ₖ-AbGroupHom-Distr TensorMultHom idGroupHom n m x y)
    ∙ sym (inducedFun-EM-comp _ _ (n +' m) (x ⌣ₖ⊗ y))

  _⌣ₖ_ : {n m : ℕ} → EM G' n → EM G' m → EM G' (n +' m)
  x ⌣ₖ y = EMTensorMult _ (x ⌣ₖ⊗ y)

  ⌣ₖ-0ₖ : (n m : ℕ) (x : EM G' n) → (x ⌣ₖ 0ₖ m) ≡ 0ₖ (n +' m)
  ⌣ₖ-0ₖ n m x = cong (EMTensorMult (n +' m)) (⌣ₖ-0ₖ⊗ n m x) ∙ EMTensorMult0ₖ _

  0ₖ-⌣ₖ : (n m : ℕ) (x : EM G' m) → (0ₖ n ⌣ₖ x) ≡ 0ₖ (n +' m)
  0ₖ-⌣ₖ n m x = cong (EMTensorMult (n +' m)) (0ₖ-⌣ₖ⊗ n m x) ∙ EMTensorMult0ₖ _

  distrR⌣ₖ : (n m : ℕ) (x y : EM G' n) (z : EM G' m) → ((x +ₖ y) ⌣ₖ z) ≡ (x ⌣ₖ z) +ₖ (y ⌣ₖ z)
  distrR⌣ₖ n m x y z = cong (EMTensorMult (n +' m)) (RightDistributivity.main n m x y z)
                     ∙ EMTensorMultPres+ (n +' m) _ _

  distrL⌣ₖ : (n m : ℕ) (x : EM G' n) (y z : EM G' m) → (x ⌣ₖ (y +ₖ z)) ≡ (x ⌣ₖ y) +ₖ (x ⌣ₖ z)
  distrL⌣ₖ n m x y z = cong (EMTensorMult (n +' m)) (LeftDistributivity.main n m x y z)
                     ∙ EMTensorMultPres+ (n +' m) _ _

  assoc⌣ₖ : (n m l : ℕ) (x : EM G' n) (y : EM G' m) (z : EM G' l)
         → ((x ⌣ₖ y) ⌣ₖ z) ≡ subst (EM G') (+'-assoc n m l) (x ⌣ₖ (y ⌣ₖ z))
  assoc⌣ₖ n m l x y z =
      lem _ _ (x ⌣ₖ⊗ y) z
    ∙ cong (EMTensorMult3ₗ ((n +' m) +' l)) (Assoc.main n m l x y z)
    ∙ sym (substCommSlice (EM ((G' ⨂ G') ⨂ G')) _
          (EMTensorMult3ₗ)
          (+'-assoc n m l)
          (inducedFun-EM (GroupEquiv→GroupHom ⨂assoc)
            (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z))))
    ∙ cong (subst (EM G') (+'-assoc n m l))
           ((((sym (inducedFun-EM-comp _ _ (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z)))
            ∙ λ i → inducedFun-EM (lem2 i) (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z)))
            ∙ inducedFun-EM-comp
               (inducedHom⨂ idGroupHom TensorMultHom)
               TensorMultHom (n +' (m +' l)) (x ⌣ₖ⊗ (y ⌣ₖ⊗ z)))
           ∙ cong (inducedFun-EM TensorMultHom (n +' (m +' l)))
               (sym (⌣ₖ-AbGroupHom-Distr idGroupHom TensorMultHom n (m +' l) x (y ⌣ₖ⊗ z))
             ∙ (λ i → inducedFun-EM-id _ x i ⌣ₖ⊗ inducedFun-EM TensorMultHom (m +' l) (y ⌣ₖ⊗ z))))
          ∙ λ i → inducedFun-EM TensorMultHom _ (x ⌣ₖ⊗ inducedFun-EM TensorMultHom _ (y ⌣ₖ⊗ z)))
    where
    lem2 : compGroupHom (GroupEquiv→GroupHom ⨂assoc) TensorMult3Homₗ
         ≡ compGroupHom (inducedHom⨂ idGroupHom TensorMultHom) TensorMultHom
    lem2 = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
            (funExt (⊗elimProp (λ _ → is-set strG _ _)
              (λ a → ⊗elimProp (λ _ → is-set strG _ _)
                       (λ b c → sym (·Assoc ringStrG a b c))
                       λ b c ind ind2 → cong₂ _+G_ ind ind2
                                     ∙ sym (·DistR+ ringStrG a (fst TensorMultHom b) (fst TensorMultHom c)))
              λ x y ind ind2 → cong₂ _+G_ ind ind2))
