{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.RingLaws where
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.RingStructure.CupProduct

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.Truncation renaming (elim to trElim)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Int
  renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +Comm to +ℤ-comm
          ; ·Comm to ∙-comm ; +Assoc to ℤ+-assoc ; -_ to -ℤ_)
    hiding (_+'_ ; +'≡+)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

-- Some boring lemmas
·₀≡·ℤ : (x y : ℤ) → _·₀_ {n = zero} x y ≡ x ℤ∙ y
·₀≡·ℤ (pos zero) y = refl
·₀≡·ℤ (pos (suc n)) y = cong (y ℤ+_) (·₀≡·ℤ (pos n) y)
·₀≡·ℤ (negsuc zero) (pos zero) = refl
·₀≡·ℤ (negsuc zero) (pos (suc n)) = -AntiComm 0 (pos (suc n))
·₀≡·ℤ (negsuc zero) (negsuc n) = -AntiComm 0 (negsuc n)
·₀≡·ℤ (negsuc (suc n)) (pos m) =
   (cong ((_ℤ+ (pos 0 - pos m))) (·₀≡·ℤ (negsuc n) (pos m))
  ∙ cong ((negsuc n ℤ∙ (pos m)) ℤ+_)
         (-AntiComm 0 (pos m) ∙ cong (-ℤ_) (help m)))
  ∙ sym (+ℤ-comm (-ℤ (pos m)) (negsuc n ℤ∙ (pos m)))
    where
    help : (m : ℕ) → (pos m - 0) ≡ pos m
    help zero = refl
    help (suc m) = refl
·₀≡·ℤ (negsuc (suc n)) (negsuc m) =
     +ℤ-comm (_·₀_{n = zero} (negsuc n) (negsuc m)) (pos 0 - (negsuc m))
  ∙∙ cong ((pos 0 - negsuc m) ℤ+_) (·₀≡·ℤ (negsuc n) (negsuc m))
  ∙∙ cong (_ℤ+ (negsuc n ℤ∙ negsuc m)) (help m)
    where
    help : (m : ℕ) → (pos 0 - negsuc m) ≡ pos (suc m)
    help zero = refl
    help (suc n) = cong sucℤ (help n)

comm-·₀ : (x y : ℤ) → _·₀_ {n = 0} x y ≡ y ·₀ x
comm-·₀ x y = ·₀≡·ℤ x y ∙∙ ∙-comm x y ∙∙ sym (·₀≡·ℤ y x)

+'-assoc : (n m l : ℕ) → (n +' (m +' l)) ≡ ((n +' m) +' l)
+'-assoc n m l =
     (λ i → +'≡+ n (+'≡+ m l i) i)
  ∙∙ +-assoc n m l
  ∙∙ (λ i → +'≡+ (+'≡+ n m (~ i)) l (~ i))

-- Zero multiplication

⌣ₖ-0ₖ : (n m : ℕ) → (x : coHomK n)
        → x ⌣ₖ (0ₖ _) ≡ 0ₖ _
⌣ₖ-0ₖ  n m x = snd (⌣ₖ∙ n m x)

0ₖ-⌣ₖ : (n m : ℕ) → (x : coHomK m) →
        (0ₖ _) ⌣ₖ x ≡ 0ₖ _
0ₖ-⌣ₖ n m = funExt⁻ (cong fst (snd (⌣ₖ∙∙ n m)))

⌣ₖ-0ₖ≡0ₖ-⌣ₖ : (n m : ℕ) → ⌣ₖ-0ₖ n m (0ₖ _) ≡ 0ₖ-⌣ₖ n m (0ₖ _)
⌣ₖ-0ₖ≡0ₖ-⌣ₖ zero zero = refl
⌣ₖ-0ₖ≡0ₖ-⌣ₖ zero (suc m) = refl
⌣ₖ-0ₖ≡0ₖ-⌣ₖ (suc n) zero = refl
⌣ₖ-0ₖ≡0ₖ-⌣ₖ (suc zero) (suc m) = refl
⌣ₖ-0ₖ≡0ₖ-⌣ₖ (suc (suc n)) (suc m) = refl

-- Left distributivity

private
  ⌣ₖ-distrFun : -- z ⌣ₖ (x +ₖ y)
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (m +' n)
  fst (⌣ₖ-distrFun n m x y) z =
    z ⌣ₖ (x +ₖ y)
  snd (⌣ₖ-distrFun n m x y) =
    0ₖ-⌣ₖ m n (x +ₖ y)

  ⌣ₖ-distrFun2 : -- z ⌣ₖ x +ₖ z ⌣ₖ y
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (m +' n)
  fst (⌣ₖ-distrFun2 n m x y) z =
    z ⌣ₖ x +ₖ z ⌣ₖ y
  snd (⌣ₖ-distrFun2 n m x y) =
    cong₂ _+ₖ_ (0ₖ-⌣ₖ m n x) (0ₖ-⌣ₖ m n y) ∙ rUnitₖ _ _

  leftDistr-⌣ₖ· : (n m : ℕ) (x y : coHomK (suc n)) → ⌣ₖ-distrFun (suc n) (suc m) x y ≡ ⌣ₖ-distrFun2 (suc n) (suc m) x y
  leftDistr-⌣ₖ· n m =
    elim2 (λ _ _ → isOfHLevelSuc (2 + n) (hLevHelp n m _ _))
          main
    where
    hLevHelp : (n m : ℕ) (x y : _) → isOfHLevel (2 + n) ( ⌣ₖ-distrFun (suc n) (suc m) x y ≡ ⌣ₖ-distrFun2 (suc n) (suc m) x y)
    hLevHelp n m x y =
      (subst (isOfHLevel (3 + n))
        (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (+-comm n m i)))))
          (isOfHLevel↑∙ (suc n) m)) _ _

    left-fst : (n : ℕ) (x : S₊ (suc n)) →
      fst (⌣ₖ-distrFun (suc n) (suc m) ∣ ptSn (suc n) ∣ ∣ x ∣) ≡
      fst (⌣ₖ-distrFun2 (suc n) (suc m) ∣ ptSn (suc n) ∣ ∣ x ∣)
    left-fst zero y =
        (funExt (λ z → sym (lUnitₖ _ (z ⌣ₖ ∣ y ∣)) ∙ λ i → ⌣ₖ-0ₖ _ _ z (~ i) +ₖ z ⌣ₖ ∣ y ∣))
    left-fst (suc n) y =
        (funExt (λ z → sym (lUnitₖ _ (z ⌣ₖ ∣ y ∣)) ∙ λ i → ⌣ₖ-0ₖ _ _ z (~ i) +ₖ z ⌣ₖ ∣ y ∣))

    right-fst : (n : ℕ) (x : S₊ (suc n)) →
      fst (⌣ₖ-distrFun (suc n) (suc m) ∣ x ∣ (0ₖ _)) ≡
      fst (⌣ₖ-distrFun2 (suc n) (suc m) ∣ x ∣ (0ₖ _))
    right-fst n x = funExt (λ z → (cong (z ⌣ₖ_) (rUnitₖ _ ∣ x ∣) ∙∙ sym (rUnitₖ _ _) ∙∙ λ i → z ⌣ₖ ∣ x ∣ +ₖ ⌣ₖ-0ₖ _ (suc n) z (~ i)))

    helper : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x)
          → sym (lUnitₖ _ x) ∙ cong (_+ₖ x) p ≡ sym (rUnitₖ _ x) ∙ cong (x +ₖ_) p
    helper n x = J (λ x p → sym (lUnitₖ _ x) ∙ cong (_+ₖ x) p ≡ sym (rUnitₖ _ x) ∙ cong (x +ₖ_) p)
                   (helper' n)
      where
      helper' : (n : ℕ) → (λ i → lUnitₖ (suc n) (0ₖ (suc n)) (~ i)) ∙
               (λ i → 0ₖ (suc n) +ₖ 0ₖ (suc n))
               ≡
               (λ i → rUnitₖ (suc n) (0ₖ (suc n)) (~ i)) ∙
               (λ i → 0ₖ (suc n) +ₖ 0ₖ (suc n))
      helper' zero = refl
      helper' (suc n) = refl

    left-fst≡right-fst : (n : ℕ) → left-fst n (ptSn _) ≡ right-fst n (ptSn _)
    left-fst≡right-fst zero i j z = helper _ (z ⌣ₖ ∣ base ∣) (sym (⌣ₖ-0ₖ _ _ z)) i j
    left-fst≡right-fst (suc n) i j z = helper _ (z ⌣ₖ ∣ north ∣) (sym (⌣ₖ-0ₖ _ (suc (suc n)) z)) i j

    main : (a b : S₊ (suc n)) →
      ⌣ₖ-distrFun (suc n) (suc m) ∣ a ∣ₕ ∣ b ∣ₕ ≡
      ⌣ₖ-distrFun2 (suc n) (suc m) ∣ a ∣ₕ ∣ b ∣ₕ
    main =
      wedgeconFun n n
      (λ x y → subst (λ l → isOfHLevel l ((⌣ₖ-distrFun (suc n) (suc m) ∣ x ∣ ∣ y ∣)
                                           ≡  ⌣ₖ-distrFun2 (suc n) (suc m) ∣ x ∣ ∣ y ∣))
                        (+-suc n (suc n))
                        (isOfHLevelPlus {n = 2 + n} n (hLevHelp n m ∣ x ∣ ∣ y ∣)))
      (λ x → →∙Homogeneous≡ (isHomogeneousKn _) (left-fst n x))
      (λ x → →∙Homogeneous≡ (isHomogeneousKn _) (right-fst n x))
      (cong (→∙Homogeneous≡ (isHomogeneousKn _)) (sym (left-fst≡right-fst n)))

  -- Distributivity for 0 dimensional cases
  leftDistr₀n : (n : ℕ) → (z : coHomK 0) (x y : coHomK n)
    → z ·₀ (x +[ n ]ₖ y) ≡ z ·₀ x +[ n ]ₖ (z ·₀ y)
  leftDistr₀n n (pos zero) x y = sym (rUnitₖ n (0ₖ _))
  leftDistr₀n n (pos (suc z)) x y =
       cong ((x +ₖ y) +ₖ_) (leftDistr₀n n (pos z) x y)
    ∙∙ sym (assocₖ n x y (pos z ·₀ x +[ n ]ₖ (pos z ·₀ y)))
    ∙∙ cong (x +ₖ_) (assocₖ n y (pos z ·₀ x) (pos z ·₀ y)
                 ∙∙ cong (_+ₖ (pos z ·₀ y)) (commₖ n y (pos z ·₀ x))
                 ∙∙ sym (assocₖ n (pos z ·₀ x) y (pos z ·₀ y)))
     ∙ assocₖ n x _ _
  leftDistr₀n n (negsuc zero) x y = -distrₖ n x y
  leftDistr₀n n (negsuc (suc z)) x y =
       cong₂ (_+ₖ_) (leftDistr₀n n (negsuc z) x y) (-distrₖ n x y)
    ∙∙ assocₖ n ((negsuc z ·₀ x) +ₖ (negsuc z ·₀ y)) (-ₖ x) (-ₖ y)
    ∙∙ cong (_-ₖ y) (sym (assocₖ n (negsuc z ·₀ x) (negsuc z ·₀ y) (-ₖ x))
                 ∙∙ cong ((negsuc z ·₀ x) +ₖ_) (commₖ n (negsuc z ·₀ y) (-ₖ x))
                 ∙∙ assocₖ n (negsuc z ·₀ x) (-ₖ x) (negsuc z ·₀ y))
     ∙ sym (assocₖ n (negsuc (suc z) ·₀ x) _ _)

  leftDistrn₀ : (n : ℕ) → (z : coHomK n) (x y : coHomK 0)
    → (x ℤ+ y) ·₀ z ≡ x ·₀ z +[ n ]ₖ (y ·₀ z)
  leftDistrn₀ n z x (pos zero) = sym (rUnitₖ n (x ·₀ z))
  leftDistrn₀ n z x (pos (suc y)) =
       lem (x +pos y)
    ∙∙ cong (z +ₖ_) (leftDistrn₀ n z x (pos y) ∙ commₖ n _ _)
    ∙∙ assocₖ n z _ _
     ∙ commₖ n _ _
    where
    lem : (a : ℤ) → (sucℤ a) ·₀ z ≡ z +ₖ (a ·₀ z)
    lem (pos zero) = refl
    lem (pos (suc a)) = cong (z +ₖ_) (lem (pos a))
    lem (negsuc zero) = sym (rCancelₖ n z)
    lem (negsuc (suc a)) = sym (-cancelLₖ n z (negsuc a ·₀ z)) ∙ sym (assocₖ n z (negsuc a ·₀ z) (-ₖ z))
  leftDistrn₀ n z x (negsuc y) = main y
    where
    help : (x : ℤ) → predℤ x ·₀ z ≡ (x ·₀ z -ₖ z)
    help (pos zero) = sym (lUnitₖ n (-ₖ z))
    help (pos (suc x)) = sym (-cancelLₖ n z (pos x ·₀ z))
    help (negsuc x) = refl

    main : (y : _) → (x ℤ+ negsuc y) ·₀ z ≡  (x ·₀ z) +ₖ (negsuc y ·₀ z)
    main zero = help x
    main (suc y) =
         help (x +negsuc y)
      ∙∙ cong (_-ₖ z) (main y)
      ∙∙ sym (assocₖ n _ _ _)

leftDistr-⌣ₖ : (n m : ℕ) (z : coHomK n) (x y : coHomK m)
          → z ⌣ₖ (x +ₖ y) ≡ (z ⌣ₖ x +ₖ z ⌣ₖ y)
leftDistr-⌣ₖ zero m z x y = leftDistr₀n m z x y
leftDistr-⌣ₖ (suc n) zero z x y = leftDistrn₀ (suc n) z x y
leftDistr-⌣ₖ (suc n) (suc m) z x y = funExt⁻ (cong fst (leftDistr-⌣ₖ· m n x y)) z


-- Right distributivity

private
  ⌣ₖ-distrFun-r : -- (x +ₖ y) ⌣ₖ z
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (n +' m)
  fst (⌣ₖ-distrFun-r n m x y) z =
    (x +ₖ y) ⌣ₖ z
  snd (⌣ₖ-distrFun-r n m x y) =
    ⌣ₖ-0ₖ n m (x +ₖ y) -- ⌣ₖ-0ₖ m n (x +ₖ y)

  ⌣ₖ-distrFun2-r :
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (n +' m)
  fst (⌣ₖ-distrFun2-r n m x y) z =
    x ⌣ₖ z +ₖ y ⌣ₖ z
  snd (⌣ₖ-distrFun2-r n m x y) =
    cong₂ _+ₖ_ (⌣ₖ-0ₖ n m x) (⌣ₖ-0ₖ n m y) ∙ rUnitₖ _ _

  rightDistr-⌣ₖ· : (n m : ℕ) (x y : coHomK (suc n)) → ⌣ₖ-distrFun-r (suc n) (suc m) x y ≡ ⌣ₖ-distrFun2-r (suc n) (suc m) x y
  rightDistr-⌣ₖ· n m =
    elim2 (λ _ _ → isOfHLevelPath (3 + n) (isOfHLevel↑∙ (suc n) m) _ _)
          main
    where
    fst-left : (n : ℕ) (y : S₊ (suc n)) →
      fst (⌣ₖ-distrFun-r (suc n) (suc m) ∣ ptSn (suc n) ∣ ∣ y ∣) ≡
      fst (⌣ₖ-distrFun2-r (suc n) (suc m) ∣ ptSn (suc n) ∣ ∣ y ∣)
    fst-left n y =
      funExt (λ z
        → cong (_⌣ₖ z) (lUnitₖ _ ∣ y ∣)
        ∙∙ sym (lUnitₖ _ (∣ y ∣ ⌣ₖ z))
        ∙∙ cong (_+ₖ (∣ y ∣ ⌣ₖ z)) (sym (0ₖ-⌣ₖ _ _ z)))

    fst-right : (n : ℕ) (x : S₊ (suc n)) →
      fst (⌣ₖ-distrFun-r (suc n) (suc m) ∣ x ∣ ∣ ptSn (suc n) ∣) ≡
      fst (⌣ₖ-distrFun2-r (suc n) (suc m) ∣ x ∣ ∣ ptSn (suc n) ∣)
    fst-right n x =
      funExt λ z
        → cong (_⌣ₖ z) (rUnitₖ _ ∣ x ∣)
        ∙∙ sym (rUnitₖ _ _)
        ∙∙ cong (∣ x ∣ ⌣ₖ z +ₖ_) (sym (0ₖ-⌣ₖ _ _ z))

    left≡right : (n : ℕ) → fst-left n (ptSn (suc n)) ≡ fst-right n (ptSn (suc n))
    left≡right zero = refl
    left≡right (suc n) = refl

    main : (a b : S₊ (suc n)) →
      ⌣ₖ-distrFun-r (suc n) (suc m) ∣ a ∣ₕ ∣ b ∣ₕ ≡
      ⌣ₖ-distrFun2-r (suc n) (suc m) ∣ a ∣ₕ ∣ b ∣ₕ
    main =
      wedgeconFun n n
        (λ x y → subst (λ l → isOfHLevel l ((⌣ₖ-distrFun-r (suc n) (suc m) ∣ x ∣ ∣ y ∣)
                                           ≡  ⌣ₖ-distrFun2-r (suc n) (suc m) ∣ x ∣ ∣ y ∣))
                        (+-suc n (suc n))
                        (isOfHLevelPlus {n = 2 + n} n (isOfHLevel↑∙ (suc n) m _ _)))
        (λ x → →∙Homogeneous≡ (isHomogeneousKn _) (fst-left n x))
        (λ x → →∙Homogeneous≡ (isHomogeneousKn _) (fst-right n x))
        (cong (→∙Homogeneous≡ (isHomogeneousKn _)) (sym (left≡right n)))

rightDistr-⌣ₖ : (n m : ℕ) (x y : coHomK n) (z : coHomK m)
          → (x +ₖ y) ⌣ₖ z ≡ (x ⌣ₖ z +ₖ y ⌣ₖ z)
rightDistr-⌣ₖ zero zero x y z =
     comm-·₀ (x ℤ+ y) z
  ∙∙ leftDistr-⌣ₖ zero zero z x y
  ∙∙ cong₂ _+ₖ_ (sym (comm-·₀ x z)) (sym (comm-·₀ y z))
rightDistr-⌣ₖ zero (suc m) x y z = leftDistr-⌣ₖ _ zero z x y
rightDistr-⌣ₖ (suc n) zero x y z = leftDistr-⌣ₖ zero (suc n) z x y
rightDistr-⌣ₖ (suc n) (suc m) x y z = (funExt⁻ (cong fst (rightDistr-⌣ₖ· n m x y))) z

-- Associativity

private
-- We need to give the two associators as (doubly) pointed functions
  assocer : (n m k : ℕ) → coHomK (suc n)
    →  coHomK-ptd (suc m)
    →∙ (coHomK-ptd (suc k)
    →∙ coHomK-ptd ((suc n) +' ((suc m) +' (suc k))) ∙)
  fst (fst (assocer n m k x) y) z = x ⌣ₖ (y ⌣ₖ z)
  snd (fst (assocer n m k x) y) = cong (x ⌣ₖ_) (⌣ₖ-0ₖ _ (suc k) y) ∙ ⌣ₖ-0ₖ _ _ x
  snd (assocer n m k x) =
    ΣPathP (funExt (λ z → cong (x ⌣ₖ_) (0ₖ-⌣ₖ (suc m) (suc k) z) ∙ ⌣ₖ-0ₖ (suc n) _ x)
          , help)
    where
    h : (n m k : ℕ) (x : coHomK (suc n)) → cong (_⌣ₖ_ x) (⌣ₖ-0ₖ (suc m) (suc k) (0ₖ _)) ≡
                                  (λ i → x ⌣ₖ 0ₖ-⌣ₖ (suc m) (suc k) (0ₖ _) i)
    h zero zero k x = refl
    h zero (suc m) k x = refl
    h (suc n) zero k x = refl
    h (suc n) (suc m) k x = refl

    help : PathP (λ i → (cong (x ⌣ₖ_) (0ₖ-⌣ₖ (suc m) (suc k) (0ₖ _)) ∙ ⌣ₖ-0ₖ (suc n) _ x) i ≡ 0ₖ _)
               (cong (x ⌣ₖ_) (⌣ₖ-0ₖ (suc m) (suc k) (0ₖ _)) ∙ ⌣ₖ-0ₖ (suc n) _ x) refl
    help = compPathR→PathP
      (cong (_∙ ⌣ₖ-0ₖ (suc n) ((suc m) +' (suc k)) x) (h n m k x)
      ∙∙ rUnit _
      ∙∙ cong ((cong (x ⌣ₖ_) (0ₖ-⌣ₖ (suc m) (suc k) (0ₖ _)) ∙ ⌣ₖ-0ₖ (suc n) _ x) ∙_) (rUnit refl))

  assoc2-sub : (n m k : ℕ) → _ → _
  assoc2-sub n m k = subst coHomK (sym (+'-assoc n m k))

  assoc2-sub-0 : (n m k : ℕ) → assoc2-sub n m k (0ₖ _) ≡ 0ₖ _
  assoc2-sub-0 zero zero zero = refl
  assoc2-sub-0 zero zero (suc zero) = refl
  assoc2-sub-0 zero zero (suc (suc k)) = refl
  assoc2-sub-0 zero (suc zero) zero = refl
  assoc2-sub-0 zero (suc zero) (suc k) = refl
  assoc2-sub-0 zero (suc (suc m)) zero = refl
  assoc2-sub-0 zero (suc (suc m)) (suc k) = refl
  assoc2-sub-0 (suc zero) zero zero = refl
  assoc2-sub-0 (suc zero) zero (suc k) = refl
  assoc2-sub-0 (suc (suc n)) zero zero = refl
  assoc2-sub-0 (suc (suc n)) zero (suc k) = refl
  assoc2-sub-0 (suc zero) (suc m) zero = refl
  assoc2-sub-0 (suc (suc n)) (suc m) zero = refl
  assoc2-sub-0 (suc zero) (suc m) (suc k) = refl
  assoc2-sub-0 (suc (suc n)) (suc m) (suc k) = refl

  assocer2 : (n m k : ℕ)
           → coHomK (suc n)
           → coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd ((suc n) +' ((suc m) +' (suc k))) ∙)
  fst (fst (assocer2 n m k x) y) z =
    subst coHomK (sym (+'-assoc (suc n) (suc m) (suc k))) ((x ⌣ₖ y) ⌣ₖ z) --
  snd (fst (assocer2 zero m k x) y) =
    cong (subst coHomK (sym (+'-assoc 1 (suc m) (suc k)))) (⌣ₖ-0ₖ _ _ (x ⌣ₖ y))
  snd (fst (assocer2 (suc n) m k x) y) =
    cong (subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k)))) (⌣ₖ-0ₖ _ _ (x ⌣ₖ y))
  fst (snd (assocer2 zero m k x) i) z =
    subst coHomK (sym (+'-assoc (suc zero) (suc m) (suc k))) (⌣ₖ-0ₖ _ _ x i ⌣ₖ z)
  snd (snd (assocer2 zero m k x) i) j =
    subst coHomK (sym (+'-assoc (suc zero) (suc m) (suc k))) (⌣ₖ-0ₖ _ _ (⌣ₖ-0ₖ _ _ x i) j)
  fst (snd (assocer2 (suc n) m k x) i) z =
    subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k))) (⌣ₖ-0ₖ _ _ x i ⌣ₖ z)
  snd (snd (assocer2 (suc n) m k x) i) j =
    subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k))) (⌣ₖ-0ₖ _ _ (⌣ₖ-0ₖ _ _ x i) j)

  assocer-helpFun : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
  fst (assocer-helpFun n m a) b = Kn→ΩKn+1 _ (a ⌣ₖ b)
  snd (assocer-helpFun n m a) = cong (Kn→ΩKn+1 _) (⌣ₖ-0ₖ (suc n) (suc m) a) ∙ Kn→ΩKn+10ₖ _

  assocer-helpFun2 : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
  fst (assocer-helpFun2 n m a) b i = (Kn→ΩKn+1 _ a i) ⌣ₖ b
  snd (assocer-helpFun2 n m a) i j = ⌣ₖ-0ₖ _ (suc m) (Kn→ΩKn+1 _ a j) i

-- Key lemma for associativity
assocer-helpFun≡ : (n m : ℕ) → (x : coHomK (suc n)) → assocer-helpFun n m x ≡ assocer-helpFun2 n m x
assocer-helpFun≡ n m =
  trElim (λ _ → isOfHLevelPath (3 + n) (hLev-assocer-helpFun n m) _ _)
         λ a → →∙Homogeneous≡ (subst isHomogeneous Kn≃ΩKn+1∙ (isHomogeneousKn _))
           (funExt (main n a))
  where
  hLev-assocer-helpFun : (n m : ℕ) → isOfHLevel (3 + n) (coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m))))
  hLev-assocer-helpFun n m =
    subst (isOfHLevel (3 + n)) (cong (coHomK-ptd (suc m) →∙_)
      (Kn≃ΩKn+1∙))
      (isOfHLevel↑∙ (suc n) m)

  main : (n : ℕ) (a : S₊ (suc n)) (b : _)
    → fst (assocer-helpFun n m ∣ a ∣) b ≡ fst (assocer-helpFun2 n m ∣ a ∣) b
  main zero a b k i =
    hcomp
      (λ r → λ {(i = i0) → 0ₖ _
               ; (i = i1) → ∣ rCancel (merid north) r (~ k) ∣
               ; (k = i0) → Kn→ΩKn+1 _ (∣ a ∣ ⌣ₖ b) i
               ; (k = i1) → (Kn→ΩKn+1 _ ∣ a ∣ i) ⌣ₖ b})
      (∣ compPath-filler (merid a) (sym (merid base)) k i ∣ ⌣ₖ b)
  main (suc n) a b k i =
    hcomp
      (λ r → λ {(i = i0) → 0ₖ _
               ; (i = i1) → ∣ rCancel (merid north) r (~ k) ∣
               ; (k = i0) → Kn→ΩKn+1 _ (∣ a ∣ ⌣ₖ b) i
               ; (k = i1) → (Kn→ΩKn+1 _ ∣ a ∣ i) ⌣ₖ b})
      (∣ compPath-filler (merid a) (sym (merid north)) k i ∣ ⌣ₖ b)

assoc-helper : (n m : ℕ) (x : coHomK (suc n)) (y : coHomK (suc m))
             → Kn→ΩKn+1 _ (x ⌣ₖ y) ≡ λ i → (Kn→ΩKn+1 _ x i) ⌣ₖ y
assoc-helper n m x y = funExt⁻ (cong fst (assocer-helpFun≡ n m x)) y

assoc-⌣ₖ· : (n m k : ℕ) → (x : coHomK (suc n)) → assocer n m k x ≡ assocer2 n m k x
assoc-⌣ₖ· n m k =
  trElim (λ _ → isOfHLevelPath (3 + n)
            (transport (λ i → isOfHLevel (3 + n)
                (coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd (h (~ i)) ∙)))
              (isOfHLevel↑∙∙ m k (suc n))) _ _)
         λ a → →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousKn _))
           (funExt λ b → →∙Homogeneous≡ (isHomogeneousKn _)
             (funExt (main n m k a b)))
  where

  h : (suc n) +' ((suc m) +' (suc k)) ≡ suc (suc (suc n + m + k))
  h = cong (2 +_) (+-suc n (m + k)) ∙ λ i → suc (suc (suc (+-assoc n m k i)))


  main : (n m k : ℕ) (a : S₊ (suc n)) (b : coHomK (suc m)) (c : coHomK (suc k))
    → ∣ a ∣ ⌣ₖ b ⌣ₖ c ≡
      (subst coHomK (λ i → +'-assoc (suc n) (suc m) (suc k) (~ i))
        ((∣ a ∣ ⌣ₖ b) ⌣ₖ c))
  main zero m k a b c = goal a ∙ sym (funExt⁻ t ((∣ a ∣ ⌣ₖ b) ⌣ₖ c))
    where
    t : subst coHomK (λ i → +'-assoc 1 (suc m) (suc k) (~ i)) ≡ idfun _
    t = cong (subst coHomK) (isSetℕ _ _ (+'-assoc 1 (suc m) (suc k)) refl) ∙ funExt transportRefl
    goal : (a : _) → ∣ a ∣ ⌣ₖ b ⌣ₖ c ≡ (∣ a ∣ ⌣ₖ b) ⌣ₖ c
    goal base = refl
    goal (loop i) j = assoc-helper m k b c j i
  main (suc n) m k north b c = refl
  main (suc n) m k south b c = refl
  main (suc n) m k (merid a i) b c j = help2 j i
    where
      transpLem : (n m : ℕ) (p : n ≡ m) → subst coHomK p (0ₖ _) ≡ 0ₖ _
      transpLem zero m = J (λ m p → subst coHomK p (0ₖ _) ≡ 0ₖ _) refl
      transpLem (suc zero) m = J (λ m p → subst coHomK p (0ₖ _) ≡ 0ₖ _) refl
      transpLem (suc (suc n)) m = J (λ m p → subst coHomK p (0ₖ _) ≡ 0ₖ _) refl

      transpLem-refl : transpLem (suc (suc (suc (suc (n + m + k)))))
                                    (suc (suc n +' (suc m +' suc k)))
                                    (λ i₃ → +'-assoc (2 + n) (suc m) (suc k) (~ i₃)) ≡ refl
      transpLem-refl = transportRefl refl
      moveTransports : (n m : ℕ) (x : coHomK n) (p : n ≡ m) (q : (suc n) ≡ suc m)
                    → PathP (λ i → transpLem _ _ q (~ i) ≡ transpLem _ _ q (~ i))
                            (Kn→ΩKn+1 _ (subst coHomK p x))
                            (cong (subst coHomK q) (Kn→ΩKn+1 _ x))
      moveTransports n m x =
        J (λ m p → (q : (suc n) ≡ suc m)
                    → PathP (λ i → transpLem _ _ q (~ i) ≡ transpLem _ _ q (~ i))
                            (Kn→ΩKn+1 _ (subst coHomK p x))
                            (cong (subst coHomK q) (Kn→ΩKn+1 _ x)))
          λ q → transport (λ j → PathP (λ i → transpLem (suc n) (suc n) (isSetℕ _ _ refl q j) (~ i)
                                              ≡ transpLem (suc n) (suc n) (isSetℕ _ _ refl q j) (~ i))
                           (Kn→ΩKn+1 _ (subst coHomK refl x))
                           (cong (subst coHomK (isSetℕ _ _ refl q j)) (Kn→ΩKn+1 _ x)))
                 (h2 n x)
        where
        h2 : (n : ℕ) (x : _)
         → PathP  (λ i₁ →
         transpLem (suc n) (suc n) (λ _ → suc n) (~ i₁) ≡
         transpLem (suc n) (suc n) (λ _ → suc n) (~ i₁))
         (Kn→ΩKn+1 n (subst coHomK (λ _ → n) x))
         (λ i₁ → subst coHomK (λ _ → suc n) (Kn→ΩKn+1 n x i₁))
        h2 zero x k i =
          hcomp (λ j → λ {(i = i0) → transportRefl (refl {x = 0ₖ _}) (~ j) k
                         ; (i = i1) → transportRefl (refl {x = 0ₖ _}) (~ j) k
                         ; (k = i0) → Kn→ΩKn+1 _ (transportRefl x j) i
                         ; (k = i1) → transportRefl (Kn→ΩKn+1 _ x i) (~ j)})
                 (Kn→ΩKn+1 _ x i)
        h2 (suc n) x k i =
          hcomp (λ j → λ {(i = i0) → transportRefl (refl {x = 0ₖ _}) (~ j) k
                         ; (i = i1) → transportRefl (refl {x = 0ₖ _}) (~ j) k
                         ; (k = i0) → Kn→ΩKn+1 _ (transport refl x) i
                         ; (k = i1) → transportRefl (Kn→ΩKn+1 _ x i) (~ j)})
                 (Kn→ΩKn+1 _ (transportRefl x k) i)

      finalTransp : (n : ℕ) (a : _) → Kn→ΩKn+1 _ (subst coHomK (λ i₁ → +'-assoc (suc n) (suc m) (suc k) (~ i₁)) ((∣ a ∣ ⌣ₖ b) ⌣ₖ c))
                  ≡ cong (subst coHomK (λ i₁ → +'-assoc (2 + n) (suc m) (suc k) (~ i₁))) (Kn→ΩKn+1 _ ((∣ a ∣ ⌣ₖ b) ⌣ₖ c))
      finalTransp n a =
           rUnit _
        ∙∙ (λ i → (λ j → transpLem (suc (suc (suc (suc (n + m + k)))))
                          (suc (suc n +' (suc m +' suc k)))
                          (λ i₃ → +'-assoc (2 + n) (suc m) (suc k) (~ i₃)) (i ∧ j))
                ∙∙ moveTransports _ _ ((∣ a ∣ ⌣ₖ b) ⌣ₖ c)
                     (sym (+'-assoc (suc n) (suc m) (suc k)))
                     (sym (+'-assoc (2 + n) (suc m) (suc k))) i
                ∙∙ λ j → transpLem (suc (suc (suc (suc (n + m + k)))))
                                    (suc (suc n +' (suc m +' suc k)))
                                    (λ i₃ → +'-assoc (2 + n) (suc m) (suc k) (~ i₃)) (i ∧ ~ j))
        ∙∙ (λ i → transportRefl refl i
                ∙∙ cong (subst coHomK (λ i₁ → +'-assoc (2 + n) (suc m) (suc k) (~ i₁))) (Kn→ΩKn+1 _ ((∣ a ∣ ⌣ₖ b) ⌣ₖ c))
                ∙∙ transportRefl refl i)
         ∙ sym (rUnit _)

      help2 : cong (λ x → (∣ x ∣) ⌣ₖ (b ⌣ₖ c)) (merid a) ≡ cong (assoc2-sub (2 + n) (suc m) (suc k)) (cong (λ x → (∣ x ∣ ⌣ₖ b) ⌣ₖ c) (merid a))
      help2 = ((λ r → Kn→ΩKn+1 _ (main n m k a b c r)))
            ∙∙ finalTransp n a
            ∙∙ λ r i → subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k))) (assoc-helper _ _ (∣ a ∣ ⌣ₖ b) c r i)


-- Some key distributivity lemmas
-Distₗ : (n m : ℕ) (x : coHomK n) (y : coHomK m) → (-ₖ (x ⌣ₖ y)) ≡ (-ₖ x) ⌣ₖ y
-Distₗ n m x y =
       sym (rUnitₖ _ (-ₖ (x ⌣ₖ y)))
    ∙∙ cong ((-ₖ (x ⌣ₖ y)) +ₖ_) (sym (rCancelₖ _ (x ⌣ₖ y)))
    ∙∙ assocₖ _ (-ₖ (x ⌣ₖ y)) (x ⌣ₖ y) (-ₖ (x ⌣ₖ y))
    ∙∙ cong (_-ₖ (x ⌣ₖ y)) help
    ∙∙ sym (assocₖ _ ((-ₖ x) ⌣ₖ y) (x ⌣ₖ y) (-ₖ (x ⌣ₖ y)))
    ∙∙ cong ((-ₖ x) ⌣ₖ y +ₖ_) (rCancelₖ _ (x ⌣ₖ y))
    ∙∙ rUnitₖ _ ((-ₖ x) ⌣ₖ y)
  where
  help : (-ₖ (x ⌣ₖ y)) +ₖ (x ⌣ₖ y) ≡ (-ₖ x) ⌣ₖ y +ₖ (x ⌣ₖ y)
  help = lCancelₖ _ _
      ∙∙ sym (0ₖ-⌣ₖ _ _ y)
       ∙ cong (_⌣ₖ y) (sym (lCancelₖ _ x))
      ∙∙ rightDistr-⌣ₖ _ _ (-ₖ x) x y

-Distᵣ : (n m : ℕ) (x : coHomK n) (y : coHomK m) → (-ₖ (x ⌣ₖ y)) ≡ x ⌣ₖ (-ₖ y)
-Distᵣ n m x y =
  sym (rUnitₖ _ (-ₖ (x ⌣ₖ y)))
    ∙∙ cong ((-ₖ (x ⌣ₖ y)) +ₖ_) (sym (rCancelₖ _ (x ⌣ₖ y)))
    ∙∙ assocₖ _ (-ₖ (x ⌣ₖ y)) (x ⌣ₖ y) (-ₖ (x ⌣ₖ y))
    ∙∙ cong (_-ₖ (x ⌣ₖ y)) help
    ∙∙ sym (assocₖ _ (x ⌣ₖ (-ₖ y)) (x ⌣ₖ y) (-ₖ (x ⌣ₖ y)))
    ∙∙ cong (x ⌣ₖ (-ₖ y) +ₖ_) (rCancelₖ _ (x ⌣ₖ y))
    ∙∙ rUnitₖ _ (x ⌣ₖ (-ₖ y))
  where
  help : (-ₖ (x ⌣ₖ y)) +ₖ (x ⌣ₖ y) ≡ x ⌣ₖ (-ₖ y) +ₖ (x ⌣ₖ y)
  help = lCancelₖ _ _
      ∙∙ sym (⌣ₖ-0ₖ _ _ x)
      ∙∙ cong (x ⌣ₖ_) (sym (lCancelₖ _ y))
       ∙ leftDistr-⌣ₖ _ _ x (-ₖ y) y

assoc₀ : (m k : ℕ) (x : ℤ) (y : coHomK m) (z : coHomK k) → _⌣ₖ_{n = zero} x (y ⌣ₖ z) ≡ (_⌣ₖ_{n = zero} {m = m} x y) ⌣ₖ z
assoc₀ m k x y z = main x
  where
  h : subst coHomK (sym (+'-assoc zero m k)) ≡ idfun _
  h = cong (subst coHomK) (isSetℕ _ _ _ refl) ∙ funExt transportRefl
  mainPos : (x : ℕ) → _⌣ₖ_ {n = zero} (pos x) (y ⌣ₖ z) ≡ ((_⌣ₖ_ {n = zero} {m = m} (pos x) y) ⌣ₖ z)
  mainPos zero = sym (0ₖ-⌣ₖ _ _ z) ∙ cong (_⌣ₖ z) (sym (0ₖ-⌣ₖ _ _ y))
  mainPos (suc n) =
      cong (y ⌣ₖ z +ₖ_) (mainPos n)
    ∙∙ sym (rightDistr-⌣ₖ _ _ y (_⌣ₖ_ {n = zero} {m = m} (pos n) y) z)
    ∙∙ (λ i → (y +ₖ (_⌣ₖ_ {n = zero} {m = m} (pos n) y)) ⌣ₖ z)

  main : (x : ℤ) → x ⌣ₖ y ⌣ₖ z ≡ ((_⌣ₖ_ {n = zero} {m = m} x y) ⌣ₖ z)
  main (pos n) = mainPos n
  main (negsuc n) =
       (λ i → _⌣ₖ_ {n = zero} (+ℤ-comm (negsuc n) 0 i) (y ⌣ₖ z))
    ∙∙ sym (-Distₗ zero _ (pos (suc n)) (y ⌣ₖ z))
     ∙ cong (-ₖ_) (mainPos (suc n))
    ∙∙ -Distₗ _ _ (pos (suc n) ⌣ₖ y) z
    ∙∙ cong (_⌣ₖ z) ((-Distₗ zero _ (pos (suc n)) y))
    ∙∙ λ i → (_⌣ₖ_ {n = zero} (+ℤ-comm (negsuc n) 0 (~ i)) y) ⌣ₖ z

assoc-⌣ₖ : (n m k : ℕ) (x : coHomK n) (y : coHomK m) (z : coHomK k)
  → x ⌣ₖ y ⌣ₖ z ≡ subst coHomK (sym (+'-assoc n m k)) ((x ⌣ₖ y) ⌣ₖ z)
assoc-⌣ₖ zero m k x y z = assoc₀ _ _ x y z ∙ sym (funExt⁻ h ((x ⌣ₖ y) ⌣ₖ z))
  where
  h : subst coHomK (sym (+'-assoc zero m k)) ≡ idfun _
  h = cong (subst coHomK) (isSetℕ _ _ _ refl) ∙ funExt transportRefl

assoc-⌣ₖ (suc n) zero k x y z =
     help y
  ∙∙ sym (transportRefl ((x ⌣ₖ y) ⌣ₖ z))
  ∙∙ λ i → transport (λ j → coHomK ((isSetℕ _ _ ((sym (+'-assoc (suc n) zero k))) refl (~ i) j)))
       ((_⌣ₖ_ {m = zero} x y) ⌣ₖ z)
  where
  helpPos : (y : ℕ) → x ⌣ₖ (_⌣ₖ_ {n = zero} (pos y) z) ≡
      ((_⌣ₖ_ {m = zero} x (pos y)) ⌣ₖ z)
  helpPos zero =
    (⌣ₖ-0ₖ _ _ x)
     ∙∙ (sym (0ₖ-⌣ₖ _ _ z))
     ∙∙ cong (_⌣ₖ z) (sym (⌣ₖ-0ₖ _ _ x))
  helpPos (suc y) =
    leftDistr-⌣ₖ _ _ x z (_⌣ₖ_{n = zero} (pos y) z)
    ∙∙ cong ((x ⌣ₖ z) +ₖ_) (helpPos y)
    ∙∙ sym (rightDistr-⌣ₖ _ _ x (_⌣ₖ_{n = zero} (pos y) x) z)

  help : (y : ℤ) → x ⌣ₖ (_⌣ₖ_ {n = zero} y z) ≡
      ((_⌣ₖ_ {m = zero} x y) ⌣ₖ z)
  help (pos n) = helpPos n
  help (negsuc n) =
       (λ i → x ⌣ₖ (_⌣ₖ_ {n = zero} (+ℤ-comm (negsuc n) 0 i) z))
    ∙∙ cong (x ⌣ₖ_) (sym (-Distₗ zero _ (pos (suc n)) z))
    ∙∙ sym (-Distᵣ _ _ x _)
    ∙∙ cong -ₖ_ (helpPos (suc n))
    ∙∙ -Distₗ _ _ _ z
    ∙∙ cong (_⌣ₖ z) (-Distᵣ _ zero x (pos (suc n)))
    ∙∙ λ i → (_⌣ₖ_ {m = zero} x (+ℤ-comm (negsuc n) 0 (~ i))) ⌣ₖ z
assoc-⌣ₖ (suc n) (suc m) zero x y z =
    (assoc-⌣ₖ (suc n) zero (suc m) x z y)
  ∙∙ cong (subst coHomK (sym (+'-assoc (suc n) zero (suc m))))
     (sym (assoc₀ _ _ z x y))
  ∙∙ (funExt⁻ (sym h) (_⌣ₖ_ {n = zero} z (x ⌣ₖ y)))
  where
  h : subst coHomK (sym (+'-assoc (suc n) (suc m) zero))
    ≡ subst coHomK (λ i → +'-assoc (suc n) zero (suc m) (~ i))
  h = cong (subst coHomK) (isSetℕ _ _ _ _)
assoc-⌣ₖ (suc n) (suc m) (suc k) x y z =
  funExt⁻ (cong fst (funExt⁻ (cong fst (assoc-⌣ₖ· n m k x)) y)) z

-- Ring laws for ⌣
module _ {A : Type ℓ} (n m : ℕ) where
  ⌣-0ₕ : (f : coHom n A) → (f ⌣ 0ₕ m) ≡ 0ₕ _
  ⌣-0ₕ = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
                λ f → cong ∣_∣₂ (funExt λ x → ⌣ₖ-0ₖ n m (f x))

  0ₕ-⌣ : (f : coHom m A) → (0ₕ n ⌣ f) ≡ 0ₕ _
  0ₕ-⌣ = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
                λ f → cong ∣_∣₂ (funExt λ x → 0ₖ-⌣ₖ n m (f x))


  leftDistr-⌣ : (f : coHom n A) (g h : coHom m A)
              → f ⌣ (g +ₕ h) ≡ f ⌣ g +ₕ f ⌣ h
  leftDistr-⌣ =
    sElim (λ _ → isSetΠ2 λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f → sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
        λ g h → cong ∣_∣₂ (funExt λ x → leftDistr-⌣ₖ n m (f x) (g x) (h x))

  rightDistr-⌣ : (g h : coHom n A) (f : coHom m A) → (g +ₕ h) ⌣ f ≡ g ⌣ f +ₕ h ⌣ f
  rightDistr-⌣ =
    sElim2 (λ _ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
      λ g h → sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ f → cong ∣_∣₂ (funExt λ x → rightDistr-⌣ₖ n m (g x) (h x) (f x))

  assoc-⌣ : (l : ℕ) (f : coHom n A) (g : coHom m A) (h : coHom l A)
          → f ⌣ g ⌣ h ≡ subst (λ x → coHom x A) (sym (+'-assoc n m l)) ((f ⌣ g) ⌣ h)
  assoc-⌣ l =
    sElim (λ _ → isSetΠ2 λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f → sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ g → sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) λ h →
          cong ∣_∣₂ ((funExt (λ x → assoc-⌣ₖ n m l (f x) (g x) (h x)
                   ∙ cong (subst coHomK (sym (+'-assoc n m l)))
                     λ i → (f (transportRefl x (~ i)) ⌣ₖ g (transportRefl x (~ i)))
                         ⌣ₖ (h (transportRefl x (~ i))))))

-- Additive unit(s)
0⌣ :  ∀ {ℓ} {A : Type ℓ} (n m : ℕ) (x : coHom n A)
     → x ⌣ (0ₕ m) ≡ 0ₕ _
0⌣ n m = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
                λ f → cong ∣_∣₂ (funExt λ x → ⌣ₖ-0ₖ n m (f x))

⌣0 :  ∀ {ℓ} {A : Type ℓ} (n m : ℕ) (x : coHom n A)
     → (0ₕ m) ⌣ x ≡ 0ₕ _
⌣0 n m = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
                λ f → cong ∣_∣₂ (funExt λ x → 0ₖ-⌣ₖ m n (f x))

-- Multiplicative unit
1⌣ : ∀ {ℓ} {A : Type ℓ} → coHom 0 A
1⌣ = ∣ (λ _ → 1) ∣₂

private
  n+'0 : (n : ℕ) → n +' 0 ≡ n
  n+'0 zero = refl
  n+'0 (suc n) = refl

lUnit⌣ₖ : (n : ℕ) (x : coHomK n) → _⌣ₖ_ {n = 0} (pos 1) x ≡ x
lUnit⌣ₖ zero = λ _ → refl
lUnit⌣ₖ (suc n) x = rUnitₖ _ x

lUnit⌣ : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (x : coHom n A)
  → x ⌣ 1⌣ ≡ subst (λ n → coHom n A) (sym (n+'0 n)) x
lUnit⌣ zero = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f → cong ∣_∣₂ (funExt (λ x → comm-·₀ (f x) (pos 1))) ∙ sym (transportRefl ∣ f ∣₂)
lUnit⌣ (suc n) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f → cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) (0ₖ-⌣ₖ zero _ (f x)) ∙ rUnitₖ _ (f x)))
       ∙ sym (transportRefl ∣ f ∣₂)

rUnit⌣ : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (x : coHom n A)
       → 1⌣ ⌣ x ≡ x
rUnit⌣ zero = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
               λ f → refl
rUnit⌣ (suc n) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
               λ f → cong ∣_∣₂ (funExt λ x → rUnitₖ _ (f x))

-ₕDistᵣ : ∀ {ℓ} {A : Type ℓ} (n m : ℕ)
  (x : coHom n A) (y : coHom m A) → (-ₕ (x ⌣ y)) ≡ x ⌣ (-ₕ y)
-ₕDistᵣ n m =
  sElim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
    λ f g → cong ∣_∣₂ (funExt λ x → -Distᵣ n m (f x) (g x))

-- TODO : Graded ring structure
