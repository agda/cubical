{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CupProduct where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties

open import Cubical.Foundations.Transport

open import Cubical.HITs.S1 hiding (encode ; decode ; _·_)
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm ; +-assoc to ℤ+-assoc ; -_ to -ℤ_) hiding (_+'_ ; +'≡+)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma
open import Cubical.Foundations.Path

open import Cubical.Foundations.Pointed.Homogeneous

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level

isOfHLevel→∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) → isOfHLevel n (fst B) → isOfHLevel n (A →∙ B)
isOfHLevel→∙ n hlev = isOfHLevelΣ n (isOfHLevelΠ n (λ _ → hlev)) λ x → isOfHLevelPath n hlev _ _


-- Cup product with one K₀-argument

infixl 30 _·₀_

_·₀_ : {n : ℕ} (m : Int) → coHomK n → coHomK n
_·₀_ {n = n} (pos zero) x = 0ₖ _
_·₀_ {n = n} (pos (suc m)) x = x +ₖ (pos m ·₀ x)
_·₀_ {n = n} (negsuc zero) x = -ₖ x
_·₀_ {n = n} (negsuc (suc m)) x = (negsuc m ·₀ x) -ₖ x

·₀-rUnit : {n : ℕ} (m : Int) → _·₀_ m (0ₖ n) ≡ 0ₖ n
·₀-rUnit (pos zero) = refl
·₀-rUnit (pos (suc n)) = cong (0ₖ _ +ₖ_) (·₀-rUnit (pos n)) ∙ rUnitₖ _ (0ₖ _)
·₀-rUnit {n = zero} (negsuc zero) = refl
·₀-rUnit {n = suc zero} (negsuc zero) = refl
·₀-rUnit {n = suc (suc k)} (negsuc zero) = refl
·₀-rUnit {n = zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (·₀-rUnit (negsuc n))
·₀-rUnit {n = suc zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (·₀-rUnit (negsuc n))
·₀-rUnit {n = suc (suc k)} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (·₀-rUnit (negsuc n))

·₀-lUnit : {n : ℕ} (x : coHomK n) → 0 ·₀ x ≡ 0ₖ n
·₀-lUnit m = refl

·₀≡·ℤ : (x y : Int) → _·₀_ {n = zero} x y ≡ x ℤ∙ y
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
    help (suc n) = cong sucInt (help n)

comm-·₀ : (x y : Int) → _·₀_ {n = 0} x y ≡ y ·₀ x
comm-·₀ x y = ·₀≡·ℤ x y ∙∙ ∙-comm x y ∙∙ sym (·₀≡·ℤ y x)

---

_+'_ : ℕ → ℕ → ℕ
zero +' b = b
suc a +' zero = suc a
suc a +' suc b = 2 + (a + b)

+'-zero : (n : ℕ) → n +' 0 ≡ n
+'-zero zero = refl
+'-zero (suc n) = refl


+'≡+ : (n m : ℕ) → n +' m ≡ n + m
+'≡+ zero m = refl
+'≡+ (suc n) zero = cong suc (sym (+-comm n zero))
+'≡+ (suc n) (suc m) = cong suc (sym (+-suc n m))

+'-assoc : (n m l : ℕ) → (n +' (m +' l)) ≡ ((n +' m) +' l)
+'-assoc n m l =
     (λ i → +'≡+ n (+'≡+ m l i) i)
  ∙∙ +-assoc n m l
  ∙∙ (λ i → +'≡+ (+'≡+ n m (~ i)) l (~ i))

-- Cup procut

-- Pointed version first (enables truncation elimination)
⌣ₖ∙ : (n m : ℕ) → coHomK n → coHomK-ptd m →∙ coHomK-ptd (n +' m)
fst (⌣ₖ∙ zero m a) b = a ·₀ b
snd (⌣ₖ∙ zero m a) = ·₀-rUnit a
fst (⌣ₖ∙ (suc n) zero a) b = b ·₀ a
snd (⌣ₖ∙ (suc n) zero a) = refl
⌣ₖ∙ (suc n) (suc m) = trRec (isOfHLevel↑∙ (suc n) m) (cup n m)
  where
  cup : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
  fst (cup zero m base) _ = 0ₖ _
  fst (cup zero m (loop i)) x = Kn→ΩKn+1 _ x i
  fst (cup (suc n) m north) _ = 0ₖ _
  fst (cup (suc n) m south) _ = 0ₖ _
  fst (cup (suc n) m (merid a i)) x = Kn→ΩKn+1 _ (fst (cup n m a) x) i
  snd (cup zero m base) = refl
  snd (cup zero m (loop i)) k = Kn→ΩKn+10ₖ _ k i
  snd (cup (suc n) m north) = refl
  snd (cup (suc n) m south) = refl
  snd (cup (suc n) m (merid a i)) k = (cong (Kn→ΩKn+1 _) (snd (cup n m a)) ∙ Kn→ΩKn+10ₖ _) k i

-- Non pointed version
infixr 35 _⌣ₖ_
_⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n +' m)
_⌣ₖ_ {n = n} {m = m} x y = fst (⌣ₖ∙ n m x) y

-- Doubly pointed version
⌣ₖ∙∙ : (n m : ℕ) → coHomK-ptd n →∙ (coHomK-ptd m →∙ coHomK-ptd (n +' m) ∙)
fst (⌣ₖ∙∙ n m) = ⌣ₖ∙ n m
fst (snd (⌣ₖ∙∙ zero zero) i) x = 0
fst (snd (⌣ₖ∙∙ zero (suc m)) i) x = 0ₖ _
fst (snd (⌣ₖ∙∙ (suc n) zero) i) x = ·₀-rUnit x i
fst (snd (⌣ₖ∙∙ (suc zero) (suc m)) i) x = 0ₖ _
fst (snd (⌣ₖ∙∙ (suc (suc n)) (suc m)) i) x = 0ₖ _
snd (snd (⌣ₖ∙∙ zero zero) i) = refl
snd (snd (⌣ₖ∙∙ zero (suc m)) i) = refl
snd (snd (⌣ₖ∙∙ (suc n) zero) i) = refl
snd (snd (⌣ₖ∙∙ (suc zero) (suc m)) i) = refl
snd (snd (⌣ₖ∙∙ (suc (suc n)) (suc m)) i) = refl

-- Right and left unit laws
rUnit-⌣ₖ : (n m : ℕ) → (x : coHomK n)
        → x ⌣ₖ (0ₖ _) ≡ 0ₖ _
rUnit-⌣ₖ  n m x = snd (⌣ₖ∙ n m x)

lUnit-⌣ₖ : (n m : ℕ) → (x : coHomK m) →
        (0ₖ _) ⌣ₖ x ≡ 0ₖ _
lUnit-⌣ₖ n m = funExt⁻ (cong fst (snd (⌣ₖ∙∙ n m)))

rUnit-⌣ₖ≡lUnit-⌣ₖ : (n m : ℕ) → rUnit-⌣ₖ n m (0ₖ _) ≡ lUnit-⌣ₖ n m (0ₖ _)
rUnit-⌣ₖ≡lUnit-⌣ₖ zero zero = refl
rUnit-⌣ₖ≡lUnit-⌣ₖ zero (suc m) = refl
rUnit-⌣ₖ≡lUnit-⌣ₖ (suc n) zero = refl
rUnit-⌣ₖ≡lUnit-⌣ₖ (suc zero) (suc m) = refl
rUnit-⌣ₖ≡lUnit-⌣ₖ (suc (suc n)) (suc m) = refl

-- Left distributativity

private
  ⌣ₖ-distrFun : -- z ⌣ₖ (x +ₖ y)
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (m +' n)
  fst (⌣ₖ-distrFun n m x y) z =
    z ⌣ₖ (x +ₖ y)
  snd (⌣ₖ-distrFun n m x y) =
    lUnit-⌣ₖ m n (x +ₖ y)

  ⌣ₖ-distrFun2 : -- z ⌣ₖ x +ₖ z ⌣ₖ y
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (m +' n)
  fst (⌣ₖ-distrFun2 n m x y) z =
    z ⌣ₖ x +ₖ z ⌣ₖ y
  snd (⌣ₖ-distrFun2 n m x y) =
    cong₂ _+ₖ_ (lUnit-⌣ₖ m n x) (lUnit-⌣ₖ m n y) ∙ rUnitₖ _ _

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
        (funExt (λ z → sym (lUnitₖ _ (z ⌣ₖ ∣ y ∣)) ∙ λ i → rUnit-⌣ₖ _ _ z (~ i) +ₖ z ⌣ₖ ∣ y ∣))
    left-fst (suc n) y =
        (funExt (λ z → sym (lUnitₖ _ (z ⌣ₖ ∣ y ∣)) ∙ λ i → rUnit-⌣ₖ _ _ z (~ i) +ₖ z ⌣ₖ ∣ y ∣))

    right-fst : (n : ℕ) (x : S₊ (suc n)) →
      fst (⌣ₖ-distrFun (suc n) (suc m) ∣ x ∣ (0ₖ _)) ≡
      fst (⌣ₖ-distrFun2 (suc n) (suc m) ∣ x ∣ (0ₖ _))
    right-fst n x = funExt (λ z → (cong (z ⌣ₖ_) (rUnitₖ _ ∣ x ∣) ∙∙ sym (rUnitₖ _ _) ∙∙ λ i → z ⌣ₖ ∣ x ∣ +ₖ rUnit-⌣ₖ _ (suc n) z (~ i)))

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
    left-fst≡right-fst zero i j z = helper _ (z ⌣ₖ ∣ base ∣) (sym (rUnit-⌣ₖ _ _ z)) i j
    left-fst≡right-fst (suc n) i j z = helper _ (z ⌣ₖ ∣ north ∣) (sym (rUnit-⌣ₖ _ (suc (suc n)) z)) i j

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
    lem : (a : Int) → (sucInt a) ·₀ z ≡ z +ₖ (a ·₀ z)
    lem (pos zero) = refl
    lem (pos (suc a)) = cong (z +ₖ_) (lem (pos a))
    lem (negsuc zero) = sym (rCancelₖ n z)
    lem (negsuc (suc a)) = sym (-cancelLₖ n z (negsuc a ·₀ z)) ∙ sym (assocₖ n z (negsuc a ·₀ z) (-ₖ z))
  leftDistrn₀ n z x (negsuc y) = main y
    where
    help : (x : Int) → predInt x ·₀ z ≡ (x ·₀ z -ₖ z)
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


-- Right distributativity

private
  ⌣ₖ-distrFun-r : -- (x +ₖ y) ⌣ₖ z
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (n +' m)
  fst (⌣ₖ-distrFun-r n m x y) z =
    (x +ₖ y) ⌣ₖ z
  snd (⌣ₖ-distrFun-r n m x y) =
    rUnit-⌣ₖ n m (x +ₖ y) -- rUnit-⌣ₖ m n (x +ₖ y)

  ⌣ₖ-distrFun2-r :
    (n m : ℕ) → (x y : coHomK n)
      → coHomK-ptd m →∙ coHomK-ptd (n +' m)
  fst (⌣ₖ-distrFun2-r n m x y) z =
    x ⌣ₖ z +ₖ y ⌣ₖ z
  snd (⌣ₖ-distrFun2-r n m x y) =
    cong₂ _+ₖ_ (rUnit-⌣ₖ n m x) (rUnit-⌣ₖ n m y) ∙ rUnitₖ _ _

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
        ∙∙ cong (_+ₖ (∣ y ∣ ⌣ₖ z)) (sym (lUnit-⌣ₖ _ _ z)))

    fst-right : (n : ℕ) (x : S₊ (suc n)) →
      fst (⌣ₖ-distrFun-r (suc n) (suc m) ∣ x ∣ ∣ ptSn (suc n) ∣) ≡
      fst (⌣ₖ-distrFun2-r (suc n) (suc m) ∣ x ∣ ∣ ptSn (suc n) ∣)
    fst-right n x =
      funExt λ z
        → cong (_⌣ₖ z) (rUnitₖ _ ∣ x ∣)
        ∙∙ sym (rUnitₖ _ _)
        ∙∙ cong (∣ x ∣ ⌣ₖ z +ₖ_) (sym (lUnit-⌣ₖ _ _ z))

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
assocer : (n m k : ℕ) → coHomK (suc n)
  →  coHomK-ptd (suc m)
  →∙ (coHomK-ptd (suc k)
  →∙ coHomK-ptd ((suc n) +' ((suc m) +' (suc k))) ∙)
fst (fst (assocer n m k x) y) z = x ⌣ₖ (y ⌣ₖ z)
snd (fst (assocer n m k x) y) = cong (x ⌣ₖ_) (rUnit-⌣ₖ _ (suc k) y) ∙ rUnit-⌣ₖ _ _ x
snd (assocer n m k x) =
  ΣPathP (funExt (λ z → cong (x ⌣ₖ_) (lUnit-⌣ₖ (suc m) (suc k) z) ∙ rUnit-⌣ₖ (suc n) _ x)
        , help)
  where
  h : (n m k : ℕ) (x : coHomK (suc n)) → cong (_⌣ₖ_ x) (rUnit-⌣ₖ (suc m) (suc k) (0ₖ _)) ≡
                                (λ i → x ⌣ₖ lUnit-⌣ₖ (suc m) (suc k) (0ₖ _) i)
  h zero zero k x = refl
  h zero (suc m) k x = refl
  h (suc n) zero k x = refl
  h (suc n) (suc m) k x = refl

  help : PathP (λ i → (cong (x ⌣ₖ_) (lUnit-⌣ₖ (suc m) (suc k) (0ₖ _)) ∙ rUnit-⌣ₖ (suc n) _ x) i ≡ 0ₖ _)
             (cong (x ⌣ₖ_) (rUnit-⌣ₖ (suc m) (suc k) (0ₖ _)) ∙ rUnit-⌣ₖ (suc n) _ x) refl
  help = compPathR→PathP
    (cong (_∙ rUnit-⌣ₖ (suc n) ((suc m) +' (suc k)) x) (h n m k x)
    ∙∙ rUnit _
    ∙∙ cong ((cong (x ⌣ₖ_) (lUnit-⌣ₖ (suc m) (suc k) (0ₖ _)) ∙ rUnit-⌣ₖ (suc n) _ x) ∙_) (rUnit refl))

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
  cong (subst coHomK (sym (+'-assoc 1 (suc m) (suc k)))) (rUnit-⌣ₖ _ _ (x ⌣ₖ y))
snd (fst (assocer2 (suc n) m k x) y) =
  cong (subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k)))) (rUnit-⌣ₖ _ _ (x ⌣ₖ y))
fst (snd (assocer2 zero m k x) i) z =
  subst coHomK (sym (+'-assoc (suc zero) (suc m) (suc k))) (rUnit-⌣ₖ _ _ x i ⌣ₖ z)
snd (snd (assocer2 zero m k x) i) j =
  subst coHomK (sym (+'-assoc (suc zero) (suc m) (suc k))) (rUnit-⌣ₖ _ _ (rUnit-⌣ₖ _ _ x i) j)
fst (snd (assocer2 (suc n) m k x) i) z =
  subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k))) (rUnit-⌣ₖ _ _ x i ⌣ₖ z)
snd (snd (assocer2 (suc n) m k x) i) j =
  subst coHomK (sym (+'-assoc (2 + n) (suc m) (suc k))) (rUnit-⌣ₖ _ _ (rUnit-⌣ₖ _ _ x i) j)

pFun : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
fst (pFun n m a) b = Kn→ΩKn+1 _ (a ⌣ₖ b)
snd (pFun n m a) = cong (Kn→ΩKn+1 _) (rUnit-⌣ₖ (suc n) (suc m) a) ∙ Kn→ΩKn+10ₖ _

pFun2 : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
fst (pFun2 n m a) b i = (Kn→ΩKn+1 _ a i) ⌣ₖ b
snd (pFun2 n m a) i j = rUnit-⌣ₖ _ (suc m) (Kn→ΩKn+1 _ a j) i

pFun≡ : (n m : ℕ) → (x : coHomK (suc n)) → pFun n m x ≡ pFun2 n m x
pFun≡ n m =
  trElim (λ _ → isOfHLevelPath (3 + n) (hLev-pFun n m) _ _)
         λ a → →∙Homogeneous≡ (subst isHomogeneous Kn≃ΩKn+1∙ (isHomogeneousKn _))
           (funExt (main n a))
  where
  hLev-pFun : (n m : ℕ) → isOfHLevel (3 + n) (coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m))))
  hLev-pFun n m = 
    subst (isOfHLevel (3 + n)) (cong (coHomK-ptd (suc m) →∙_)
      (Kn≃ΩKn+1∙))
      (isOfHLevel↑∙ (suc n) m)

  main : (n : ℕ) (a : S₊ (suc n)) (b : _) → fst (pFun n m ∣ a ∣) b ≡ fst (pFun2 n m ∣ a ∣) b
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
assoc-helper n m x y = funExt⁻ (cong fst (pFun≡ n m x)) y

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


  main : (n m k : ℕ) → (a : S₊ (suc n)) (b : coHomK (suc m)) (c : coHomK (suc k))
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
      ∙∙ sym (lUnit-⌣ₖ _ _ y)
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
      ∙∙ sym (rUnit-⌣ₖ _ _ x)
      ∙∙ cong (x ⌣ₖ_) (sym (lCancelₖ _ y))
       ∙ leftDistr-⌣ₖ _ _ x (-ₖ y) y

assoc₀ : (m k : ℕ) (x : Int) (y : coHomK m) (z : coHomK k) → _⌣ₖ_{n = zero} x (y ⌣ₖ z) ≡ (_⌣ₖ_{n = zero} {m = m} x y) ⌣ₖ z
assoc₀ m k x y z = main x
  where
  h : subst coHomK (sym (+'-assoc zero m k)) ≡ idfun _
  h = cong (subst coHomK) (isSetℕ _ _ _ refl) ∙ funExt transportRefl
  mainPos : (x : ℕ) → _⌣ₖ_ {n = zero} (pos x) (y ⌣ₖ z) ≡ ((_⌣ₖ_ {n = zero} {m = m} (pos x) y) ⌣ₖ z)
  mainPos zero = sym (lUnit-⌣ₖ _ _ z) ∙ cong (_⌣ₖ z) (sym (lUnit-⌣ₖ _ _ y))
  mainPos (suc n) =
      cong (y ⌣ₖ z +ₖ_) (mainPos n)
    ∙∙ sym (rightDistr-⌣ₖ _ _ y (_⌣ₖ_ {n = zero} {m = m} (pos n) y) z)
    ∙∙ (λ i → (y +ₖ (_⌣ₖ_ {n = zero} {m = m} (pos n) y)) ⌣ₖ z)

  main : (x : Int) → x ⌣ₖ y ⌣ₖ z ≡ ((_⌣ₖ_ {n = zero} {m = m} x y) ⌣ₖ z)
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
    (rUnit-⌣ₖ _ _ x)
     ∙∙ (sym (lUnit-⌣ₖ _ _ z))
     ∙∙ cong (_⌣ₖ z) (sym (rUnit-⌣ₖ _ _ x))
  helpPos (suc y) =
    leftDistr-⌣ₖ _ _ x z (_⌣ₖ_{n = zero} (pos y) z)
    ∙∙ cong ((x ⌣ₖ z) +ₖ_) (helpPos y)
    ∙∙ sym (rightDistr-⌣ₖ _ _ x (_⌣ₖ_{n = zero} (pos y) x) z)

  help : (y : Int) → x ⌣ₖ (_⌣ₖ_ {n = zero} y z) ≡
      ((_⌣ₖ_ {m = zero} x y) ⌣ₖ z)
  help (pos n) = helpPos n
  help (negsuc n) =
       (λ i → x ⌣ₖ (_⌣ₖ_ {n = zero} (+ℤ-comm (negsuc n) 0 i) z))
    ∙∙ cong (x ⌣ₖ_) (sym (-Distₗ zero _ (pos (suc n)) z)) -- cong (x ⌣ₖ_) (sym (-Distₗ zero _ (pos n) z))
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

_⌣_ : {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n +' m) A
_⌣_ = sRec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

open import Cubical.Algebra.Ring
-- open import Cubical.Data.List

open IsRing
open RingStr renaming (_+_ to _+ᵣ_ ; _·_ to _·ᵣ_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

-- open import Cubical.Data.Vec

open import Cubical.HITs.PropositionalTruncation renaming (∣_∣ to ∣_∣₁ ; rec to pRec ; rec2 to pRec2 ; elim to pElim)
Gradeℕ : (A : ℕ → Type ℓ) (a₀ : (n : ℕ) → A n) → Type _
Gradeℕ A a₀ =
  Σ[ v ∈ ((n : ℕ) → (A n)) ]
    ∃[ n ∈ ℕ ] ((m : ℕ) → n < m → v m ≡ a₀ m)

isSetGradeℕ : {A : ℕ → Type ℓ} {a₀ : (n : ℕ) → A n} → ((n : ℕ) → isSet (A n)) → isSet (Gradeℕ A a₀)
isSetGradeℕ set =
  isSetΣ
    (isSetΠ (λ _ → set _)) λ _ →
     isProp→isSet propTruncIsProp

coHomR : (A : Type ℓ) → Type ℓ
coHomR A = Gradeℕ (λ n → coHom n A) 0ₕ

1-coHomR : {A : Type ℓ} → coHomR A
fst 1-coHomR zero = ∣ (λ _ → 1) ∣₂
fst 1-coHomR (suc n) = 0ₕ _
snd 1-coHomR = ∣ 1 , (λ {0 p → ⊥-rec (¬-<-zero p) ; (suc n) _ → refl}) ∣₁

_+ₕᵣ_ : {A : Type ℓ} → coHomR A → coHomR A → coHomR A
fst ((f , p) +ₕᵣ (g , q)) n = f n +ₕ g n
(snd ((f , p) +ₕᵣ (g , q))) =
  pRec2 propTruncIsProp
    (λ p q → ∣ (max (fst p) (fst q))
             , (λ m ineq → cong₂ _+ₕ_ (snd p m (≤-trans (≤-k+ {k = 1} (left-≤-max {m = (fst p)} {fst q})) ineq))
                    (snd q m (≤-trans (≤-k+ {k = 1} (right-≤-max {n = (fst q)} {m = fst p}))
                      (<≤-trans (0 , refl) ineq))) ∙ rUnitₕ _ (0ₕ _)) ∣₁) p q

-0ₕ : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → Path (coHom n A) (-[ n ]ₕ (0ₕ n)) (0ₕ n)
-0ₕ zero = refl
-0ₕ (suc zero) = refl
-0ₕ (suc (suc n)) = refl

-ₕᵣ_ : {A : Type ℓ} → coHomR A → coHomR A
fst (-ₕᵣ (f , p)) x = -ₕ (f x)
snd (-ₕᵣ (f , p)) = pRec propTruncIsProp (λ {(x , q) → ∣ x , (λ m ineq → cong -ₕ_ (q m ineq) ∙ -0ₕ m) ∣}) p


charac≡ : {A : Type ℓ} {f g : coHomR A} → ((n : ℕ) → (fst f) n ≡ (fst g) n) → f ≡ g
charac≡ ind = Σ≡Prop (λ _ → propTruncIsProp) (funExt ind)

decEqℕ : (n m : ℕ) → (¬ n ≡ m) ⊎ (n ≡ m)
decEqℕ zero zero = inr refl
decEqℕ zero (suc m) = inl λ p → (snotz (sym p))
decEqℕ (suc n) zero = inl snotz
decEqℕ (suc n) (suc m) with (decEqℕ n m)
... | inl p = inl λ q → p (cong predℕ q)
... | inr p = inr (cong suc p)

isProp-decEqℕ : (n m : ℕ) → isProp ((¬ n ≡ m) ⊎ (n ≡ m))
isProp-decEqℕ n m (inl x) (inl x₁) =
  cong inl (funExt λ p → ⊥-rec (x p))
isProp-decEqℕ n m (inl x) (inr x₁) = ⊥-rec (x x₁)
isProp-decEqℕ n m (inr x) (inl x₁) = ⊥-rec (x₁ x)
isProp-decEqℕ n m (inr x) (inr x₁) = cong inr (isSetℕ _ _ x x₁)

inclFun : {A : Type ℓ} {n : ℕ}
      → coHom n A
      → (m : ℕ) → (¬ n ≡ m) ⊎ (n ≡ m) → coHom m A
inclFun x m (inl x₁) = 0ₕ _
inclFun x m (inr x₁) = subst (λ n → coHom n _) x₁ x

<→¬≡ : (n m : ℕ) → n < m → ¬ (n ≡ m)
<→¬≡ n zero p = ⊥-rec (¬-<-zero p)
<→¬≡ zero (suc m) p q = snotz (sym q)
<→¬≡ (suc n) (suc m) p q = <→¬≡ n m (<-k+-cancel p) (cong predℕ q)

incl : {A : Type ℓ} {n : ℕ}
      → coHom n A
      → coHomR A
fst (incl {n = n} x) m = inclFun x m (decEqℕ n m)
snd (incl {n = n} x) =
  ∣ n , (λ m p → cong (inclFun x m) (isProp-decEqℕ n m (decEqℕ n m) (inl (<→¬≡ n m p)))) ∣₁

open import Cubical.Data.List

sumList : {A : Type ℓ} {n : ℕ} → coHomR A → ∥ List (coHomR A) ∥
sumList {A = A} = uncurry λ f → Cubical.HITs.PropositionalTruncation.map
  (uncurry (c f))
  where
  c : (f : (n : ℕ) → coHom n A) → (x : ℕ) (y : (m : ℕ) → x < m → f m ≡ 0ₕ m) → List (coHomR A)
  c f zero y = []
  c f (suc x) y = {!c f x ?!} ++ [ incl (f (suc x)) ]
    where
    new : {!!}
    new = {!!}

h : (n m : ℕ) → (n ≤ m) ⊎ (m < n)
h n m = help (n ≟ m)
  where
  help : Trichotomy n m → (n ≤ m) ⊎ (m < n)
  help (lt x) = inl (<-weaken x)
  help (eq x) = inl (0 , x)
  help (gt x) = inr x

h' : (n m : ℕ) → (n < m) ⊎ (m ≤ n)
h' n m = help (n ≟ m)
  where
  help : Trichotomy n m → (n < m) ⊎ (m ≤ n)
  help (lt x) = inl x
  help (eq x) = inr (0 , sym x)
  help (gt x) = inr (<-weaken x)

_·₀'_ : {A :  Type ℓ} → Int → coHomR A → coHomR A
x ·₀' y = {!!}

elimCohomR :
  ∀ {ℓ} {A : Type ℓ}
   → {P : coHomR A → Type ℓ}
   → ((x : _) → isProp (P x))
   → ((n : ℕ) (x : coHom n A)→ P (incl x))
   → ((x : coHomR A) (y : coHomR A) → P x → P y → P (x +ₕᵣ y))
   → (x : _) → P x
elimCohomR {A = A} {P = P} prop ind1 ind2 =
  uncurry λ f → pElim (λ _ → prop _)
    λ {(n , ineq) → help f n ineq}
  where
  isProp-help : (x n : ℕ) → isProp ((x < n) ⊎ (n ≤ x))
  isProp-help x n = {!!}

  help3 : (f : (n : ℕ) → coHom n A) (n : ℕ) (ineq : ((m : ℕ) → n < m → f m ≡ 0ₕ m))
       → Σ[ p ∈ _ ] P p × (p ≡ ((f , ∣ n , ineq ∣₁)))
  fst (help3 f zero ineq) = incl (f 0)
  fst (snd (help3 f zero ineq)) = ind1 _ (f 0)
  snd (snd (help3 f zero ineq)) = 
    sym (charac≡ λ {0 → sym (transportRefl (f zero))
                    ; (suc n) → ineq (suc n) (n , +-comm n 1)})
  help3 f (suc n) ineq = {!!} -- f-copy +ₕᵣ incl (f (suc n)) , {!!}
    where
    f-copy' : (n : ℕ) → (f : (n : ℕ) → coHom n A) → (m : ℕ) → (m < suc n) ⊎ (suc n ≤ m)→ coHom m A
    f-copy' n f m (inl x) = f m
    f-copy' n f m (inr x) = 0ₕ _

    f-copy : (n : ℕ) → coHomR A → coHomR A
    fst (f-copy n f) m = f-copy' n (fst f) m (h' m (suc n))
    snd (f-copy n f) = pRec propTruncIsProp (λ p → ∣ n , (λ m p → cong (f-copy' n (fst f) m) (isProp-help _ _ _ (inr ((fst p) , snd p)))) ∣₁) (snd f)

    f-copy≡ : (f : (n : ℕ) → coHom n A) (n : ℕ) (p : ((m : ℕ) → suc n < m → f m ≡ 0ₕ _))
            → (f , ∣ (suc n , p) ∣₁) ≡ ((f , ∣ n , (λ m q → p m {!!}) ∣₁) +ₕᵣ {!!}) -- (f-copy ?) (f , ∣ p ∣₁) +ₕᵣ ?
    f-copy≡ = {!!}

{-
    f-copy≡ f (zero , p) = charac≡ {!h' ? 1!} -- {!!} ∙∙ {!!} ∙∙ λ i → f-copy' zero f n {!n!} +ₕ inclFun (f zero) n {!!}
      where
      help : (n : ℕ) → ((n < 1) ⊎ (1 ≤ n)) → f n ≡ f-copy' zero f n (h' n 1) +ₕ inclFun (f zero) n (decEqℕ zero n)
      help n (inl x) = {!!} ∙∙ {!!} ∙∙ λ i → f-copy' zero f n (isProp-help _ _ (inl x) (h' n 1) i) +ₕ inclFun (f 1) n {!!} -- decEqℕ zero n
      help n (inr x) = {!!}
    f-copy≡ f (suc n , p) = {!!}

-}
  help : (f : (n : ℕ) → coHom n A) (n : ℕ) (ineq : ((m : ℕ) → n < m → f m ≡ 0ₕ m))
      → P (f , ∣ n , ineq ∣₁)
  help f zero ineq = subst P (sym help2) (ind1 0 (f 0))
    where
    help2 : (f , ∣ zero , ineq ∣₁) ≡ incl (f 0)
    help2 = charac≡ λ {0 → sym (transportRefl (f zero))
                    ; (suc n) → ineq (suc n) (n , +-comm n 1)}
  help f (suc n) ineq = {!!}
    where
    help2 : (f , ∣ zero , ineq ∣₁) ≡ {!!}
    help2 = {!!}

{-
-- pairs≤ : (n : ℕ) → Σ[ p ∈ ℕ × ℕ ] (fst p · snd p ≡ n)
-- pairs≤ zero = {!0 , 0!}
-- pairs≤ (suc n) = {!!}

-- h : (n m : ℕ) → (n ≤ m) ⊎ (m < n)
-- h n m = help (n ≟ m)
--   where
--   help : Trichotomy n m → (n ≤ m) ⊎ (m < n)
--   help (lt x) = inl (<-weaken x)
--   help (eq x) = inl (0 , x)
--   help (gt x) = inr x

-- {-
-- sumBelow : (n : ℕ) → (x y : ℕ) → (x · y ≤ n) ⊎ (n < x · y) → List (ℕ × ℕ)
-- sumBelow n zero y (inl (zero , p)) = []
-- sumBelow n (suc x) zero (inl (zero , p)) = []
-- sumBelow n (suc x) (suc y) (inl (zero , p)) = [ suc x , suc y ] ++ sumBelow n x (suc y) (h _ _) ++ sumBelow n (suc x) y (h _ _)
-- sumBelow n zero y (inl (suc diff , p)) = []
-- sumBelow n (suc x) zero (inl (suc diff , p)) = []
-- sumBelow n (suc x) (suc y) (inl (suc diff , p)) = sumBelow n x (suc y) (h _ _) ++ sumBelow n (suc x) y (h _ _)
-- sumBelow n zero y (inr p) = []
-- sumBelow n (suc x) zero (inr p) = []
-- sumBelow n (suc x) (suc y) (inr p) = sumBelow n x (suc y) (h _ _) ++ sumBelow n (suc x) y (h _ _)

-- sumAll : {!sumBelow 15 15 15 (h _ _)!}
-- sumAll = {!!}

-- sum : ∀ {ℓ} {A : ℕ → Type ℓ} (f g : (n : ℕ) → A n) (n : ℕ)
--             (+A : (n m : ℕ) → A n → A m → A (n +' m))
--             → ((m : ℕ) → A m)
-- sum f g n +A m = {!!}
-- -}

-- coHomRing : ∀ {ℓ} (A : Type ℓ) → Ring
-- fst (coHomRing A) = coHomR A
-- 0r (snd (coHomRing A)) = 0ₕ , (0 , (λ _ _ → refl))
-- 1r (snd (coHomRing A)) = 1-coHomR
-- _+ᵣ_ (snd (coHomRing A)) (f , p) (g , q) =
--   (λ n → f n +ₕ g n) , max (fst p) (fst q)
--     , λ m ineq
--       → cong₂ _+ₕ_ (snd p m (≤-trans (≤-k+ {k = 1} (left-≤-max {m = (fst p)} {fst q})) ineq))
--                     (snd q m (≤-trans (≤-k+ {k = 1} (right-≤-max {n = (fst q)} {m = fst p}))
--                       (<≤-trans (0 , refl) ineq))) ∙ rUnitₕ _ (0ₕ _)
-- fst ((snd (coHomRing A) RingStr.· (f , p)) (g , q)) zero = f 0 +ₕ g 0
-- fst ((snd (coHomRing A) RingStr.· (f , p)) (g , q)) (suc n) = {!!}
-- snd ((snd (coHomRing A) RingStr.· (f , p)) (g , q)) = {!!}
-- - snd (coHomRing A) = {!!}
-- +IsAbGroup (isRing (snd (coHomRing A))) = {!!}
-- ·IsMonoid (isRing (snd (coHomRing A))) = {!!}
-- dist (isRing (snd (coHomRing A))) = {!!}
-}
