{-# OPTIONS --safe --experimental-lossy-unification #-}

{- This file contains properties of K(G,n) for G of order 2
(in particular of ℤ/2) -}

module Cubical.Homotopy.EilenbergMacLane.Order2 where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)

open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous


open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; elim to ℕelim)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct

open AbGroupStr

module EM2 {ℓ : Level} (G : AbGroup ℓ)
         (-Const : (x : fst G) → -_ (snd G) x ≡ x) where

  -ₖConst : (n : ℕ) → (x : EM G (suc n)) → -ₖ x ≡ x
  -ₖConst =
   elim+2 -ₖConst₁
     (TR.elim (λ _ → isOfHLevelPath 4
                       (hLevelEM _ 2) _ _)
     λ { north → refl
       ; south i → ∣ merid embase i ∣
       ; (merid a i) j →
         hcomp (λ r → λ {(i = i0) → ∣ north ∣
                         ; (i = i1) → ∣ merid embase (j ∧ r) ∣
                         ; (j = i0) → EM→ΩEM+1-sym (suc zero) a r i
                         ; (j = i1) → ∣ compPath-filler (merid a)
                                        (sym (merid embase)) (~ r) i ∣})
                (EM→ΩEM+1 (suc zero) (-ₖConst₁ a j) i)})
     λ n ind → TR.elim (λ _ → isOfHLevelPath (suc (suc (suc (suc (suc n)))))
                        (hLevelEM _ (suc (suc (suc n)))) _ _)
     λ { north → refl
       ; south i → ∣ merid north i ∣
       ; (merid a i) j →
          hcomp (λ r → λ {(i = i0) → ∣ north ∣
                         ; (i = i1) → ∣ merid north (j ∧ r) ∣
                         ; (j = i0) → EM→ΩEM+1-sym (suc (suc n)) ∣ a ∣ₕ r i
                         ; (j = i1) → ∣ compPath-filler (merid a)
                                         (sym (merid north)) (~ r) i ∣})
                (EM→ΩEM+1 (suc (suc n)) (ind ∣ a ∣ j) i)}
    where
    -ₖConst₁ : (x : EM G (suc zero)) → -[ 1 ]ₖ x ≡ x
    -ₖConst₁ = elimSet _ (λ _ → emsquash _ _)
          refl
          λ g → flipSquare (sym (emloop-sym (AbGroup→Group G) g)
               ∙ cong emloop (-Const g))

  -- encode-decode proof that sym = id in ΩK(ℤ/2,n)
  -- (reducing to (transport refl) refl for the case sym refl = refl)
  private
    symCode : (n : ℕ) (x : EM G (suc n))
      → 0ₖ (suc n) ≡ x
      → TypeOfHLevel ℓ (suc n)
    symCode zero =
      EM-raw'-elim _ 1
       (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelTypeOfHLevel 1)
        λ { embase-raw → λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _
         ; (emloop-raw g i) → main g i}
      where
      main' : (g : fst G)
        → PathP (λ i → Path (EM G 1) embase (emloop g i) → Type ℓ)
                 (λ p → p ≡ sym p) λ p → p ≡ sym p
      main' g = toPathP (funExt
        λ p → (λ i
            → transp (λ j → Path (EM G 1) embase (emloop g (~ j ∧ ~ i))) i
                      (compPath-filler p (sym (emloop g)) i)
             ≡ sym (transp (λ j → Path (EM G 1) embase (emloop g (~ j ∧ ~ i))) i
                      (compPath-filler p (sym (emloop g)) i)))
           ∙ cong (p ∙ sym (emloop g) ≡_) (symDistr p (sym (emloop g))
                  ∙ isCommΩEM {G = G} 0 (emloop g) (sym p)
                  ∙ cong (sym p ∙_) (cong sym (sym (EM→ΩEM+1-sym 0 g)
                  ∙ cong (EM→ΩEM+1 0) (-Const g))))
           ∙ (λ i → compPath-filler p (sym (emloop g)) (~ i)
                   ≡ compPath-filler (sym p) (sym (emloop g)) (~ i)))
      main : (g : fst G)
        → PathP (λ i → Path (EM G 1) embase (emloop g i) → TypeOfHLevel ℓ 1)
                 (λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _)
                 λ p → (p ≡ sym p) , hLevelEM G 1 _ _ _ _
      main g = toPathP (funExt (λ p → Σ≡Prop (λ _ → isPropIsProp)
                (funExt⁻ (fromPathP (main' g)) p)))
    symCode (suc n) =
      TR.elim (λ _ → isOfHLevelΠ (4 +ℕ n)
              λ _ → isOfHLevelSuc (3 +ℕ n) (isOfHLevelTypeOfHLevel (2 +ℕ n)))
              λ a p → Code a p , hLevCode a p
      where
      Code : (a : EM-raw G (suc (suc n))) → 0ₖ (suc (suc n)) ≡ ∣ a ∣ₕ → Type ℓ
      Code north p = p ≡ sym p
      Code south p = p ∙ cong ∣_∣ₕ (sym (merid ptEM-raw))
                   ≡ cong ∣_∣ₕ (merid ptEM-raw) ∙ sym p
      Code (merid a i) = h a i
        where
        K2 = EM G (suc (suc n))



        h : (a : _) → PathP (λ i → Path K2 ∣ north ∣ ∣ merid a i ∣ → Type ℓ)
                             (λ p → (p ≡ sym p))
                             λ p → (p ∙ cong ∣_∣ₕ (sym (merid ptEM-raw))
                                  ≡ cong ∣_∣ₕ (merid ptEM-raw) ∙ sym p)
        h a =
          toPathP (flipTransport
                   {A = λ i → Path K2 ∣ north ∣ ∣ merid a i ∣ → Type ℓ}
                      (funExt (λ p →
                        (((p₃ p
                         ∙ λ i → p₁ p i ≡ p₂ p (~ i))
                        ∙ λ i → delTransp p (~ i) ∙ sym m∙
                               ≡ m∙ ∙ sym (delTransp p (~ i)))
                       ∙ sym (transportRefl _)))))
          where
          m∙ : Path K2 ∣ north ∣ ∣ south ∣
          m∙ i = ∣ merid ptEM-raw i ∣

          ma : Path K2 ∣ north ∣ ∣ south ∣
          ma i = ∣ merid a i ∣

          σ' : (n : ℕ) (a : EM-raw G (suc n)) → fst ((Ω (EM∙ G (suc (suc n)))))
          σ' n a i = ∣ (merid a ∙ sym (merid ptEM-raw)) i ∣ₕ

          delTransp : (p : _) → transport (λ i → Path K2 ∣ north ∣ ∣ merid a i ∣) p
                       ≡ p ∙ cong ∣_∣ₕ (merid a)
          delTransp p i = transp (λ j → Path K2 ∣ north ∣ ∣ merid a (j ∨ i) ∣) i
                         (compPath-filler p (cong ∣_∣ₕ (merid a)) i)

          σ-sym : (n : ℕ) (a : _) → sym (σ' n a) ≡ σ' n a
          σ-sym zero a = sym (EM→ΩEM+1-sym 1 a)
                       ∙ cong (EM→ΩEM+1 1) (-ₖConst 0 a)
          σ-sym (suc n) a = sym (EM→ΩEM+1-sym (2 +ℕ n) ∣ a ∣)
                          ∙ cong (EM→ΩEM+1 (2 +ℕ n)) (-ₖConst (suc n) ∣ a ∣)

          p₁ : (p : Path K2 ∣ north ∣ ∣ north ∣)
            → p ∙ σ' n a ≡ (p ∙ ma) ∙ sym m∙
          p₁ p = (λ i → p ∙ (cong-∙ ∣_∣ₕ (merid a) (sym (merid ptEM-raw))) i)
               ∙ assoc p ma (sym m∙)

          p₂ : (p : _) → m∙ ∙ sym (p ∙ ma) ≡ sym (sym (σ' n a) ∙ p)
          p₂ p =
              (((λ i → m∙ ∙ (symDistr p ma i))
              ∙ assoc _ _ _
              ∙ (λ i → symDistr ma (sym m∙) (~ i) ∙ sym p)
              ∙ λ i → sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid ptEM-raw)) (~ i))
                     ∙ sym p)
              ∙ (isCommΩEM _ _ _))
            ∙ sym (symDistr (σ' n a) p)
            ∙ cong sym (cong (_∙ p) (sym (σ-sym n a)))

          p₃ : (p : _) → (p ≡ sym p) ≡ (p ∙ σ' n a ≡ sym (sym (σ' n a) ∙ p))
          p₃ p i = compPath-filler p (σ' n a) i
                 ≡ sym (compPath-filler' (sym (σ' n a)) p i)

      hLevCode : (a : EM-raw G (suc (suc n))) (p : 0ₖ (suc (suc n)) ≡ ∣ a ∣ₕ)
        → isOfHLevel (suc (suc n)) (Code a p)
      hLevCode =
        suspToPropElim ptEM-raw
          (λ _ → isPropΠ λ _ → isPropIsOfHLevel (2 +ℕ n))
          λ p → hLevelEM _ (2 +ℕ n) _ _ _ _

    encode-sym : (n : ℕ) (x : EM G (suc n)) (p : 0ₖ (suc n) ≡ x)
              → symCode n x p .fst
    encode-sym zero = J> refl
    encode-sym (suc n) = J> refl

  symConstEM : (n : ℕ) (x : EM G n) (p : x ≡ x) → p ≡ sym p
  symConstEM zero x p = is-set (snd G) _ _ _ _
  symConstEM (suc zero) =
    EM.EM-raw'-elim G 1
      (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (hLevelEM G 1 _ _) _ _)
    (EM-raw'-trivElim G zero (λ _ → isPropΠ λ _ → hLevelEM G 1 _ _ _ _)
     (encode-sym 0 embase))
  symConstEM (suc (suc n)) =
    EM.EM-raw'-elim G (2 +ℕ n) (λ _ → isOfHLevelΠ (3 +ℕ n)
      λ _ → isOfHLevelPath (3 +ℕ n) (hLevelEM G (2 +ℕ n) _ _) _ _)
        (EM-raw'-trivElim G (suc n)
         (λ _ → isOfHLevelΠ (2 +ℕ n) λ _ → hLevelEM G (2 +ℕ n) _ _ _ _)
          (encode-sym (suc n) ∣ north ∣))

  symConstEM-refl : {n : ℕ} → symConstEM n (0ₖ n) refl ≡ refl
  symConstEM-refl {n = zero} = isOfHLevelPath 2 (is-set (snd G)) _ _ _ _ _ _
  symConstEM-refl {n = suc zero} = transportRefl refl
  symConstEM-refl {n = suc (suc n)} = transportRefl refl


ℤ/2 : AbGroup ℓ-zero
ℤ/2 = Group→AbGroup (ℤGroup/ 2) +ₘ-comm

private
  module EMZ/2 = EM2 ℤ/2 -Const-ℤ/2

-ₖConst-ℤ/2 : (n : ℕ) → (x : EM ℤ/2 (suc n)) → -ₖ x ≡ x
-ₖConst-ℤ/2 = EMZ/2.-ₖConst

symConst-ℤ/2 : (n : ℕ) (x : EM ℤ/2 n) (p : x ≡ x) → p ≡ sym p
symConst-ℤ/2 = EMZ/2.symConstEM

symConst-ℤ/2-refl : {n : ℕ} → symConst-ℤ/2 n (0ₖ n) refl ≡ refl
symConst-ℤ/2-refl = EMZ/2.symConstEM-refl

-- Commutativity of cup product

module _ where
  private
    open PlusBis
    cp⊗ : (n m : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m)
      → EM (ℤ/2 ⨂ ℤ/2) (n +' m)
    cp⊗ n m x y = x ⌣ₖ⊗ y

    cp⊗∙ : (n m : ℕ) (x : EM ℤ/2 n) → EM∙ ℤ/2 m →∙ EM∙ (ℤ/2 ⨂ ℤ/2) (n +' m)
    cp⊗∙ n m x = cup∙ n m x

    subst' : (n m : ℕ) → EM (ℤ/2 ⨂ ℤ/2) (m +' n) → EM (ℤ/2 ⨂ ℤ/2) (n +' m)
    subst' n m = subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm m n)

    commFun1 : (n m : ℕ) (x : EM ℤ/2 n) → EM∙ ℤ/2 m →∙ EM∙ (ℤ/2 ⨂ ℤ/2) (n +' m)
    fst (commFun1 n m x) y = subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm m n) (y ⌣ₖ⊗ x)
    snd (commFun1 n m x) =
        cong (subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm m n)) (0ₖ-⌣ₖ⊗ m n x)
      ∙ substCommSlice (λ _ → EM (ℤ/2 ⨂ ℤ/2) (n +' m))
          (EM (ℤ/2 ⨂ ℤ/2)) (λ a _ → 0ₖ a) (+'-comm m n) (0ₖ (n +' m))

  ℕ-elim2 : ∀ {ℓ} {P : ℕ → ℕ → Type ℓ}
          → ((n : ℕ) → P zero n)
          → ((n : ℕ) → P (suc n) zero)
          → ((n m : ℕ) → P (suc n) m × P n (suc m) → P (suc n) (suc m))
          → (n m : ℕ) → P n m
  ℕ-elim2 l r ind zero = l
  ℕ-elim2 l r ind (suc n) zero = r n
  ℕ-elim2 {P = P} l r ind (suc n) (suc m) =
    ind n m ((ℕ-elim2 {P = P} l r ind (suc n) m)
           , (ℕ-elim2 {P = P} l r ind n (suc m)))

  0-case : (x y : fst ℤ/2) → cp⊗∙ zero zero x .fst y ≡ cp⊗∙ zero zero y .fst x
  0-case =
    (ℤ/2-elim
           (ℤ/2-elim refl
             (0ₖ-⌣ₖ⊗ zero zero 1
             ∙ sym (⌣ₖ-0ₖ⊗ zero zero 1)))
           (ℤ/2-elim
             (⌣ₖ-0ₖ⊗ zero zero 1
             ∙ sym (0ₖ-⌣ₖ⊗ zero zero 1)) refl))

  pre-comm : (n m : ℕ) (x : EM ℤ/2 n) → cp⊗∙ n m x ≡ commFun1 n m x
  pre-comm zero m x =
    →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt (l m x))
    where
    l : (m : ℕ) (x : fst ℤ/2) (y : EM ℤ/2 m) →
      cp⊗∙ zero m x .fst y ≡
      subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm m zero) (y ⌣ₖ⊗ x)
    l = elim+2
         (λ x y → 0-case x y ∙ sym (transportRefl _))
         (λ x y → lem x y ∙ sym (transportRefl (cp⊗ 1 zero y x)))
         λ n ind x y → lem2 n ind x y
                      ∙ sym ((λ i → subst (EM (ℤ/2 ⨂ ℤ/2)) (isSetℕ _ _ (+'-comm (suc (suc n)) zero) refl i)
                                   (cp⊗ (suc (suc n)) zero y x))
                           ∙ transportRefl _)
      where
      lem : (x : fst ℤ/2) (y : EM ℤ/2 1) → cp⊗∙ zero 1 x .fst y ≡ cp⊗ 1 zero y x
      lem x = EM-raw'-elim ℤ/2 1
        (λ _ → hLevelEM _ 1 _ _)
        λ { embase-raw → refl
         ; (emloop-raw g i) j
           → EM→ΩEM+1 0 (0-case x g j) i}

      lem2 : (m : ℕ) (ind : (x : fst ℤ/2) (y : EM ℤ/2 (suc m))
        → cp⊗∙ zero (suc m) x .fst y
        ≡ subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm (suc m) zero) (y ⌣ₖ⊗ x)) (x : fst ℤ/2) (y : EM ℤ/2 (suc (suc m)))
          → cp⊗∙ zero (suc (suc m)) x .fst y ≡ cp⊗ (suc (suc m)) zero y x
      lem2 m ind x = TR.elim (λ _ → isOfHLevelPath (4 +ℕ m) (hLevelEM _ (suc (suc m))) _ _)
             λ { north → refl
               ; south → refl
               ; (merid a i) j
               → EM→ΩEM+1 (suc m) ((ind x (EM-raw→EM ℤ/2 _ a)
                                  ∙∙ (λ i → subst (EM (ℤ/2 ⨂ ℤ/2)) (isSetℕ _ _ (+'-comm (suc m) zero) refl i)
                                              (cp⊗ (suc m) zero (EM-raw→EM ℤ/2 (suc m) a) x))
                                  ∙∙ transportRefl (cp⊗ (suc m) zero (EM-raw→EM ℤ/2 (suc m) a) x)) j) i}
  pre-comm (suc n) zero x =
    →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y
       → (l y n x ∙ sym (transportRefl _))
        ∙ λ i → subst (EM (ℤ/2 ⨂ ℤ/2))
                       (isSetℕ _ _ refl (+'-comm zero (suc n)) i)
                       (cp⊗ zero (suc n) y x))
    where
    l : (y : fst ℤ/2)  (n : ℕ)(x : EM ℤ/2 (suc n)) →
      cp⊗∙ (suc n) zero x .fst y  ≡ cp⊗ zero (suc n) y x
    l y = ℕelim
         (EM-raw'-elim ℤ/2 1
          (λ _ → hLevelEM _ 1 _ _)
          (λ { embase-raw → refl
            ; (emloop-raw g i) j → EM→ΩEM+1 _ (0-case g y j) i}))
         λ n ind → TR.elim (λ _ → isOfHLevelPath (4 +ℕ n) (hLevelEM _ (suc (suc n))) _ _)
           λ { north → refl
             ; south → refl
             ; (merid a i) j → EM→ΩEM+1 _ (ind (EM-raw→EM ℤ/2 (suc n) a) j) i}
  pre-comm (suc n) (suc m) =
    EM-raw'-elim ℤ/2 (suc n)
      (λ _ → isOfHLevelPath' (suc (suc n)) {!isOfHLevel↑∙ n (suc m)!} _ _) {!!}
    where
    cp⊗' : (n m : ℕ) → EM ℤ/2 (suc m) → EM-raw'∙ ℤ/2 (suc n) →∙ EM∙ (ℤ/2 ⨂ ℤ/2) (suc n +' suc m)
    fst (cp⊗' n m y) x = cp⊗ (suc n) (suc m) (EM-raw'→EM _ _ x) y
    snd (cp⊗' n m y) = cong (λ x → cp⊗ (suc n) (suc m) x y) (EM-raw'→EM∙ ℤ/2 (suc n))
                      ∙ 0ₖ-⌣ₖ⊗ (suc n) (suc m) y

    commFun' : (n m : ℕ) → EM ℤ/2 (suc m) → EM-raw'∙ ℤ/2 (suc n) →∙ EM∙ (ℤ/2 ⨂ ℤ/2) (suc n +' suc m)
    fst (commFun' n m y) x = {!!}
    snd (commFun' n m y) = {!!}

    1-1 : {!!}
    1-1 = {!!}

    main : (n m : ℕ) → (x : EM ℤ/2 (suc n)) → cp⊗∙ (suc n) (suc m) x ≡ commFun1 (suc n) (suc m) x
    main =
      ℕ-elim2
        (ℕelim {!!}
                {!(x : EM ℤ/2 1) → cp⊗∙ 1 1 x ≡ commFun1 1 1 x!})
        {!!}
        {!!}

  gradedComm : (n m : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m)
    → x ⌣ₖ⊗ y ≡ subst (EM (ℤ/2 ⨂ ℤ/2)) (+'-comm m n) (y ⌣ₖ⊗ x)
  gradedComm n m x y = {!!}
